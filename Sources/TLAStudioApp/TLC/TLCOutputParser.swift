import Foundation
import os

// MARK: - Pre-compiled Regex Patterns

/// Pre-compiled regex patterns for TLC output parsing.
/// These are compiled once at load time to avoid repeated compilation overhead.
private enum TLCRegex {
    /// Progress line: "X states generated, Y distinct states, Z states left"
    static let progressLine = try! NSRegularExpression(
        pattern: #"(\d+) states generated.*?(\d+) distinct states.*?(\d+) states left"#
    )

    /// State count: "X distinct states"
    static let stateCount = try! NSRegularExpression(
        pattern: #"(\d+) distinct states"#
    )

    /// Trace state: "State N: <Action>"
    static let traceState = try! NSRegularExpression(
        pattern: #"State (\d+):\s*<(.+)>"#
    )

    /// Variable assignment: "/\ variable = value"
    static let variable = try! NSRegularExpression(
        pattern: #"/\\\s*(\w+)\s*=\s*(.+)"#
    )

    /// Coverage line: "<ActionName ...>: count"
    static let coverage = try! NSRegularExpression(
        pattern: #"<(\w+)[^>]+>:\s*(\d+)"#
    )
}

// MARK: - TLC Output Parser

/// Parses TLC output in both JSON (-tool mode) and plain text formats.
/// Thread-safe: Uses internal locking for state accessed from background threads.
class TLCOutputParser {
    private var lineBuffer = LineBuffer(maxBufferSize: 10 * 1024 * 1024, compactionThreshold: 64 * 1024)
    private var states: UInt64 = 0
    private var distinct: UInt64 = 0
    private var statesLeft: UInt64 = 0
    private var coverage: [String: (count: UInt64, states: UInt64)] = [:]
    private var errorTrace: ErrorTrace?
    private var currentPhase: ModelCheckProgress.Phase = .parsing
    private var startTime: Date?
    private var currentTraceStates: [TraceState] = []
    private var isParsingTrace = false
    private var errorMessage: String?

    // Cached coverage array to avoid repeated map transformations
    private var cachedCoverageArray: [ActionCoverage]?
    private var coverageDirty = false
    private var errorType: ErrorTrace.ErrorType?

    /// Whether an OutOfMemoryError was detected during parsing
    private(set) var detectedOOM = false

    /// Lock for thread-safe access from readability handlers
    private let lock = NSLock()

    private let logger = Log.logger(category: "TLCOutputParser")

    /// Threshold for streaming trace states to disk (above this, use lazy loading)
    static let largeTraceThreshold = 1000

    // Session tracking
    var sessionId: UUID = UUID()

    // MARK: - Coverage Cache

    /// Get cached coverage array, recomputing only when dirty
    private func getCoverageArray() -> [ActionCoverage] {
        if coverageDirty || cachedCoverageArray == nil {
            cachedCoverageArray = coverage.map {
                ActionCoverage(actionName: $0.key, count: $0.value.count, distinctStates: $0.value.states)
            }
            coverageDirty = false
        }
        return cachedCoverageArray ?? []
    }

    /// Mark coverage as dirty when updated
    private func markCoverageDirty() {
        coverageDirty = true
    }

    // MARK: - Public API

    /// Thread-safe parse method for use from readability handlers (background threads).
    /// Uses internal locking to prevent data races.
    func parseThreadSafe(_ data: Data) -> ModelCheckProgress? {
        lock.lock()
        defer { lock.unlock() }
        return parseInternal(data)
    }

    /// Parse incoming data from TLC stdout (thread-safe)
    func parse(_ data: Data) -> ModelCheckProgress? {
        lock.lock()
        defer { lock.unlock() }
        return parseInternal(data)
    }

    /// Internal parse implementation.
    /// Processes all complete lines in the chunk and returns the most recent progress update.
    private func parseInternal(_ data: Data) -> ModelCheckProgress? {
        let lines = lineBuffer.append(data)
        var latestProgress: ModelCheckProgress?

        for lineData in lines {
            guard let line = String(data: lineData, encoding: .utf8) else {
                continue
            }

            // Try JSON parsing first (TLC -tool mode)
            if line.hasPrefix("{") {
                if let progress = parseJSONLine(line) {
                    latestProgress = progress
                }
            } else {
                // Fall back to plain text parsing
                if let progress = parseTextLine(line) {
                    latestProgress = progress
                }
            }
        }

        return latestProgress
    }

    /// Get final result after TLC exits (synchronous version for small traces, thread-safe)
    func finalResult(exitCode: Int32, duration: TimeInterval) -> ModelCheckResult {
        lock.lock()
        defer { lock.unlock() }
        return ModelCheckResult(
            sessionId: sessionId,
            success: exitCode == 0 && errorTrace == nil && !detectedOOM,
            statesFound: states,
            distinctStates: distinct,
            duration: duration,
            coverage: getCoverageArray(),
            errorTrace: errorTrace,
            message: detectedOOM ? (errorMessage ?? "Out of memory") : errorMessage,
            outOfMemory: detectedOOM,
            suggestJVMRetry: detectedOOM
        )
    }

    /// Get final result with storage support for large traces (thread-safe)
    func finalResultWithStorage(exitCode: Int32, duration: TimeInterval) async -> ModelCheckResult {
        let (traceCount, capturedStates, capturedSessionId, capturedErrorType, capturedErrorMessage,
             capturedLoopStart, capturedViolatedProperty, capturedStatesFound, capturedDistinct, capturedCoverage) = lock.withLock {
            (currentTraceStates.count, currentTraceStates, sessionId, errorType, errorMessage,
             errorTrace?.loopStart, errorTrace?.violatedProperty, states, distinct, coverage)
        }

        if traceCount <= Self.largeTraceThreshold {
            return finalResult(exitCode: exitCode, duration: duration)
        }

        logger.info("Large trace detected (\(traceCount) states), streaming to disk")

        do {
            let traceWriter = try await TraceStorageManager.shared.beginTrace(sessionId: capturedSessionId)

            for state in capturedStates {
                try await traceWriter.append(state)
            }

            let lazyTrace = try await TraceStorageManager.shared.finalizeTrace(
                sessionId: capturedSessionId,
                type: capturedErrorType ?? .evaluationError,
                message: capturedErrorMessage ?? "Error found",
                loopStart: capturedLoopStart,
                violatedProperty: capturedViolatedProperty
            )

            logger.info("Trace stored successfully for session \(capturedSessionId.uuidString)")

            let capturedOOM = lock.withLock { detectedOOM }

            return ModelCheckResult(
                sessionId: capturedSessionId,
                success: exitCode == 0 && !capturedOOM,
                statesFound: capturedStatesFound,
                distinctStates: capturedDistinct,
                duration: duration,
                coverage: capturedCoverage.map { ActionCoverage(actionName: $0.key, count: $0.value.count, distinctStates: $0.value.states) },
                errorTrace: nil,  // Don't keep in-memory trace for large results
                message: capturedOOM ? (capturedErrorMessage ?? "Out of memory") : capturedErrorMessage,
                lazyErrorTrace: lazyTrace,
                outOfMemory: capturedOOM,
                suggestJVMRetry: capturedOOM
            )
        } catch {
            logger.error("Failed to store large trace: \(error.localizedDescription)")
            // Fall back to in-memory (may cause memory pressure)
            return finalResult(exitCode: exitCode, duration: duration)
        }
    }

    /// Reset parser state for a new run (thread-safe)
    func reset() {
        lock.lock()
        defer { lock.unlock() }
        lineBuffer.reset()
        states = 0
        distinct = 0
        statesLeft = 0
        coverage = [:]
        cachedCoverageArray = nil
        coverageDirty = false
        errorTrace = nil
        currentPhase = .parsing
        startTime = nil
        currentTraceStates = []
        isParsingTrace = false
        errorMessage = nil
        errorType = nil
        sessionId = UUID()
        detectedOOM = false
    }

    // MARK: - JSON Parsing

    private func parseJSONLine(_ line: String) -> ModelCheckProgress? {
        guard let data = line.data(using: .utf8),
              let json = try? JSONSerialization.jsonObject(with: data) as? [String: Any],
              let type = json["type"] as? String else {
            return nil
        }

        switch type {
        case "progress":
            return parseProgressJSON(json)

        case "error":
            parseErrorJSON(json)
            return ModelCheckProgress(
                sessionId: sessionId,
                phase: .error,
                statesFound: states,
                distinctStates: distinct,
                statesLeft: statesLeft
            )

        case "coverage":
            parseCoverageJSON(json)
            return nil

        case "state":
            parseStateJSON(json)
            return nil

        case "done":
            currentPhase = .done
            return ModelCheckProgress(
                sessionId: sessionId,
                phase: .done,
                statesFound: states,
                distinctStates: distinct,
                statesLeft: 0,
                coverage: getCoverageArray()
            )

        default:
            return nil
        }
    }

    private func parseProgressJSON(_ json: [String: Any]) -> ModelCheckProgress {
        states = json["states"] as? UInt64 ?? states
        distinct = json["distinct"] as? UInt64 ?? distinct
        statesLeft = json["queue"] as? UInt64 ?? statesLeft

        let duration = json["time"] as? TimeInterval ?? 0
        let sps = json["sps"] as? Double ?? 0
        let action = json["action"] as? String
        let memory = json["memory"] as? UInt64 ?? 0

        if let phase = json["phase"] as? String {
            currentPhase = ModelCheckProgress.Phase(rawValue: phase) ?? .computing
        } else {
            currentPhase = .computing
        }

        return ModelCheckProgress(
            sessionId: sessionId,
            phase: currentPhase,
            statesFound: states,
            distinctStates: distinct,
            statesLeft: statesLeft,
            duration: duration,
            statesPerSecond: sps,
            currentAction: action,
            coverage: getCoverageArray(),
            memoryUsed: memory
        )
    }

    private func parseErrorJSON(_ json: [String: Any]) {
        let message = json["message"] as? String ?? "Unknown error"
        let typeStr = json["errorType"] as? String ?? "error"

        let type: ErrorTrace.ErrorType
        switch typeStr {
        case "invariant":
            type = .invariantViolation
        case "deadlock":
            type = .deadlock
        case "liveness":
            type = .livenessViolation
        case "assertion":
            type = .assertionFailure
        case "temporal":
            type = .temporal
        default:
            type = .evaluationError
        }

        errorMessage = message
        errorType = type

        if let traceData = json["trace"] as? [[String: Any]] {
            var traceStates: [TraceState] = []
            for (index, stateData) in traceData.enumerated() {
                let action = stateData["action"] as? String
                var variables: [String: StateValue] = [:]

                if let vars = stateData["variables"] as? [String: Any] {
                    for (name, value) in vars {
                        if let stateValue = parseStateValue(value) {
                            variables[name] = stateValue
                        }
                    }
                }

                var location: SourceLocation?
                if let loc = stateData["location"] as? [String: Any] {
                    location = SourceLocation(
                        file: loc["file"] as? String,
                        line: loc["line"] as? Int ?? 0,
                        column: loc["column"] as? Int ?? 0
                    )
                }

                traceStates.append(TraceState(
                    id: index,
                    action: action,
                    variables: variables,
                    location: location
                ))
            }

            errorTrace = ErrorTrace(
                type: type,
                message: message,
                states: traceStates,
                loopStart: json["loopStart"] as? Int,
                violatedProperty: json["property"] as? String
            )
        }
    }

    private func parseCoverageJSON(_ json: [String: Any]) {
        if let actions = json["actions"] as? [String: [String: UInt64]] {
            for (name, data) in actions {
                coverage[name] = (
                    count: data["count"] ?? 0,
                    states: data["states"] ?? 0
                )
            }
            markCoverageDirty()
        }
    }

    private func parseStateJSON(_ json: [String: Any]) {
        let id = json["id"] as? Int ?? currentTraceStates.count
        let action = json["action"] as? String
        var variables: [String: StateValue] = [:]

        if let vars = json["variables"] as? [String: Any] {
            for (name, value) in vars {
                if let stateValue = parseStateValue(value) {
                    variables[name] = stateValue
                }
            }
        }

        currentTraceStates.append(TraceState(
            id: id,
            action: action,
            variables: variables,
            location: nil
        ))
    }

    private func parseStateValue(_ value: Any) -> StateValue? {
        if let intValue = value as? Int {
            return .int(intValue)
        } else if let stringValue = value as? String {
            // Check for boolean
            if stringValue == "TRUE" {
                return .bool(true)
            } else if stringValue == "FALSE" {
                return .bool(false)
            }
            return .string(stringValue)
        } else if let boolValue = value as? Bool {
            return .bool(boolValue)
        } else if let arrayValue = value as? [Any] {
            // Could be set, sequence, or tuple
            let elements = arrayValue.compactMap { parseStateValue($0) }
            return .sequence(elements)
        } else if let dictValue = value as? [String: Any] {
            // Record
            var record: [String: StateValue] = [:]
            for (key, val) in dictValue {
                if let stateVal = parseStateValue(val) {
                    record[key] = stateVal
                }
            }
            return .record(record)
        }
        return nil
    }

    // MARK: - Text Parsing

    private func parseTextLine(_ line: String) -> ModelCheckProgress? {
        let trimmed = line.trimmingCharacters(in: .whitespaces)

        // Check for OOM in stdout as well
        if checkForOOM(trimmed) {
            detectedOOM = true
            errorMessage = "Out of memory: \(trimmed)"
            errorType = .evaluationError
            currentPhase = .error
            return ModelCheckProgress(
                sessionId: sessionId,
                phase: .error,
                statesFound: states,
                distinctStates: distinct
            )
        }

        // Progress line: "Progress(X) at 2023-01-01 12:00:00: Y states generated, Z distinct states found, W states left on queue."
        if trimmed.hasPrefix("Progress(") {
            return parseProgressLine(trimmed)
        }

        // State count: "Finished computing initial states: X distinct states generated."
        if trimmed.contains("distinct states generated") || trimmed.contains("states found") {
            return parseStateCountLine(trimmed)
        }

        // Error line
        if trimmed.hasPrefix("Error:") || trimmed.contains("Invariant") && trimmed.contains("violated") {
            errorMessage = trimmed
            if trimmed.contains("Invariant") {
                errorType = .invariantViolation
            } else if trimmed.contains("Deadlock") {
                errorType = .deadlock
            }
            currentPhase = .error
            return ModelCheckProgress(
                sessionId: sessionId,
                phase: .error,
                statesFound: states,
                distinctStates: distinct
            )
        }

        // Trace state
        if trimmed.hasPrefix("State ") && trimmed.contains(":") {
            isParsingTrace = true
            parseTraceStateLine(trimmed)
            return nil
        }

        // Variable assignment in trace
        if isParsingTrace && trimmed.contains(" = ") {
            parseVariableLine(trimmed)
            return nil
        }

        // Coverage line
        if trimmed.hasPrefix("<") && trimmed.contains(" line ") {
            parseCoverageLine(trimmed)
            return nil
        }

        // Model checking complete
        if trimmed.contains("Model checking completed") || trimmed.contains("No error has been found") {
            currentPhase = .done
            return ModelCheckProgress(
                sessionId: sessionId,
                phase: .done,
                statesFound: states,
                distinctStates: distinct,
                statesLeft: 0
            )
        }

        return nil
    }

    private func parseProgressLine(_ line: String) -> ModelCheckProgress? {
        guard let match = TLCRegex.progressLine.firstMatch(in: line, range: NSRange(line.startIndex..., in: line)) else {
            return nil
        }

        if match.numberOfRanges >= 4 {
            if let range1 = Swift.Range(match.range(at: 1), in: line) {
                states = UInt64(line[range1]) ?? states
            }
            if let range2 = Swift.Range(match.range(at: 2), in: line) {
                distinct = UInt64(line[range2]) ?? distinct
            }
            if let range3 = Swift.Range(match.range(at: 3), in: line) {
                statesLeft = UInt64(line[range3]) ?? statesLeft
            }
        }

        currentPhase = .computing

        return ModelCheckProgress(
            sessionId: sessionId,
            phase: .computing,
            statesFound: states,
            distinctStates: distinct,
            statesLeft: statesLeft,
            coverage: getCoverageArray()
        )
    }

    private func parseStateCountLine(_ line: String) -> ModelCheckProgress? {
        guard let match = TLCRegex.stateCount.firstMatch(in: line, range: NSRange(line.startIndex..., in: line)),
              let range = Swift.Range(match.range(at: 1), in: line) else {
            return nil
        }

        distinct = UInt64(line[range]) ?? distinct

        return ModelCheckProgress(
            sessionId: sessionId,
            phase: currentPhase,
            statesFound: states,
            distinctStates: distinct
        )
    }

    private func parseTraceStateLine(_ line: String) {
        // State 1: <Initial predicate>
        // State 2: <Next>
        guard let match = TLCRegex.traceState.firstMatch(in: line, range: NSRange(line.startIndex..., in: line)) else {
            return
        }

        if match.numberOfRanges >= 3,
           let idRange = Swift.Range(match.range(at: 1), in: line),
           let actionRange = Swift.Range(match.range(at: 2), in: line) {
            let id = Int(line[idRange]) ?? currentTraceStates.count
            let action = String(line[actionRange])

            currentTraceStates.append(TraceState(
                id: id,
                action: action,
                variables: [:],
                location: nil
            ))
        }
    }

    private func parseVariableLine(_ line: String) {
        // /\ variable = value
        guard let match = TLCRegex.variable.firstMatch(in: line, range: NSRange(line.startIndex..., in: line)),
              !currentTraceStates.isEmpty else {
            return
        }

        if match.numberOfRanges >= 3,
           let nameRange = Swift.Range(match.range(at: 1), in: line),
           let valueRange = Swift.Range(match.range(at: 2), in: line) {
            let name = String(line[nameRange])
            let valueStr = String(line[valueRange])

            if let value = parseTextValue(valueStr) {
                let lastState = currentTraceStates.removeLast()
                var variables = lastState.variables
                variables[name] = value
                currentTraceStates.append(TraceState(
                    id: lastState.id,
                    action: lastState.action,
                    variables: variables,
                    location: lastState.location
                ))
            }
        }
    }

    private func parseTextValue(_ text: String) -> StateValue? {
        let trimmed = text.trimmingCharacters(in: .whitespaces)

        // Boolean
        if trimmed == "TRUE" {
            return .bool(true)
        } else if trimmed == "FALSE" {
            return .bool(false)
        }

        // Integer
        if let intValue = Int(trimmed) {
            return .int(intValue)
        }

        // String
        if trimmed.hasPrefix("\"") && trimmed.hasSuffix("\"") {
            let content = String(trimmed.dropFirst().dropLast())
            return .string(content)
        }

        // Set
        if trimmed.hasPrefix("{") && trimmed.hasSuffix("}") {
            // Simple parsing for basic sets
            let content = String(trimmed.dropFirst().dropLast())
            if content.isEmpty {
                return .set([])
            }
            // For now, store as string for complex sets
            return .string(trimmed)
        }

        // Sequence/Tuple
        if trimmed.hasPrefix("<<") && trimmed.hasSuffix(">>") {
            let content = String(trimmed.dropFirst(2).dropLast(2))
            if content.isEmpty {
                return .sequence([])
            }
            // Simple comma split for basic tuples
            let elements = content.split(separator: ",").compactMap { parseTextValue(String($0)) }
            return .sequence(elements)
        }

        // Default to string
        return .string(trimmed)
    }

    private func parseCoverageLine(_ line: String) {
        // <Next line X, col Y to line A, col B of module M>: 123
        guard let match = TLCRegex.coverage.firstMatch(in: line, range: NSRange(line.startIndex..., in: line)) else {
            return
        }

        if match.numberOfRanges >= 3,
           let nameRange = Swift.Range(match.range(at: 1), in: line),
           let countRange = Swift.Range(match.range(at: 2), in: line) {
            let name = String(line[nameRange])
            let count = UInt64(line[countRange]) ?? 0

            let existing = coverage[name] ?? (count: 0, states: 0)
            coverage[name] = (count: count, states: existing.states)
            markCoverageDirty()
        }
    }

    // MARK: - OOM Detection

    /// Check if a line indicates an OutOfMemoryError (JVM or GraalVM native image)
    private func checkForOOM(_ line: String) -> Bool {
        line.contains("OutOfMemoryError") ||
        line.contains("java.lang.OutOfMemoryError") ||
        line.contains("GC overhead limit exceeded") ||
        line.contains("Java heap space") ||
        line.contains("unable to create new native thread") ||
        (line.contains("Metaspace") && line.contains("OutOfMemory")) ||
        line.contains("failed to allocate") ||
        line.contains("Cannot reserve enough memory") ||
        line.contains("Native memory allocation") ||
        line.contains("Could not reserve enough space") ||
        line.contains("insufficient memory") ||
        line.contains("mmap failed") ||
        (line.contains("CommittedMemory") && line.contains("limit"))
    }

    /// Parse stderr line for OOM detection (thread-safe)
    func parseStderr(_ line: String) {
        lock.lock()
        defer { lock.unlock() }
        if checkForOOM(line) {
            detectedOOM = true
            errorMessage = "Out of memory: \(line)"
            errorType = .evaluationError
        }
    }

    /// Check if OOM was detected (thread-safe)
    func hasDetectedOOM() -> Bool {
        lock.lock()
        defer { lock.unlock() }
        return detectedOOM
    }

    // MARK: - Finalization

    /// Finalize error trace if we were building one (thread-safe)
    func finalizeErrorTrace() {
        lock.lock()
        defer { lock.unlock() }
        if !currentTraceStates.isEmpty, let type = errorType {
            errorTrace = ErrorTrace(
                type: type,
                message: errorMessage ?? "Error found",
                states: currentTraceStates,
                loopStart: nil,
                violatedProperty: nil
            )
        }
    }
}
