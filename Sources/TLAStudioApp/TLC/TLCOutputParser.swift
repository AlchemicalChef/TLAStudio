import Foundation
import os

// MARK: - Pre-compiled Regex Patterns

/// Pre-compiled regex patterns for TLC output parsing.
/// These are compiled once at load time to avoid repeated compilation overhead.
private enum TLCRegex {
    /// Progress line: "X states generated, Y distinct states, Z states left"
    static let progressLine = try! NSRegularExpression(
        pattern: #"([0-9][0-9,]*) states generated.*?([0-9][0-9,]*) distinct states.*?([0-9][0-9,]*) states left"#
    )

    /// State count: "X distinct states"
    static let stateCount = try! NSRegularExpression(
        pattern: #"([0-9][0-9,]*) distinct states"#
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
        pattern: #"<(\w+)[^>]+>:\s*([0-9][0-9,]*)"#
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
    private var pendingTraceState: TraceState?
    /// Single-consumer streaming writer. Replaces the former per-state chained
    /// Task pattern, which built an O(N) retain chain of un-started Tasks
    /// synchronously under the parse lock (each Task captured its predecessor +
    /// a TraceState). The producer now yields to `traceWriteContinuation` (O(1),
    /// no allocation, no lock-held burst); one `traceConsumerTask` opens the
    /// writer once and drains the stream serially to disk.
    private var traceWriteContinuation: AsyncStream<TraceState>.Continuation?
    private var traceConsumerTask: Task<Void, Error>?
    private var streamingFallbackStates: [TraceState] = []
    private var streamedTraceCount = 0
    private var isParsingTrace = false
    private var errorMessage: String?
    private var traceLoopStart: Int?
    private var traceViolatedProperty: String?

    // Cached coverage array to avoid repeated map transformations
    private var cachedCoverageArray: [ActionCoverage]?
    private var coverageDirty = false
    private var errorType: ErrorTrace.ErrorType?

    /// Whether an OutOfMemoryError was detected during parsing
    private(set) var detectedOOM = false

    /// Non-fatal warnings/diagnostics that were observed but not surfaced as
    /// hard errors. Includes:
    /// - text-mode lines starting with `Warning:`,
    /// - JSON envelopes with an unrecognised `type` field,
    /// - text-mode lines that match `Error:` but no known classification.
    /// Lock-protected; flushed into `ModelCheckResult.warnings` at finalisation.
    private var collectedWarnings: [String] = []

    /// Lock for thread-safe access from readability handlers
    private let lock = NSLock()

    private let logger = Log.logger(category: "TLCOutputParser")

    /// Threshold for streaming trace states to disk (above this, use lazy loading)
    static let largeTraceThreshold = 1000

    /// Cap on number of warnings collected to bound memory under runaway output.
    private static let warningCap = 200

    /// Append a warning under lock, respecting `warningCap`.
    /// Caller must already hold `lock`.
    private func appendWarningLocked(_ text: String) {
        guard collectedWarnings.count < Self.warningCap else { return }
        collectedWarnings.append(text)
    }

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
        return finalResult(exitCode: exitCode, duration: duration, incomplete: false)
    }

    /// Internal entry point allowing callers (notably `finalResultWithStorage`)
    /// to flag that the result is partial — e.g. trace finalisation failed and
    /// the in-memory fallback path was taken.
    func finalResult(exitCode: Int32, duration: TimeInterval, incomplete: Bool) -> ModelCheckResult {
        lock.lock()
        defer { lock.unlock() }
        flushPendingTraceStateLocked()
        let retainedTraceStates = streamingFallbackStates.isEmpty
            ? currentTraceStates
            : streamingFallbackStates + currentTraceStates
        let retainedErrorTrace = errorTrace ?? makeErrorTrace(from: retainedTraceStates)
        // Treat any non-zero exit without an OOM signal and without a classified
        // error trace as `incomplete` — TLC produced output we couldn't fully
        // explain, and downstream UI should not claim success.
        let unclassifiedExit = exitCode != 0 && retainedErrorTrace == nil && !detectedOOM
        let isIncomplete = incomplete || unclassifiedExit
        return ModelCheckResult(
            sessionId: sessionId,
            success: exitCode == 0 && retainedErrorTrace == nil && !detectedOOM,
            statesFound: states,
            distinctStates: distinct,
            duration: duration,
            coverage: getCoverageArray(),
            errorTrace: retainedErrorTrace,
            message: detectedOOM ? (errorMessage ?? "Out of memory") : errorMessage,
            outOfMemory: detectedOOM,
            suggestJVMRetry: detectedOOM,
            warnings: collectedWarnings,
            incomplete: isIncomplete
        )
    }

    /// Get final result with storage support for large traces (thread-safe)
    func finalResultWithStorage(exitCode: Int32, duration: TimeInterval) async -> ModelCheckResult {
        let (traceCount, capturedStates, capturedSessionId, capturedErrorType, capturedErrorMessage,
             capturedLoopStart, capturedViolatedProperty, capturedStatesFound, capturedDistinct,
             capturedCoverage, capturedOOM, capturedWarnings, writeContinuation, consumerTask) = lock.withLock {
            flushPendingTraceStateLocked()
            return (
                currentTraceStates.count + streamedTraceCount,
                currentTraceStates,
                sessionId,
                errorType,
                errorMessage,
                traceLoopStart ?? errorTrace?.loopStart,
                traceViolatedProperty ?? errorTrace?.violatedProperty,
                states,
                distinct,
                coverage,
                detectedOOM,
                collectedWarnings,
                traceWriteContinuation,
                traceConsumerTask
            )
        }

        if let consumerTask {
            logger.info("Finalizing streamed trace with \(traceCount) states")

            do {
                // Close the stream so the consumer's for-await loop ends, then wait
                // for it to drain every queued append (rethrows on writer failure).
                writeContinuation?.finish()
                try await consumerTask.value

                let lazyTrace = try await TraceStorageManager.shared.finalizeTrace(
                    sessionId: capturedSessionId,
                    type: capturedErrorType ?? .evaluationError,
                    message: capturedErrorMessage ?? "Error found",
                    loopStart: capturedLoopStart,
                    violatedProperty: capturedViolatedProperty
                )

                let hasErrorTrace = traceCount > 0 || capturedErrorType != nil || capturedErrorMessage != nil

                return ModelCheckResult(
                    sessionId: capturedSessionId,
                    success: exitCode == 0 && !hasErrorTrace && !capturedOOM,
                    statesFound: capturedStatesFound,
                    distinctStates: capturedDistinct,
                    duration: duration,
                    coverage: capturedCoverage.map { ActionCoverage(actionName: $0.key, count: $0.value.count, distinctStates: $0.value.states) },
                    errorTrace: nil,
                    message: capturedOOM ? (capturedErrorMessage ?? "Out of memory") : capturedErrorMessage,
                    lazyErrorTrace: lazyTrace,
                    outOfMemory: capturedOOM,
                    suggestJVMRetry: capturedOOM,
                    warnings: capturedWarnings,
                    // Unclassified non-zero exit with no error trace signals partial output.
                    incomplete: exitCode != 0 && !hasErrorTrace && !capturedOOM
                )
            } catch {
                // F-S7-error-prop-007: trace finaliser failed; we fall back to
                // the in-memory `finalResult` path but flag the result as
                // incomplete so callers don't claim success on partial data.
                logger.error("Failed to finalize streamed trace: \(error.localizedDescription)")
                return finalResult(exitCode: exitCode, duration: duration, incomplete: true)
            }
        }

        guard traceCount > Self.largeTraceThreshold else {
            return finalResult(exitCode: exitCode, duration: duration)
        }

        logger.info("Large trace detected at finalization (\(traceCount) states), writing to disk")

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

            let hasErrorTrace = traceCount > 0 || capturedErrorType != nil || capturedErrorMessage != nil

            return ModelCheckResult(
                sessionId: capturedSessionId,
                success: exitCode == 0 && !hasErrorTrace && !capturedOOM,
                statesFound: capturedStatesFound,
                distinctStates: capturedDistinct,
                duration: duration,
                coverage: capturedCoverage.map { ActionCoverage(actionName: $0.key, count: $0.value.count, distinctStates: $0.value.states) },
                errorTrace: nil,  // Don't keep in-memory trace for large results
                message: capturedOOM ? (capturedErrorMessage ?? "Out of memory") : capturedErrorMessage,
                lazyErrorTrace: lazyTrace,
                outOfMemory: capturedOOM,
                suggestJVMRetry: capturedOOM,
                warnings: capturedWarnings,
                incomplete: exitCode != 0 && !hasErrorTrace && !capturedOOM
            )
        } catch {
            // F-S7-error-prop-007: storing the large trace failed; we degrade
            // to the in-memory fallback but flag the result as incomplete.
            logger.error("Failed to store large trace: \(error.localizedDescription)")
            return finalResult(exitCode: exitCode, duration: duration, incomplete: true)
        }
    }

    private func appendCompletedTraceStateLocked(_ state: TraceState) {
        if traceWriteContinuation != nil {
            // Once streaming-to-disk is active, post-bootstrap states go to disk only.
            // `streamingFallbackStates` retains only the pre-threshold snapshot seeded
            // by `startTraceStreamingLocked` so the synchronous-fallback path can still
            // emit a partial trace if the writer fails. Retaining every streamed state
            // here would defeat the OOM mitigation entirely.
            enqueueTraceWriteLocked(state, retainForFallback: false)
            return
        }

        currentTraceStates.append(state)
        if currentTraceStates.count > Self.largeTraceThreshold {
            startTraceStreamingLocked()
        }
    }

    private func flushPendingTraceStateLocked() {
        guard let pendingTraceState else {
            return
        }
        self.pendingTraceState = nil
        appendCompletedTraceStateLocked(pendingTraceState)
    }

    private func startTraceStreamingLocked() {
        guard traceWriteContinuation == nil else {
            return
        }

        let capturedSessionId = sessionId
        let statesToStream = currentTraceStates
        streamingFallbackStates = statesToStream
        currentTraceStates.removeAll(keepingCapacity: false)

        // One consumer opens the writer once and drains the stream serially. The
        // stream buffers states the producer yields before/faster-than the writer
        // (unbounded, matching the prior chain's behaviour, but without a Task or
        // retain link per state).
        let (stream, continuation) = AsyncStream<TraceState>.makeStream()
        traceWriteContinuation = continuation
        traceConsumerTask = Task<Void, Error> {
            let writer = try await TraceStorageManager.shared.beginTrace(sessionId: capturedSessionId)
            for await state in stream {
                try Task.checkCancellation()
                try await writer.append(state)
            }
        }

        for state in statesToStream {
            enqueueTraceWriteLocked(state, retainForFallback: false)
        }
    }

    private func enqueueTraceWriteLocked(_ state: TraceState, retainForFallback: Bool = true) {
        guard let continuation = traceWriteContinuation else {
            currentTraceStates.append(state)
            return
        }

        if retainForFallback {
            streamingFallbackStates.append(state)
        }

        continuation.yield(state)
        streamedTraceCount += 1
    }

    private func traceStateCountLocked() -> Int {
        streamedTraceCount + currentTraceStates.count + (pendingTraceState == nil ? 0 : 1)
    }

    private func makeErrorTrace(from states: [TraceState]) -> ErrorTrace? {
        guard !states.isEmpty, errorType != nil || errorMessage != nil else {
            return nil
        }
        return ErrorTrace(
            type: errorType ?? .evaluationError,
            message: errorMessage ?? "Error found",
            states: states,
            loopStart: traceLoopStart,
            violatedProperty: traceViolatedProperty
        )
    }

    /// Reset parser state for a new run (thread-safe)
    func reset() {
        lock.lock()
        defer { lock.unlock() }
        traceWriteContinuation?.finish()
        traceConsumerTask?.cancel()
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
        pendingTraceState = nil
        streamingFallbackStates = []
        traceWriteContinuation = nil
        traceConsumerTask = nil
        streamedTraceCount = 0
        isParsingTrace = false
        errorMessage = nil
        errorType = nil
        traceLoopStart = nil
        traceViolatedProperty = nil
        sessionId = UUID()
        detectedOOM = false
        collectedWarnings = []
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

        case "warning":
            // F-S7-error-prop-001: surface warnings rather than dropping them.
            let message = (json["message"] as? String) ?? "Unknown TLC warning"
            logger.notice("TLC warning: \(message, privacy: .public)")
            appendWarningLocked("TLC warning: \(message)")
            return nil

        default:
            // F-S7-error-prop-001: unknown JSON envelope kind — record raw line
            // so it surfaces in `ModelCheckResult.warnings` instead of vanishing.
            logger.notice("Unhandled TLC JSON message type: \(type, privacy: .public)")
            appendWarningLocked("Unhandled TLC JSON message type: \(type) — \(line)")
            return nil
        }
    }

    private func parseProgressJSON(_ json: [String: Any]) -> ModelCheckProgress {
        states = parseUInt64JSONValue(json["states"]) ?? states
        distinct = parseUInt64JSONValue(json["distinct"]) ?? distinct
        statesLeft = parseUInt64JSONValue(json["queue"]) ?? statesLeft

        let duration = parseDoubleJSONValue(json["time"]) ?? 0
        let sps = parseDoubleJSONValue(json["sps"]) ?? 0
        let action = json["action"] as? String
        let memory = parseUInt64JSONValue(json["memory"]) ?? 0

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
        traceLoopStart = parseIntJSONValue(json["loopStart"])
        traceViolatedProperty = json["property"] as? String

        if let traceData = json["trace"] as? [[String: Any]] {
            if traceWriteContinuation == nil && streamedTraceCount == 0 {
                pendingTraceState = nil
                currentTraceStates.removeAll(keepingCapacity: true)
            }

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
                        line: parseIntJSONValue(loc["line"]) ?? 0,
                        column: parseIntJSONValue(loc["column"]) ?? 0
                    )
                }

                appendCompletedTraceStateLocked(TraceState(
                    id: index,
                    action: action,
                    variables: variables,
                    location: location
                ))
            }

            if traceWriteContinuation == nil {
                errorTrace = ErrorTrace(
                    type: type,
                    message: message,
                    states: currentTraceStates,
                    loopStart: traceLoopStart,
                    violatedProperty: traceViolatedProperty
                )
            } else {
                errorTrace = nil
            }
        }
    }

    private func parseCoverageJSON(_ json: [String: Any]) {
        if let actions = json["actions"] as? [String: Any] {
            for (name, data) in actions {
                guard let data = data as? [String: Any] else { continue }
                coverage[name] = (
                    count: parseUInt64JSONValue(data["count"]) ?? 0,
                    states: parseUInt64JSONValue(data["states"]) ?? 0
                )
            }
            markCoverageDirty()
        }
    }

    private func parseStateJSON(_ json: [String: Any]) {
        let id = parseIntJSONValue(json["id"]) ?? traceStateCountLocked()
        let action = json["action"] as? String
        var variables: [String: StateValue] = [:]

        if let vars = json["variables"] as? [String: Any] {
            for (name, value) in vars {
                if let stateValue = parseStateValue(value) {
                    variables[name] = stateValue
                }
            }
        }

        appendCompletedTraceStateLocked(TraceState(
            id: id,
            action: action,
            variables: variables,
            location: nil
        ))
    }

    private func parseStateValue(_ value: Any) -> StateValue? {
        if let numberValue = value as? NSNumber {
            if isJSONBoolean(numberValue) {
                return .bool(numberValue.boolValue)
            }
            if let intValue = parseIntJSONValue(numberValue) {
                return .int(intValue)
            }
        } else if let boolValue = value as? Bool {
            return .bool(boolValue)
        } else if let intValue = parseIntJSONValue(value) {
            return .int(intValue)
        } else if let stringValue = value as? String {
            // Check for boolean
            if stringValue == "TRUE" {
                return .bool(true)
            } else if stringValue == "FALSE" {
                return .bool(false)
            }
            return .string(stringValue)
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

    private func parseUInt64JSONValue(_ value: Any?) -> UInt64? {
        if let value = value as? UInt64 {
            return value
        } else if let value = value as? UInt {
            return UInt64(value)
        } else if let value = value as? Int, value >= 0 {
            return UInt64(value)
        } else if let value = value as? Int64, value >= 0 {
            return UInt64(value)
        } else if let value = value as? NSNumber, !isJSONBoolean(value) {
            let doubleValue = value.doubleValue
            guard doubleValue.isFinite,
                  doubleValue >= 0,
                  doubleValue.rounded(.towardZero) == doubleValue else { return nil }
            return value.uint64Value
        } else if let value = value as? String {
            return UInt64(value.replacingOccurrences(of: ",", with: ""))
        }
        return nil
    }

    private func parseIntJSONValue(_ value: Any?) -> Int? {
        if let value = value as? Int {
            return value
        } else if let value = value as? Int64 {
            return Int(value)
        } else if let value = value as? UInt64, value <= UInt64(Int.max) {
            return Int(value)
        } else if let value = value as? NSNumber, !isJSONBoolean(value) {
            let doubleValue = value.doubleValue
            guard doubleValue.isFinite,
                  doubleValue >= Double(Int.min),
                  doubleValue <= Double(Int.max),
                  doubleValue.rounded(.towardZero) == doubleValue else { return nil }
            return value.intValue
        } else if let value = value as? String {
            return Int(value.replacingOccurrences(of: ",", with: ""))
        }
        return nil
    }

    private func parseDoubleJSONValue(_ value: Any?) -> Double? {
        if let value = value as? Double {
            return value
        } else if let value = value as? Int {
            return Double(value)
        } else if let value = value as? UInt64 {
            return Double(value)
        } else if let value = value as? NSNumber, !isJSONBoolean(value) {
            return value.doubleValue
        } else if let value = value as? String {
            return Double(value.replacingOccurrences(of: ",", with: ""))
        }
        return nil
    }

    private func isJSONBoolean(_ value: NSNumber) -> Bool {
        CFGetTypeID(value) == CFBooleanGetTypeID()
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

        // Warning line — collect for surfacing via ModelCheckResult.warnings
        // rather than silently dropping (F-S7-error-prop-001).
        if trimmed.hasPrefix("Warning:") {
            logger.notice("TLC warning: \(trimmed, privacy: .public)")
            appendWarningLocked(trimmed)
            return nil
        }

        // Error line — text-mode classification.
        // F-S7-error-prop-006: cover more TLC error tokens (TLC2272 parse,
        // TLC2273 config, OOM, assertion, liveness, temporal).
        if trimmed.hasPrefix("Error:")
            || (trimmed.contains("Invariant") && trimmed.contains("violated"))
            || trimmed.contains("TLC2272")
            || trimmed.contains("TLC2273")
            || trimmed.contains("java.lang.OutOfMemoryError") {
            errorMessage = trimmed
            errorType = classifyTextModeError(trimmed)
            if errorType == .evaluationError && trimmed.contains("java.lang.OutOfMemoryError") {
                detectedOOM = true
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
                states = parseTLCUInt(line[range1]) ?? states
            }
            if let range2 = Swift.Range(match.range(at: 2), in: line) {
                distinct = parseTLCUInt(line[range2]) ?? distinct
            }
            if let range3 = Swift.Range(match.range(at: 3), in: line) {
                statesLeft = parseTLCUInt(line[range3]) ?? statesLeft
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

        distinct = parseTLCUInt(line[range]) ?? distinct

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
            flushPendingTraceStateLocked()

            let id = Int(line[idRange]).map { max(0, $0 - 1) } ?? traceStateCountLocked()
            let action = String(line[actionRange])

            pendingTraceState = TraceState(
                id: id,
                action: action,
                variables: [:],
                location: nil
            )
        }
    }

    private func parseVariableLine(_ line: String) {
        // /\ variable = value
        guard let match = TLCRegex.variable.firstMatch(in: line, range: NSRange(line.startIndex..., in: line)),
              let lastState = pendingTraceState else {
            return
        }

        if match.numberOfRanges >= 3,
           let nameRange = Swift.Range(match.range(at: 1), in: line),
           let valueRange = Swift.Range(match.range(at: 2), in: line) {
            let name = String(line[nameRange])
            let valueStr = String(line[valueRange])

            if let value = parseTextValue(valueStr) {
                var variables = lastState.variables
                variables[name] = value
                pendingTraceState = TraceState(
                    id: lastState.id,
                    action: lastState.action,
                    variables: variables,
                    location: lastState.location
                )
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
            let count = parseTLCUInt(line[countRange]) ?? 0

            let existing = coverage[name] ?? (count: 0, states: 0)
            coverage[name] = (count: count, states: existing.states)
            markCoverageDirty()
        }
    }

    private func parseTLCUInt<S: StringProtocol>(_ value: S) -> UInt64? {
        UInt64(value.replacingOccurrences(of: ",", with: ""))
    }

    /// Classify a text-mode TLC error line into an `ErrorTrace.ErrorType`.
    ///
    /// Extends the previous coverage (which only recognised "Invariant" /
    /// "Deadlock") to assertion, liveness, temporal, OOM and the TLC2272/2273
    /// parse/config family. See F-S7-error-prop-006 in the May-2026 audit.
    private func classifyTextModeError(_ line: String) -> ErrorTrace.ErrorType {
        if line.contains("Invariant") && line.contains("violated") {
            return .invariantViolation
        }
        if line.contains("Deadlock") || line.contains("deadlock") {
            return .deadlock
        }
        if line.contains("Assertion") || line.contains("assertion") {
            return .assertionFailure
        }
        if line.contains("liveness") || line.contains("Liveness") || line.contains("stuttering") {
            return .livenessViolation
        }
        if line.contains("Temporal") || line.contains("temporal property") {
            return .temporal
        }
        // TLC2272: parse failures; TLC2273: config-file errors.
        // OutOfMemory and the GraalVM "unable to allocate" family map to
        // evaluationError (with `detectedOOM` already set by the caller when
        // the OOM marker is present).
        return .evaluationError
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
        flushPendingTraceStateLocked()
        if traceWriteContinuation == nil, !currentTraceStates.isEmpty, let type = errorType {
            errorTrace = ErrorTrace(
                type: type,
                message: errorMessage ?? "Error found",
                states: currentTraceStates,
                loopStart: traceLoopStart,
                violatedProperty: traceViolatedProperty
            )
        }
    }
}
