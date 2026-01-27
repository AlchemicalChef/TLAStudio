import Foundation

// MARK: - TLAPM Output Parser

/// Parses TLAPM toolbox output format (`@!!` prefixed lines)
///
/// TLAPM produces output in blocks delimited by `@!!BEGIN` and `@!!END`,
/// with key-value pairs in between using the `@!!key:value` format.
///
/// Example:
/// ```
/// @!!BEGIN
/// @!!type:obligation
/// @!!id:1
/// @!!loc:5:1:5:50
/// @!!status:proved
/// @!!prover:zenon
/// @!!duration:0.234
/// @!!END
/// ```
final class TLAPMOutputParser: @unchecked Sendable {

    // MARK: - State

    private let lock = NSLock()
    private var buffer = Data()
    private var currentBlock: [String: String] = [:]
    private var isInBlock = false
    private var obligations: [ParsedObligation] = []
    private var sessionId: UUID = UUID()
    private var specFileURL: URL?

    // Statistics
    private var totalObligations: Int = 0
    private var provedCount: Int = 0
    private var failedCount: Int = 0
    private var trivialCount: Int = 0

    // MARK: - Parsed Obligation (Internal)

    /// Internal representation of a parsed obligation before converting to ProofObligation
    struct ParsedObligation: Sendable {
        let uuid: UUID  // Stable UUID generated once when obligation is created
        let id: Int
        let fingerprint: String?
        let location: ProofSourceLocation?
        let status: ProofStatus
        let backend: ProverBackend?
        let duration: TimeInterval?
        let reason: String?
        let kind: ObligationKind
        let obligationText: String

        var isSuccess: Bool {
            status == .proved || status == .trivial
        }
    }

    // MARK: - Public API

    /// Set the session ID for this parsing run
    func setSessionId(_ id: UUID) {
        lock.lock()
        defer { lock.unlock() }
        sessionId = id
    }

    /// Set the specification file URL for location resolution
    func setSpecFileURL(_ url: URL) {
        lock.lock()
        defer { lock.unlock() }
        specFileURL = url
    }

    /// Parse incoming data from TLAPM stdout/stderr
    /// - Parameter data: Raw data from TLAPM
    /// - Returns: A proof progress update if one was parsed, nil otherwise
    func parse(_ data: Data) -> ProofCheckProgress? {
        lock.lock()
        defer { lock.unlock() }

        buffer.append(data)

        var latestProgress: ProofCheckProgress?

        // Process complete lines
        while let newlineIndex = buffer.firstIndex(of: UInt8(ascii: "\n")) {
            let lineData = buffer[..<newlineIndex]
            buffer = Data(buffer[buffer.index(after: newlineIndex)...])

            guard let line = String(data: lineData, encoding: .utf8)?
                .trimmingCharacters(in: .carriageReturns) else {
                continue
            }

            if let progress = parseLine(line) {
                latestProgress = progress
            }
        }

        return latestProgress
    }

    /// Get all parsed obligations converted to ProofObligation
    func getAllObligations() -> [ProofObligation] {
        lock.lock()
        defer { lock.unlock() }
        return obligations.map(convertToProofObligation)
    }

    /// Get the current trivial count (for final progress reporting)
    func getTrivialCount() -> Int {
        lock.lock()
        defer { lock.unlock() }
        return trivialCount
    }

    /// Get final result after TLAPM exits
    func finalResult(exitCode: Int32, duration: TimeInterval) -> ProofCheckResult {
        lock.lock()
        defer { lock.unlock() }

        let success = exitCode == 0 && failedCount == 0
        let convertedObligations = obligations.map(convertToProofObligation)

        return ProofCheckResult(
            success: success,
            obligations: convertedObligations,
            provedCount: provedCount + trivialCount,  // trivial counts as proved
            failedCount: failedCount,
            duration: duration,
            errorMessages: success ? [] : ["Some proof obligations failed"]
        )
    }

    /// Reset parser state for a new run
    func reset() {
        lock.lock()
        defer { lock.unlock() }

        buffer = Data()
        currentBlock = [:]
        isInBlock = false
        obligations = []
        sessionId = UUID()
        specFileURL = nil
        totalObligations = 0
        provedCount = 0
        failedCount = 0
        trivialCount = 0
    }

    // MARK: - Line Parsing

    private func parseLine(_ line: String) -> ProofCheckProgress? {
        // Check for toolbox format lines (@!! prefix)
        if line.hasPrefix("@!!") {
            let content = String(line.dropFirst(3)) // Remove "@!!"

            // Block delimiters
            if content == "BEGIN" {
                isInBlock = true
                currentBlock = [:]
                return nil
            }

            if content == "END" {
                isInBlock = false
                let result = processBlock()
                if result != nil {
                    NSLog("[PARSER] Block processed, obligations: %d", obligations.count)
                }
                return result
            }

            // Key-value pairs within a block
            if isInBlock, let colonIndex = content.firstIndex(of: ":") {
                let key = String(content[..<colonIndex])
                let value = String(content[content.index(after: colonIndex)...])
                currentBlock[key] = value
            }

            return nil
        }

        // Try to parse non-toolbox format: (* OBLIGATION N @from line:col:line:col@ status *)
        // This handles TLAPM versions that don't use --toolbox output
        if let progress = parseNonToolboxLine(line) {
            return progress
        }

        // Log non-toolbox output for debugging
        if !line.isEmpty {
            parseRegularOutput(line)
        }

        return nil
    }

    /// Parse the non-toolbox TLAPM output format
    /// Format: (* OBLIGATION N @from line:col:line:col@ status *)
    /// Or: (* OBLIGATION N @from line:col:line:col@ status prover:backend *)
    private func parseNonToolboxLine(_ line: String) -> ProofCheckProgress? {
        // Match: (* OBLIGATION N ... *)
        guard line.hasPrefix("(*") && line.hasSuffix("*)") else {
            return nil
        }

        let content = String(line.dropFirst(2).dropLast(2)).trimmingCharacters(in: .whitespaces)

        // Check for OBLIGATION line
        guard content.hasPrefix("OBLIGATION") else {
            return nil
        }

        // Extract obligation number
        let parts = content.components(separatedBy: .whitespaces).filter { !$0.isEmpty }
        guard parts.count >= 2, let id = Int(parts[1]) else {
            return nil
        }

        print("[PARSER] Found OBLIGATION \(id) in non-toolbox format")

        // Parse location if present: @from line:col:line:col@
        var location: ProofSourceLocation? = nil
        if let fromRange = content.range(of: "@from "),
           let endAt = content.range(of: "@", range: fromRange.upperBound..<content.endIndex) {
            let locString = String(content[fromRange.upperBound..<endAt.lowerBound])
            location = parseLocation(locString)
        }

        // Parse status
        var status: ProofStatus = .pending
        var backend: ProverBackend? = nil

        let lowercased = content.lowercased()
        if lowercased.contains("proved") || lowercased.contains("proven") {
            status = .proved
        } else if lowercased.contains("failed") {
            status = .failed
        } else if lowercased.contains("trivial") {
            status = .trivial
        } else if lowercased.contains("to be proved") {
            status = .pending
        } else if lowercased.contains("timeout") {
            status = .timeout
        }

        // Parse backend if present: prover:backend
        if let proverRange = content.range(of: "prover:") {
            let afterProver = content[proverRange.upperBound...]
            let proverName = afterProver.components(separatedBy: .whitespaces).first ?? ""
            backend = parseProverBackend(proverName)
        }

        print("[PARSER] Obligation \(id): status=\(status), backend=\(backend?.displayName ?? "none")")

        // Update or add obligation
        let existingIndex = obligations.firstIndex(where: { $0.id == id })
        let stableUUID = existingIndex.map { obligations[$0].uuid } ?? UUID()

        let obligation = ParsedObligation(
            uuid: stableUUID,
            id: id,
            fingerprint: nil,
            location: location,
            status: status,
            backend: backend,
            duration: nil,
            reason: nil,
            kind: .step,
            obligationText: content
        )

        if let existingIndex = existingIndex {
            // Decrement old status counter before updating
            let oldStatus = obligations[existingIndex].status
            decrementStatistics(for: oldStatus)
            obligations[existingIndex] = obligation
        } else {
            obligations.append(obligation)
            totalObligations += 1
        }

        // Update statistics for the new status
        incrementStatistics(for: status)

        return makeProgressUpdate(latestObligation: obligation)
    }

    private func parseRegularOutput(_ line: String) {
        // Handle non-toolbox output (warnings, errors, info)
        // This can be extended to capture additional diagnostic information
        if line.contains("Warning:") || line.contains("Error:") {
            // Could store these for display
        }
    }

    // MARK: - Block Processing

    private func processBlock() -> ProofCheckProgress? {
        guard let type = currentBlock["type"] else {
            return nil
        }

        switch type {
        case "obligation":
            return processObligationBlock()
        case "obligationsnumber":
            return processObligationsNumberBlock()
        case "status":
            return processStatusBlock()
        case "error":
            return processErrorBlock()
        case "warning":
            return processWarningBlock()
        default:
            return nil
        }
    }

    private func processObligationsNumberBlock() -> ProofCheckProgress? {
        // Handle the obligationsnumber block to set total count
        if let countStr = currentBlock["count"], let count = Int(countStr) {
            totalObligations = max(totalObligations, count)
            return makeProgressUpdate(latestObligation: nil)
        }
        return nil
    }

    private func processObligationBlock() -> ProofCheckProgress? {
        NSLog("[PARSER] processObligationBlock: currentBlock = %@", currentBlock.description)
        guard let idString = currentBlock["id"],
              let id = Int(idString) else {
            NSLog("[PARSER] processObligationBlock: No id found in block")
            return nil
        }

        NSLog("[PARSER] processObligationBlock: id=%d, loc='%@'", id, currentBlock["loc"] ?? "nil")
        let location = parseLocation(currentBlock["loc"])
        NSLog("[PARSER] processObligationBlock: parsed location = %@", location.map { "line \($0.startLine)" } ?? "nil")
        let status = parseObligationStatus(currentBlock["status"])
        let backend = parseProverBackend(currentBlock["prover"])
        let duration = currentBlock["duration"].flatMap { Double($0) }
        let reason = currentBlock["reason"]
        let fingerprint = currentBlock["fp"]
        let kind = parseObligationKind(currentBlock["kind"])
        let obligationText = currentBlock["obl"] ?? ""

        // Update or add obligation - preserve UUID for existing obligations
        let existingIndex = obligations.firstIndex(where: { $0.id == id })
        let stableUUID = existingIndex.map { obligations[$0].uuid } ?? UUID()

        let obligation = ParsedObligation(
            uuid: stableUUID,
            id: id,
            fingerprint: fingerprint,
            location: location,
            status: status,
            backend: backend,
            duration: duration,
            reason: reason,
            kind: kind,
            obligationText: obligationText
        )

        if let existingIndex = existingIndex {
            // Decrement old status counter before updating
            let oldStatus = obligations[existingIndex].status
            decrementStatistics(for: oldStatus)
            obligations[existingIndex] = obligation
        } else {
            obligations.append(obligation)
            totalObligations += 1
        }

        // Update statistics for the new status
        incrementStatistics(for: status)

        return makeProgressUpdate(latestObligation: obligation)
    }

    private func processStatusBlock() -> ProofCheckProgress? {
        // Status blocks provide overall progress information
        // Use max() to only update upward - avoid race condition where
        // a status block could reset totalObligations after obligations were already added
        if let total = currentBlock["total"].flatMap({ Int($0) }) {
            totalObligations = max(totalObligations, total)
        }

        return makeProgressUpdate(latestObligation: nil)
    }

    private func processErrorBlock() -> ProofCheckProgress? {
        // Handle error blocks from TLAPM
        let message = currentBlock["msg"] ?? "Unknown error"
        let location = parseLocation(currentBlock["loc"])

        // Create a failed obligation for the error
        let errorObligation = ParsedObligation(
            uuid: UUID(),
            id: obligations.count + 1,
            fingerprint: nil,
            location: location,
            status: .failed,
            backend: nil,
            duration: nil,
            reason: message,
            kind: .step,
            obligationText: message
        )

        obligations.append(errorObligation)
        totalObligations += 1  // Error blocks must also update totalObligations
        failedCount += 1

        return makeProgressUpdate(latestObligation: errorObligation)
    }

    private func processWarningBlock() -> ProofCheckProgress? {
        // Warnings don't change progress, but could be logged
        return nil
    }

    // MARK: - Helper Methods

    private func parseLocation(_ locationString: String?) -> ProofSourceLocation? {
        guard let locString = locationString else {
            return nil
        }

        // Format: "beginLine:beginCol:endLine:endCol" or "line:col"
        let parts = locString.split(separator: ":").compactMap { Int($0) }
        let fileURL = specFileURL ?? URL(fileURLWithPath: "unknown.tla")

        switch parts.count {
        case 2:
            return ProofSourceLocation(
                fileURL: fileURL,
                startLine: parts[0],
                startColumn: parts[1],
                endLine: parts[0],
                endColumn: parts[1]
            )
        case 4:
            return ProofSourceLocation(
                fileURL: fileURL,
                startLine: parts[0],
                startColumn: parts[1],
                endLine: parts[2],
                endColumn: parts[3]
            )
        default:
            return nil
        }
    }

    private func parseObligationStatus(_ statusString: String?) -> ProofStatus {
        guard let status = statusString else {
            return .pending
        }

        switch status.lowercased() {
        case "proved", "proven":
            return .proved
        case "failed":
            return .failed
        case "trivial":
            return .trivial
        case "checking", "proving", "pending":
            return .pending
        case "interrupted":
            return .pending  // Interrupted is treated as pending (can retry)
        case "timeout", "timedout":
            return .timeout
        case "omitted":
            return .omitted
        default:
            return .unknown
        }
    }

    private func parseProverBackend(_ proverString: String?) -> ProverBackend? {
        guard let prover = proverString else {
            return nil
        }

        switch prover.lowercased() {
        case "zenon":
            return .zenon
        case "z3", "smt":
            return .z3
        case "isabelle":
            return .isabelle
        case "spass":
            return .spass
        case "ls4":
            return .ls4
        case "cvc5":
            return .cvc5
        case "auto":
            return .auto
        default:
            return nil
        }
    }

    private func parseObligationKind(_ kindString: String?) -> ObligationKind {
        guard let kind = kindString else {
            return .step
        }

        switch kind.lowercased() {
        case "theorem":
            return .theorem
        case "lemma":
            return .lemma
        case "corollary":
            return .corollary
        case "proposition":
            return .proposition
        case "step":
            return .step
        case "qed":
            return .qed
        case "assertion", "assert":
            return .assertion
        case "suffices":
            return .suffices
        case "case":
            return .case_
        case "pick":
            return .pick
        case "have":
            return .have
        case "take":
            return .take
        case "witness":
            return .witness
        default:
            return .step
        }
    }

    private func incrementStatistics(for status: ProofStatus) {
        switch status {
        case .proved:
            provedCount += 1
        case .failed, .timeout:
            // Timeout counts as failed for statistics purposes
            failedCount += 1
        case .trivial:
            // Only increment trivialCount - don't also increment provedCount
            // to avoid double-counting in progress calculations
            trivialCount += 1
        case .pending, .unknown, .omitted:
            break
        }
    }

    private func decrementStatistics(for status: ProofStatus) {
        switch status {
        case .proved:
            provedCount = max(0, provedCount - 1)
        case .failed, .timeout:
            // Timeout counts as failed for statistics purposes
            failedCount = max(0, failedCount - 1)
        case .trivial:
            trivialCount = max(0, trivialCount - 1)
        case .pending, .unknown, .omitted:
            break
        }
    }

    private func makeProgressUpdate(latestObligation: ParsedObligation?) -> ProofCheckProgress {
        let phase: ProofPhase
        let completedCount = provedCount + failedCount + trivialCount
        if failedCount > 0 {
            phase = .error
        } else if completedCount == totalObligations && totalObligations > 0 {
            phase = .done
        } else {
            phase = .checking
        }

        let currentObl: ProofObligation? = latestObligation.map(convertToProofObligation)
        let convertedObligations = obligations.map(convertToProofObligation)

        return ProofCheckProgress(
            sessionId: sessionId,
            phase: phase,
            totalObligations: totalObligations,
            provedCount: provedCount,
            failedCount: failedCount,
            trivialCount: trivialCount,
            currentObligation: currentObl,
            obligations: convertedObligations
        )
    }

    private func convertToProofObligation(_ parsed: ParsedObligation) -> ProofObligation {
        let fileURL = specFileURL ?? URL(fileURLWithPath: "unknown.tla")
        let location = parsed.location ?? ProofSourceLocation(
            fileURL: fileURL,
            startLine: 1,
            startColumn: 1,
            endLine: 1,
            endColumn: 1
        )

        return ProofObligation(
            id: parsed.uuid,  // Use stable UUID from ParsedObligation
            fingerprint: parsed.fingerprint ?? "fp_\(parsed.id)",
            location: location,
            kind: parsed.kind,
            status: parsed.status,
            backend: parsed.backend,
            duration: parsed.duration,
            errorMessage: parsed.reason,
            parent: nil,
            children: [],
            obligationText: parsed.obligationText
        )
    }
}

// MARK: - Character Set Extension

private extension CharacterSet {
    static let carriageReturns = CharacterSet(charactersIn: "\r")
}

// MARK: - Proof Check Options

/// Options for proof checking
struct ProofCheckOptions: Codable, Sendable {
    var backend: ProverBackend?
    var timeout: TimeInterval
    var threads: Int
    var checkFromLine: Int?
    var checkToLine: Int?
    var stepName: String?
    var fingerprints: Bool
    var verbose: Bool

    init(
        backend: ProverBackend? = nil,
        timeout: TimeInterval = 30,
        threads: Int = 4,
        checkFromLine: Int? = nil,
        checkToLine: Int? = nil,
        stepName: String? = nil,
        fingerprints: Bool = true,
        verbose: Bool = false
    ) {
        self.backend = backend
        self.timeout = timeout
        self.threads = threads
        self.checkFromLine = checkFromLine
        self.checkToLine = checkToLine
        self.stepName = stepName
        self.fingerprints = fingerprints
        self.verbose = verbose
    }

    static let `default` = ProofCheckOptions()
}
