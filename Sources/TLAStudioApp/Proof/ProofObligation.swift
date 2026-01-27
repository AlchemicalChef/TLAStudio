// ProofObligation.swift
// TLAStudio
//
// Data models for TLAPS (TLA+ Proof System) integration.
// These types represent proof obligations, their status, and results
// from the proof checking process.

import Foundation

// MARK: - Source Location

/// Represents a location range within a TLA+ source file.
///
/// Used to identify where a proof obligation originates in the source code,
/// enabling precise navigation and highlighting in the editor.
public struct ProofSourceLocation: Codable, Hashable, Sendable {
    /// The URL of the source file containing this location.
    public let fileURL: URL

    /// The 1-based starting line number.
    public let startLine: Int

    /// The 1-based starting column number.
    public let startColumn: Int

    /// The 1-based ending line number.
    public let endLine: Int

    /// The 1-based ending column number.
    public let endColumn: Int

    public init(
        fileURL: URL,
        startLine: Int,
        startColumn: Int,
        endLine: Int,
        endColumn: Int
    ) {
        self.fileURL = fileURL
        self.startLine = startLine
        self.startColumn = startColumn
        self.endLine = endLine
        self.endColumn = endColumn
    }

    /// Returns a human-readable description of the location.
    public var description: String {
        let fileName = fileURL.lastPathComponent
        if startLine == endLine {
            return "\(fileName):\(startLine):\(startColumn)-\(endColumn)"
        } else {
            return "\(fileName):\(startLine):\(startColumn)-\(endLine):\(endColumn)"
        }
    }

    /// Checks if this location contains the given line and column.
    public func contains(line: Int, column: Int) -> Bool {
        if line < startLine || line > endLine {
            return false
        }
        if line == startLine && column < startColumn {
            return false
        }
        if line == endLine && column > endColumn {
            return false
        }
        return true
    }
}

// MARK: - Obligation Kind

/// The type of proof obligation.
///
/// TLA+ proofs can contain various kinds of proof steps and statements,
/// each represented by a different obligation kind.
public enum ObligationKind: String, Codable, CaseIterable, Sendable {
    /// A top-level theorem statement.
    case theorem

    /// A lemma, typically a helper result for larger proofs.
    case lemma

    /// A corollary that follows from a theorem.
    case corollary

    /// A proposition statement.
    case proposition

    /// A numbered proof step (e.g., <1>1, <2>3).
    case step

    /// A QED step that concludes a proof or sub-proof.
    case qed

    /// An ASSERT statement within a proof.
    case assertion

    /// A SUFFICES step that reformulates the goal.
    case suffices

    /// A CASE step in a case analysis.
    case case_

    /// A PICK step for existential instantiation.
    case pick

    /// A HAVE step introducing a fact.
    case have

    /// A TAKE step for universal instantiation.
    case take

    /// A WITNESS step providing an existential witness.
    case witness

    /// Human-readable display name for the obligation kind.
    public var displayName: String {
        switch self {
        case .theorem: return "Theorem"
        case .lemma: return "Lemma"
        case .corollary: return "Corollary"
        case .proposition: return "Proposition"
        case .step: return "Step"
        case .qed: return "QED"
        case .assertion: return "Assertion"
        case .suffices: return "Suffices"
        case .case_: return "Case"
        case .pick: return "Pick"
        case .have: return "Have"
        case .take: return "Take"
        case .witness: return "Witness"
        }
    }

    // Custom coding to handle the underscore in case_
    private enum CodingKeys: String, CodingKey {
        case rawValue
    }

    public init(from decoder: Decoder) throws {
        let container = try decoder.singleValueContainer()
        let rawValue = try container.decode(String.self)

        // Handle "case" from external sources (TLAPM output)
        if rawValue == "case" {
            self = .case_
        } else if let kind = ObligationKind(rawValue: rawValue) {
            self = kind
        } else {
            throw DecodingError.dataCorruptedError(
                in: container,
                debugDescription: "Unknown obligation kind: \(rawValue)"
            )
        }
    }

    public func encode(to encoder: Encoder) throws {
        var container = encoder.singleValueContainer()
        // Encode case_ as "case" for external compatibility
        if self == .case_ {
            try container.encode("case")
        } else {
            try container.encode(rawValue)
        }
    }
}

// MARK: - Proof Status

/// The status of a proof obligation.
///
/// Represents the current state of verification for a proof obligation,
/// from unknown through various terminal states.
public enum ProofStatus: String, Codable, CaseIterable, Sendable {
    /// The obligation has not been checked yet.
    case unknown

    /// The obligation is queued for checking.
    case pending

    /// The obligation was successfully proved.
    case proved

    /// The prover failed to prove the obligation.
    case failed

    /// The prover timed out while checking the obligation.
    case timeout

    /// The proof was explicitly omitted by the user.
    case omitted

    /// The obligation was proved trivially (no backend needed).
    case trivial

    /// Human-readable display name for the status.
    public var displayName: String {
        switch self {
        case .unknown: return "Unknown"
        case .pending: return "Pending"
        case .proved: return "Proved"
        case .failed: return "Failed"
        case .timeout: return "Timeout"
        case .omitted: return "Omitted"
        case .trivial: return "Trivial"
        }
    }

    /// Whether this status represents a successful outcome.
    public var isSuccess: Bool {
        switch self {
        case .proved, .trivial:
            return true
        case .unknown, .pending, .failed, .timeout, .omitted:
            return false
        }
    }

    /// Whether this status represents a terminal (final) state.
    public var isTerminal: Bool {
        switch self {
        case .proved, .failed, .timeout, .omitted, .trivial:
            return true
        case .unknown, .pending:
            return false
        }
    }

    /// SF Symbol name for visual representation.
    public var symbolName: String {
        switch self {
        case .unknown: return "questionmark.circle"
        case .pending: return "clock"
        case .proved: return "checkmark.circle.fill"
        case .failed: return "xmark.circle.fill"
        case .timeout: return "clock.badge.exclamationmark"
        case .omitted: return "minus.circle"
        case .trivial: return "checkmark.circle"
        }
    }
}

// MARK: - Prover Backend

/// The backend prover used to check an obligation.
///
/// TLAPM supports multiple backend provers, each with different
/// strengths and characteristics.
public enum ProverBackend: String, Codable, CaseIterable, Sendable {
    /// Automatic backend selection by TLAPM.
    case auto

    /// Zenon, a first-order theorem prover.
    case zenon

    /// Z3, an SMT solver from Microsoft Research.
    case z3

    /// Isabelle/TLA+, an interactive theorem prover backend.
    case isabelle

    /// CVC5, an SMT solver.
    case cvc5

    /// SPASS, a first-order theorem prover.
    case spass

    /// LS4, a prover for temporal logic.
    case ls4

    /// Human-readable display name for the backend.
    public var displayName: String {
        switch self {
        case .auto: return "Auto"
        case .zenon: return "Zenon"
        case .z3: return "Z3"
        case .isabelle: return "Isabelle"
        case .cvc5: return "CVC5"
        case .spass: return "SPASS"
        case .ls4: return "LS4"
        }
    }

    /// The default timeout for this backend in seconds.
    ///
    /// Different backends have different typical solving times,
    /// so we provide appropriate defaults for each.
    public var defaultTimeout: TimeInterval {
        switch self {
        case .auto: return 15.0
        case .zenon: return 10.0
        case .z3: return 15.0
        case .isabelle: return 30.0
        case .cvc5: return 15.0
        case .spass: return 20.0
        case .ls4: return 10.0
        }
    }

    /// Command-line argument to pass to TLAPM for this backend.
    public var tlapmArgument: String {
        switch self {
        case .auto: return "--method auto"
        case .zenon: return "--method zenon"
        case .z3: return "--method smt"
        case .isabelle: return "--method isabelle"
        case .cvc5: return "--method cvc5"
        case .spass: return "--method spass"
        case .ls4: return "--method ls4"
        }
    }

    /// Brief description of the backend's capabilities.
    public var descriptionText: String {
        switch self {
        case .auto:
            return "Automatically selects the best backend for each obligation."
        case .zenon:
            return "First-order theorem prover, good for propositional and simple first-order goals."
        case .z3:
            return "SMT solver from Microsoft Research, handles arithmetic and quantifiers well."
        case .isabelle:
            return "Interactive theorem prover backend, powerful but slower."
        case .cvc5:
            return "Modern SMT solver with strong theory support."
        case .spass:
            return "First-order theorem prover with good performance on pure logic."
        case .ls4:
            return "Specialized prover for temporal logic formulas."
        }
    }
}

// MARK: - Proof Obligation

/// A single proof obligation generated by TLAPM.
///
/// Represents an individual verification task within a TLA+ proof.
/// Each obligation has a unique fingerprint from TLAPM that can be
/// used for caching results across sessions.
public struct ProofObligation: Identifiable, Codable, Hashable, Sendable {
    /// Unique identifier for this obligation instance.
    public let id: UUID

    /// TLAPM-generated fingerprint for caching.
    ///
    /// This fingerprint is computed by TLAPM based on the obligation's
    /// content and dependencies. It remains stable across runs as long
    /// as the underlying specification doesn't change.
    public let fingerprint: String

    /// Source location of the obligation in the TLA+ file.
    public let location: ProofSourceLocation

    /// The kind of proof construct this obligation represents.
    public let kind: ObligationKind

    /// Current verification status of the obligation.
    public var status: ProofStatus

    /// The backend prover used (or to be used) for this obligation.
    public var backend: ProverBackend?

    /// Time taken to check this obligation, if completed.
    public var duration: TimeInterval?

    /// Error message if the obligation failed.
    public var errorMessage: String?

    /// Parent obligation ID for hierarchical proof structure.
    public let parent: UUID?

    /// Child obligation IDs for hierarchical proof structure.
    public var children: [UUID]

    /// The textual representation of the obligation.
    ///
    /// This is the actual logical formula that needs to be proved,
    /// as generated by TLAPM.
    public let obligationText: String

    public init(
        id: UUID = UUID(),
        fingerprint: String,
        location: ProofSourceLocation,
        kind: ObligationKind,
        status: ProofStatus = .unknown,
        backend: ProverBackend? = nil,
        duration: TimeInterval? = nil,
        errorMessage: String? = nil,
        parent: UUID? = nil,
        children: [UUID] = [],
        obligationText: String
    ) {
        self.id = id
        self.fingerprint = fingerprint
        self.location = location
        self.kind = kind
        self.status = status
        self.backend = backend
        self.duration = duration
        self.errorMessage = errorMessage
        self.parent = parent
        self.children = children
        self.obligationText = obligationText
    }

    /// Returns a copy of this obligation with an updated status.
    public func with(status: ProofStatus) -> ProofObligation {
        var copy = self
        copy.status = status
        return copy
    }

    /// Returns a copy of this obligation with updated results.
    public func withResult(
        status: ProofStatus,
        backend: ProverBackend?,
        duration: TimeInterval?,
        errorMessage: String?
    ) -> ProofObligation {
        var copy = self
        copy.status = status
        copy.backend = backend
        copy.duration = duration
        copy.errorMessage = errorMessage
        return copy
    }

    // MARK: Hashable

    public func hash(into hasher: inout Hasher) {
        hasher.combine(id)
    }

    public static func == (lhs: ProofObligation, rhs: ProofObligation) -> Bool {
        lhs.id == rhs.id
    }
}

// MARK: - Proof Phase

/// The current phase of a proof checking session.
public enum ProofPhase: String, Codable, CaseIterable, Sendable {
    /// TLAPM is parsing the specification.
    case parsing

    /// TLAPM is checking proof obligations.
    case checking

    /// Proof checking has completed.
    case done

    /// An error occurred during proof checking.
    case error

    /// Human-readable display name for the phase.
    public var displayName: String {
        switch self {
        case .parsing: return "Parsing"
        case .checking: return "Checking"
        case .done: return "Done"
        case .error: return "Error"
        }
    }

    /// Whether this phase represents an active (non-terminal) state.
    public var isActive: Bool {
        switch self {
        case .parsing, .checking:
            return true
        case .done, .error:
            return false
        }
    }
}

// MARK: - Proof Progress

/// Progress update during a proof checking session.
///
/// Used for streaming updates to the UI during long-running proof
/// checking operations.
public struct ProofProgress: Identifiable, Codable, Sendable {
    /// Unique identifier for this progress update.
    public var id: UUID { sessionId }

    /// Session identifier for correlating progress updates.
    public let sessionId: UUID

    /// Current phase of the proof checking process.
    public let phase: ProofPhase

    /// Total number of obligations to check.
    public let totalObligations: Int

    /// Number of obligations successfully proved.
    public let provedCount: Int

    /// Number of obligations that failed.
    public let failedCount: Int

    /// Number of obligations still pending.
    public let pendingCount: Int

    /// The obligation currently being checked, if any.
    public let currentObligation: ProofObligation?

    public init(
        sessionId: UUID,
        phase: ProofPhase,
        totalObligations: Int,
        provedCount: Int,
        failedCount: Int,
        pendingCount: Int,
        currentObligation: ProofObligation? = nil
    ) {
        self.sessionId = sessionId
        self.phase = phase
        self.totalObligations = totalObligations
        self.provedCount = provedCount
        self.failedCount = failedCount
        self.pendingCount = pendingCount
        self.currentObligation = currentObligation
    }

    /// The completion percentage (0.0 to 1.0).
    public var completionPercentage: Double {
        guard totalObligations > 0 else { return 0.0 }
        // Use totalObligations - pendingCount to correctly include trivial obligations
        let completed = totalObligations - pendingCount
        return Double(completed) / Double(totalObligations)
    }

    /// Human-readable status message.
    public var statusMessage: String {
        switch phase {
        case .parsing:
            return "Parsing specification..."
        case .checking:
            // Include trivial in completed count
            let completed = totalObligations - pendingCount
            return "Checking obligations: \(completed)/\(totalObligations)"
        case .done:
            if failedCount == 0 {
                // provedCount should include trivial (from parser fix)
                return "All \(provedCount) obligations proved"
            } else {
                return "\(provedCount) proved, \(failedCount) failed"
            }
        case .error:
            return "Error during proof checking"
        }
    }
}

// MARK: - Proof Check Result

/// The final result of a proof checking session.
///
/// Contains the complete results including all obligations and
/// summary statistics.
public struct ProofCheckResult: Codable, Sendable {
    /// Whether all obligations were successfully proved.
    public let success: Bool

    /// All proof obligations with their final statuses.
    public let obligations: [ProofObligation]

    /// Number of obligations successfully proved.
    public let provedCount: Int

    /// Number of obligations that failed.
    public let failedCount: Int

    /// Total time taken for the proof checking session.
    public let duration: TimeInterval

    /// Any error messages encountered during checking.
    public let errorMessages: [String]

    public init(
        success: Bool,
        obligations: [ProofObligation],
        provedCount: Int,
        failedCount: Int,
        duration: TimeInterval,
        errorMessages: [String]
    ) {
        self.success = success
        self.obligations = obligations
        self.provedCount = provedCount
        self.failedCount = failedCount
        self.duration = duration
        self.errorMessages = errorMessages
    }

    /// Creates a result from a collection of obligations.
    public static func from(
        obligations: [ProofObligation],
        duration: TimeInterval,
        errorMessages: [String] = []
    ) -> ProofCheckResult {
        let provedCount = obligations.filter { $0.status.isSuccess }.count
        let failedCount = obligations.filter {
            $0.status == .failed || $0.status == .timeout
        }.count
        let success = failedCount == 0 && errorMessages.isEmpty

        return ProofCheckResult(
            success: success,
            obligations: obligations,
            provedCount: provedCount,
            failedCount: failedCount,
            duration: duration,
            errorMessages: errorMessages
        )
    }

    /// Obligations grouped by their status.
    public var obligationsByStatus: [ProofStatus: [ProofObligation]] {
        Dictionary(grouping: obligations) { $0.status }
    }

    /// Only the failed obligations for easy access.
    public var failedObligations: [ProofObligation] {
        obligations.filter { $0.status == .failed || $0.status == .timeout }
    }

    /// Summary string for display.
    public var summary: String {
        let total = obligations.count
        if success {
            return "All \(total) proof obligation(s) verified in \(String(format: "%.2f", duration))s"
        } else {
            return "\(provedCount)/\(total) proved, \(failedCount) failed in \(String(format: "%.2f", duration))s"
        }
    }
}

// MARK: - Obligation Tree

/// A tree representation of proof obligations for hierarchical display.
public struct ObligationTree: Identifiable, Sendable {
    public let id: UUID
    public let obligation: ProofObligation
    public var children: [ObligationTree]

    public init(obligation: ProofObligation, children: [ObligationTree] = []) {
        self.id = obligation.id
        self.obligation = obligation
        self.children = children
    }

    /// Builds a forest of obligation trees from a flat list.
    public static func buildForest(from obligations: [ProofObligation]) -> [ObligationTree] {
        var childrenMap: [UUID: [ProofObligation]] = [:]
        var roots: [ProofObligation] = []

        for obligation in obligations {
            if let parentId = obligation.parent {
                childrenMap[parentId, default: []].append(obligation)
            } else {
                roots.append(obligation)
            }
        }

        func buildTree(for obligation: ProofObligation) -> ObligationTree {
            let children = childrenMap[obligation.id, default: []]
                .sorted { $0.location.startLine < $1.location.startLine }
                .map { buildTree(for: $0) }
            return ObligationTree(obligation: obligation, children: children)
        }

        return roots
            .sorted { $0.location.startLine < $1.location.startLine }
            .map { buildTree(for: $0) }
    }
}
