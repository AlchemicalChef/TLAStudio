import Foundation
import os
import SwiftUI

private let logger = Log.logger(category: "ProofSession")

// MARK: - Proof Session

/// Observable object for tracking a TLAPM proof session in the UI.
///
/// This class wraps `TLAPMSession` functionality and provides a unified interface
/// for the proof obligations panel. It manages the proof checking lifecycle and
/// provides convenient access to statistics and summary information.
@MainActor
final class ProofSession: ObservableObject {

    // MARK: - Properties

    let id: UUID
    let specURL: URL

    @Published private(set) var isRunning = false
    @Published private(set) var progress: ProofProgress?
    @Published private(set) var result: ProofCheckResult?
    @Published private(set) var error: Error?
    @Published private(set) var obligations: [ProofObligation] = []
    @Published var options: ProofCheckOptions

    private var task: Task<Void, Never>?

    // MARK: - Initialization

    init(specURL: URL, options: ProofCheckOptions = .default) {
        self.id = UUID()
        self.specURL = specURL
        self.options = options
    }

    // MARK: - Session Control

    /// Start proof checking for the entire specification
    func start() {
        guard !isRunning else { return }

        isRunning = true
        error = nil
        result = nil
        obligations = []

        task = Task {
            do {
                let finalResult = try await TLAPMProcessManager.shared.startProofCheck(
                    spec: specURL,
                    options: options,
                    sessionId: id
                ) { [weak self] progressUpdate in
                    Task { @MainActor in
                        self?.handleProgress(progressUpdate)
                    }
                }

                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                self.result = finalResult
                self.obligations = finalResult.obligations
                self.isRunning = false

                // Send completion notification
                let moduleName = self.specURL.deletingPathExtension().lastPathComponent
                CompletionNotifier.shared.notifyProofComplete(
                    success: finalResult.success,
                    moduleName: moduleName,
                    proved: finalResult.provedCount,
                    failed: finalResult.failedCount,
                    duration: finalResult.duration
                )
            } catch {
                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                self.error = error
                self.isRunning = false

                // Send failure notification
                let moduleName = self.specURL.deletingPathExtension().lastPathComponent
                CompletionNotifier.shared.notifyProofComplete(
                    success: false,
                    moduleName: moduleName,
                    proved: 0,
                    failed: 0,
                    duration: 0
                )
            }
        }
    }

    /// Check a single proof step at the given location
    func checkStep(line: Int, column: Int, backend: ProverBackend? = nil) {
        logger.info("checkStep called: line=\(line), column=\(column), isRunning=\(self.isRunning)")
        guard !isRunning else {
            logger.debug("checkStep: BLOCKED - isRunning is true")
            return
        }

        isRunning = true
        error = nil

        task = Task {
            do {
                let obligation = try await TLAPMProcessManager.shared.checkSingleStep(
                    spec: specURL,
                    line: line,
                    column: column,
                    backend: backend ?? options.backend,
                    timeout: options.timeout,
                    sessionId: self.id
                )

                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                logger.info("checkStep: Got obligation result: \(String(describing: obligation.status))")

                // Update or add the obligation
                self.updateObligation(obligation)
                self.isRunning = false
            } catch {
                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                logger.error("checkStep: \(String(describing: error))")
                self.error = error
                self.isRunning = false
            }
        }
    }

    /// Stop the current proof checking session synchronously
    func stop() {
        // Cancel the task first to prevent it from setting isRunning after we clear it
        let taskToCancel = task
        task = nil
        taskToCancel?.cancel()

        // Now mark as not running - safe because we've already cancelled the task
        isRunning = false

        // Use synchronous process termination via ProcessRegistry
        ProcessRegistry.shared.terminate(id)
    }

    /// Stop the session and wait for async cleanup to complete
    func stopAsync() async {
        isRunning = false
        task?.cancel()
        task = nil
        await TLAPMProcessManager.shared.stop(sessionId: id)
    }

    /// Clear all results
    func clearResults() {
        obligations = []
        result = nil
        progress = nil
        error = nil
    }

    // MARK: - Statistics

    /// Summary statistics for the current obligations
    var statistics: (proved: Int, failed: Int, pending: Int, total: Int) {
        var proved = 0
        var failed = 0
        var pending = 0

        for obligation in obligations {
            switch obligation.status {
            case .proved, .trivial:
                proved += 1
            case .failed, .timeout:
                failed += 1
            case .pending, .unknown, .omitted:
                pending += 1
            }
        }

        return (proved, failed, pending, obligations.count)
    }

    /// Summary string for display
    var summaryString: String {
        let stats = statistics
        guard stats.total > 0 else { return "No obligations" }

        var parts: [String] = []
        if stats.proved > 0 {
            parts.append("\(stats.proved)/\(stats.total) proved")
        }
        if stats.failed > 0 {
            parts.append("\(stats.failed) failed")
        }
        if stats.pending > 0 {
            parts.append("\(stats.pending) pending")
        }

        return parts.joined(separator: ", ")
    }

    /// Whether all obligations are successfully proved
    var allProved: Bool {
        let stats = statistics
        return stats.total > 0 && stats.failed == 0 && stats.pending == 0
    }

    /// Whether any obligation failed
    var hasFailed: Bool {
        statistics.failed > 0
    }

    // MARK: - Obligation Tree

    /// Get obligations as a hierarchical tree structure
    var obligationTree: [ObligationTree] {
        ObligationTree.buildForest(from: obligations)
    }

    /// Find an obligation by ID
    func findObligation(by id: UUID) -> ProofObligation? {
        obligations.first { $0.id == id }
    }

    // MARK: - Private Helpers

    private func handleProgress(_ progressUpdate: ProofCheckProgress) {
        self.progress = ProofProgress(
            sessionId: progressUpdate.sessionId,
            phase: progressUpdate.phase,
            totalObligations: progressUpdate.totalObligations,
            provedCount: progressUpdate.provedCount,
            failedCount: progressUpdate.failedCount,
            pendingCount: progressUpdate.pendingCount,
            currentObligation: progressUpdate.currentObligation
        )

        // Update obligations list from progress
        if !progressUpdate.obligations.isEmpty {
            self.obligations = progressUpdate.obligations
        }
    }

    private func updateObligation(_ obligation: ProofObligation) {
        // Find existing obligation by fingerprint or location
        if let index = obligations.firstIndex(where: { $0.fingerprint == obligation.fingerprint }) {
            obligations[index] = obligation
        } else if let index = obligations.firstIndex(where: {
            $0.location.startLine == obligation.location.startLine &&
            $0.location.startColumn == obligation.location.startColumn
        }) {
            obligations[index] = obligation
        } else {
            obligations.append(obligation)
        }
    }
}

// MARK: - Proof Check Progress

/// Progress update during proof checking, used for UI updates.
/// This bridges the internal `ProofProgress` type with additional context.
struct ProofCheckProgress: Sendable {
    let sessionId: UUID
    let phase: ProofPhase
    let totalObligations: Int
    let provedCount: Int
    let failedCount: Int
    let trivialCount: Int
    let currentObligation: ProofObligation?
    let obligations: [ProofObligation]

    var fractionComplete: Double {
        guard totalObligations > 0 else { return 0 }
        let completed = provedCount + failedCount + trivialCount
        return Double(completed) / Double(totalObligations)
    }

    var pendingCount: Int {
        totalObligations - provedCount - failedCount - trivialCount
    }
}

// MARK: - Prover Backend Extension

extension ProverBackend {
    /// Command-line flag to pass to TLAPM
    var flag: String {
        switch self {
        case .auto: return ""
        case .zenon: return "--method zenon"
        case .z3: return "--method smt"
        case .isabelle: return "--method isabelle"
        case .cvc5: return "--method cvc5"
        case .spass: return "--method spass"
        case .ls4: return "--method ls4"
        }
    }

    /// Short display name for badges
    var shortName: String {
        switch self {
        case .auto: return "A"
        case .zenon: return "Z"
        case .z3: return "S"
        case .isabelle: return "I"
        case .cvc5: return "C"
        case .spass: return "P"
        case .ls4: return "L"
        }
    }
}

// MARK: - Proof Status Extension

extension ProofStatus {
    /// Unicode icon for display
    var icon: String {
        switch self {
        case .unknown: return "?"
        case .pending: return "\u{22EF}"     // ⋯
        case .proved: return "\u{2713}"      // ✓
        case .failed: return "\u{2717}"      // ✗
        case .timeout: return "\u{23F0}"     // ⏰
        case .omitted: return "\u{25CB}"     // ○
        case .trivial: return "\u{2728}"     // ✨
        }
    }

    /// Color for UI display
    var color: Color {
        switch self {
        case .unknown: return .secondary
        case .pending: return .secondary
        case .proved: return .green
        case .failed: return .red
        case .timeout: return .orange
        case .omitted: return .secondary
        case .trivial: return .green
        }
    }
}
