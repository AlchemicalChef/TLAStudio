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

    /// Each single-step check runs under its OWN registry id so a stale call's
    /// tail cleanup can never unregister a newer run that reused the session
    /// id (the shared-id clobber race, bug-review-2026-06-09d #1). Tracked so
    /// stop() can terminate in-flight step processes too.
    private var activeStepSessionIds = Set<UUID>()

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

        // Capture identifiers up front so the cancellation/dealloc paths below can still
        // emit completion notifications without dereferencing self. Pattern mirrors
        // TLCSession.start() — see TLCProcessManager.swift:806-814.
        let capturedSpecURL = specURL
        let capturedOptions = options
        let capturedSessionId = id

        task = Task { @MainActor [weak self] in
            do {
                let finalResult = try await TLAPMProcessManager.shared.startProofCheck(
                    spec: capturedSpecURL,
                    options: capturedOptions,
                    sessionId: capturedSessionId
                ) { [weak self] progressUpdate in
                    Task { @MainActor in
                        self?.handleProgress(progressUpdate)
                    }
                }

                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                // Guard against self being deallocated during await
                guard let self else { return }

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

                // Guard against self being deallocated during await
                guard let self else { return }

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

    /// Check a single proof step at the given location.
    /// - Parameters:
    ///   - backend: Override the session's default prover for this check.
    ///   - timeout: Override the session's timeout (the workbench's
    ///     "retry with more time" action).
    func checkStep(line: Int, column: Int, backend: ProverBackend? = nil, timeout: TimeInterval? = nil) {
        logger.info("checkStep called: line=\(line), column=\(column), isRunning=\(self.isRunning)")
        guard !isRunning else {
            logger.debug("checkStep: BLOCKED - isRunning is true")
            return
        }

        isRunning = true
        error = nil
        result = nil
        progress = nil

        // Capture state needed by the Task body so weak self can be dereferenced lazily.
        let capturedSpecURL = specURL
        let capturedBackend = backend ?? options.backend
        let capturedTimeout = timeout ?? options.timeout
        let capturedLibraryPaths = options.additionalLibraryPaths ?? []
        let stepSessionId = UUID()
        activeStepSessionIds.insert(stepSessionId)

        task = Task { @MainActor [weak self] in
            defer { self?.activeStepSessionIds.remove(stepSessionId) }
            do {
                let obligation = try await TLAPMProcessManager.shared.checkSingleStep(
                    spec: capturedSpecURL,
                    line: line,
                    column: column,
                    backend: capturedBackend,
                    timeout: capturedTimeout,
                    sessionId: stepSessionId,
                    additionalLibraryPaths: capturedLibraryPaths
                )

                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                // Guard against self being deallocated during await
                guard let self else { return }

                logger.info("checkStep: Got obligation result: \(String(describing: obligation.status))")

                // Update or add the obligation
                self.updateObligation(obligation)
                self.isRunning = false
            } catch {
                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                // Guard against self being deallocated during await
                guard let self else { return }

                logger.error("checkStep: \(String(describing: error))")
                self.error = error
                self.result = nil
                self.isRunning = false
            }
        }
    }

    /// Re-check one obligation, optionally with a different backend and/or a
    /// stretched timeout — the failed-proof workbench's retry actions.
    func retryObligation(
        _ obligation: ProofObligation,
        backend: ProverBackend? = nil,
        timeoutMultiplier: Double = 1
    ) {
        checkStep(
            line: obligation.location.startLine,
            column: obligation.location.startColumn,
            backend: backend,
            timeout: options.timeout * max(1, timeoutMultiplier)
        )
    }

    /// Obligations that need attention (failed or timed out).
    var failedObligations: [ProofObligation] {
        obligations.filter { $0.status == .failed || $0.status == .timeout }
    }

    /// Re-check only the failed/timed-out obligations, sequentially — the fast
    /// iteration loop after editing a proof, instead of re-running the whole
    /// spec.
    func recheckFailedObligations() {
        guard !isRunning else { return }
        let failed = failedObligations
        guard !failed.isEmpty else { return }

        isRunning = true
        error = nil
        progress = nil

        let capturedSpecURL = specURL
        let capturedOptions = options
        let stepSessionId = UUID()
        activeStepSessionIds.insert(stepSessionId)

        task = Task { @MainActor [weak self] in
            defer { self?.activeStepSessionIds.remove(stepSessionId) }
            for obligation in failed {
                guard !Task.isCancelled else { break }
                do {
                    let updated = try await TLAPMProcessManager.shared.checkSingleStep(
                        spec: capturedSpecURL,
                        line: obligation.location.startLine,
                        column: obligation.location.startColumn,
                        backend: capturedOptions.backend,
                        timeout: capturedOptions.timeout,
                        sessionId: stepSessionId,
                        additionalLibraryPaths: capturedOptions.additionalLibraryPaths ?? []
                    )
                    guard !Task.isCancelled, let self else { return }
                    self.updateObligation(updated)
                } catch {
                    guard !Task.isCancelled, let self else { return }
                    logger.error("recheckFailedObligations: \(String(describing: error))")
                    self.error = error
                    break
                }
            }
            self?.isRunning = false
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

        // Use synchronous process termination via ProcessRegistry — the main
        // session plus any in-flight single-step checks (per-call ids).
        ProcessRegistry.shared.terminate(id)
        for stepId in activeStepSessionIds {
            ProcessRegistry.shared.terminate(stepId)
        }
        activeStepSessionIds.removeAll()
    }

    /// Stop the session and wait for async cleanup to complete
    func stopAsync() async {
        isRunning = false
        task?.cancel()
        task = nil
        let stepIds = activeStepSessionIds
        activeStepSessionIds.removeAll()
        await TLAPMProcessManager.shared.stop(sessionId: id)
        for stepId in stepIds {
            await TLAPMProcessManager.shared.stop(sessionId: stepId)
        }
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
    /// (SF Symbol + color live in Views/StatusIconography.swift)
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
}
