import Foundation
import Combine
import os

/// State machine for one interactive simulation of a spec: holds the manually
/// built trace, the enabled successors of the current state, and the results
/// of in-state expression evaluations.
///
/// All mutation happens on the main actor; TLC work runs through the injected
/// `SimulationExpanding` runner. A monotonic generation counter discards
/// results that arrive after the user has already moved on (reset, restart,
/// step) — the same pattern as `TLADocument.semanticCheckGeneration`.
@MainActor
final class SimulationSession: ObservableObject {

    // MARK: - Types

    enum Phase: Equatable {
        /// Loading the initial states.
        case loadingInitialStates
        /// More than one initial state — the user must pick one.
        case choosingInitialState
        /// A current state exists; successors are loaded.
        case ready
        /// Expanding the current state or evaluating an expression.
        case working
        case failed(String)
    }

    struct TraceEntry: Identifiable, Equatable {
        let id: Int
        /// Action that led here (nil for the initial state).
        let actionLabel: String?
        let state: SimState
    }

    struct EvaluationEntry: Identifiable, Equatable {
        let id: Int
        let expression: String
        /// Trace index the expression was evaluated in.
        let stateIndex: Int
        let result: Result<String, SimulationError>
    }

    // MARK: - Published State

    @Published private(set) var phase: Phase = .loadingInitialStates
    @Published private(set) var initialStates: [SimState] = []
    @Published private(set) var trace: [TraceEntry] = []
    @Published private(set) var successors: [SimSuccessor] = []
    @Published private(set) var successorsTruncated = false
    @Published private(set) var evaluations: [EvaluationEntry] = []

    var currentState: SimState? { trace.last?.state }

    /// Variables that changed in the most recent step (for highlighting).
    var lastChangedVariables: Set<String> {
        guard trace.count >= 2 else { return [] }
        return trace[trace.count - 1].state.changedVariableNames(from: trace[trace.count - 2].state)
    }

    // MARK: - Internals

    let context: SimulationSpecContext
    private let runner: any SimulationExpanding
    private let logger = Log.logger(category: "SimulationSession")

    /// Invalidates in-flight stepping work whenever the user changes direction.
    private var generation = 0
    /// Invalidates in-flight evaluations only when the history is cleared
    /// (start/reset/choose), so an evaluation result still lands after the
    /// user steps — stepping doesn't erase the history it's tagged into.
    private var evaluationEpoch = 0
    private var nextEntryID = 0
    private var nextEvaluationID = 0
    private let expansionCache = GenericLRUCache<SimState, SimExpansion>(capacity: 128)

    /// Retained so cancellation propagates into the runner and terminates the
    /// underlying TLC subprocess (JavaProcessRunner is cancellation-aware).
    private var expansionTask: Task<Void, Never>?
    private var evaluationTask: Task<Void, Never>?

    init(context: SimulationSpecContext, runner: any SimulationExpanding = SimulationRunner.shared) {
        self.context = context
        self.runner = runner
    }

    // MARK: - Lifecycle

    /// Load the initial states. Auto-enters the sole initial state when there
    /// is exactly one.
    func start() {
        expansionTask?.cancel()
        evaluationTask?.cancel()
        generation += 1
        evaluationEpoch += 1
        let generation = self.generation
        phase = .loadingInitialStates
        trace = []
        successors = []
        evaluations = []
        initialStates = []

        expansionTask = Task { @MainActor [weak self] in
            guard let self else { return }
            let result = await self.runner.enumerateInitialStates(context: self.context)
            guard self.generation == generation else { return }

            switch result {
            case .failure(let error):
                self.phase = .failed(error.localizedDescription)
            case .success(let expansion):
                self.initialStates = expansion.origins
                if expansion.origins.count == 1 {
                    self.enterState(expansion.origins[0], via: nil)
                } else {
                    self.phase = .choosingInitialState
                }
            }
        }
    }

    /// Discard any in-flight work and terminate its TLC subprocesses. Called
    /// when the owning document closes or replaces the session.
    func invalidate() {
        generation += 1
        evaluationEpoch += 1
        expansionTask?.cancel()
        evaluationTask?.cancel()
        expansionTask = nil
        evaluationTask = nil
    }

    // MARK: - Stepping

    func chooseInitialState(_ state: SimState) {
        guard initialStates.contains(state) else { return }
        evaluationEpoch += 1
        trace = []
        evaluations = []
        enterState(state, via: nil)
    }

    func step(_ successor: SimSuccessor) {
        guard phase == .ready, successors.contains(successor) else { return }
        enterState(successor.state, via: successor.actionLabel)
    }

    func stepBack() {
        guard trace.count > 1 else { return }
        generation += 1
        expansionTask?.cancel()
        trace.removeLast()
        // Drop evaluations tagged to the abandoned suffix — after a different
        // re-step, their "S<n>" labels would point at a different state.
        evaluations.removeAll { $0.stateIndex >= trace.count }
        if let state = currentState {
            loadSuccessors(of: state)
        }
    }

    /// Back to the initial-state choice (or the sole initial state).
    func reset() {
        guard !initialStates.isEmpty else {
            start()
            return
        }
        generation += 1
        evaluationEpoch += 1
        expansionTask?.cancel()
        evaluationTask?.cancel()
        trace = []
        evaluations = []
        if initialStates.count == 1 {
            enterState(initialStates[0], via: nil)
        } else {
            successors = []
            phase = .choosingInitialState
        }
    }

    private func enterState(_ state: SimState, via actionLabel: String?) {
        trace.append(TraceEntry(id: nextEntryID, actionLabel: actionLabel, state: state))
        nextEntryID += 1
        loadSuccessors(of: state)
    }

    private func loadSuccessors(of state: SimState) {
        if let cached = expansionCache.get(state) {
            successors = cached.successors
            successorsTruncated = cached.truncated
            phase = .ready
            return
        }

        generation += 1
        let generation = self.generation
        phase = .working
        successors = []

        expansionTask?.cancel()
        expansionTask = Task { @MainActor [weak self] in
            guard let self else { return }
            let result = await self.runner.expand(state, context: self.context)
            guard self.generation == generation else { return }

            switch result {
            case .failure(let error):
                self.phase = .failed(error.localizedDescription)
            case .success(let expansion):
                self.expansionCache.set(state, value: expansion)
                self.successors = expansion.successors
                self.successorsTruncated = expansion.truncated
                self.phase = .ready
            }
        }
    }

    // MARK: - Expression Evaluation

    func evaluate(_ expression: String) {
        guard let state = currentState else { return }
        let trimmed = expression.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return }

        let epoch = evaluationEpoch
        let stateIndex = trace.count - 1

        evaluationTask?.cancel()
        evaluationTask = Task { @MainActor [weak self] in
            guard let self else { return }
            let result = await self.runner.evaluate(trimmed, in: state, context: self.context)
            guard self.evaluationEpoch == epoch else { return }

            self.evaluations.insert(EvaluationEntry(
                id: self.nextEvaluationID,
                expression: trimmed,
                stateIndex: stateIndex,
                result: result
            ), at: 0)
            self.nextEvaluationID += 1
            if self.evaluations.count > 50 {
                self.evaluations.removeLast(self.evaluations.count - 50)
            }
        }
    }
}
