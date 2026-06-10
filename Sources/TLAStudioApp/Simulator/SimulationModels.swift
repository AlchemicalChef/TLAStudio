import Foundation

// MARK: - Simulation State Model

/// One variable binding in a simulated state. `rawValue` is the value text
/// exactly as TLC printed it — kept verbatim so states round-trip losslessly
/// when spliced back into a generated `INIT` predicate for the next step.
struct SimVariable: Equatable, Hashable, Identifiable {
    let name: String
    let rawValue: String

    var id: String { name }
}

/// A concrete state in the interactive simulation, identified by its full
/// assignment of raw TLC-printed values (sorted by variable name).
struct SimState: Equatable, Hashable {
    let variables: [SimVariable]

    init(variables: [SimVariable]) {
        self.variables = variables.sorted { $0.name < $1.name }
    }

    var variableNames: [String] { variables.map(\.name) }

    func rawValue(of name: String) -> String? {
        variables.first { $0.name == name }?.rawValue
    }

    /// Variables whose value differs from `other` (nil → all).
    func changedVariableNames(from other: SimState?) -> Set<String> {
        guard let other else { return Set(variableNames) }
        return Set(variables.filter { other.rawValue(of: $0.name) != $0.rawValue }.map(\.name))
    }
}

/// A successor of the current state, reached by taking `actionLabel`.
struct SimSuccessor: Equatable, Identifiable {
    let actionLabel: String
    let state: SimState

    var id: String { actionLabel + "→" + state.variables.map { "\($0.name)=\($0.rawValue)" }.joined(separator: "|") }
}

/// One decomposed disjunct of the user's next-state relation.
struct SimActionDefinition: Equatable {
    /// Display label, e.g. `Inc` or `\E p \in Procs: Step(p)`.
    let label: String
    /// Verbatim source text of the disjunct (may span multiple lines).
    let expression: String
}

/// Result of one TLC expansion run: origin states (depth 0) and, per origin,
/// the outgoing transitions (depth 1).
struct SimExpansion: Equatable {
    let origins: [SimState]
    let successors: [SimSuccessor]
    /// True when the parser hit its cap and dropped states.
    let truncated: Bool
}

// MARK: - Spec Context

/// Immutable snapshot of everything the simulator needs to run TLC against the
/// user's spec. Built once when a session starts; document edits don't affect
/// a running session until it is restarted.
struct SimulationSpecContext {
    /// The user's module name (the generated module `EXTENDS` it).
    let userModuleName: String
    /// Module search path (spec directory, configured libraries, …) passed to
    /// TLC via `-DTLA-Library`.
    let searchPaths: [URL]
    /// Resolved model configuration — supplies CONSTANT definitions and the
    /// INIT/NEXT operator names.
    let config: ModelConfig
    /// Decomposed next-state actions, or nil to treat Next as a single action.
    let actions: [SimActionDefinition]?
}

// MARK: - Errors

enum SimulationError: LocalizedError, Equatable {
    case toolchainMissing
    case invalidExpression(String)
    case tlcFailed(String)
    case noStates
    case cancelled

    var errorDescription: String? {
        switch self {
        case .toolchainMissing:
            return "TLC not found. Bundle tlc-native or install tla2tools.jar with Java."
        case .invalidExpression(let reason):
            return reason
        case .tlcFailed(let message):
            return message
        case .noStates:
            return "TLC produced no states. Check that the Init predicate is satisfiable."
        case .cancelled:
            return "Cancelled"
        }
    }
}
