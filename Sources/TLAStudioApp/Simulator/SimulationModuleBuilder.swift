import Foundation

/// Builds the synthetic TLA+ module (and matching TLC config) that powers one
/// interactive-simulation step.
///
/// The technique (verified against TLC 2.20 / tlc-native): a fresh module
/// extends the user's spec, adds an auxiliary depth variable, pins INIT to a
/// concrete state (raw TLC-printed values spliced back verbatim), wraps each
/// decomposed Next-disjunct in a *named* action operator (TLC labels dot-dump
/// edges with those names), and bounds exploration with
/// `CONSTRAINT depth <= 1`. Running TLC with `-dump dot,actionlabels` then
/// yields exactly: the origin state, all of its successors, and which action
/// produced each — one short TLC run per interactive step.
enum SimulationModuleBuilder {

    static let moduleName = "TLAStudioSim"
    static let depthVariable = "tlaStudioSimDepth"
    static let initName = "TLAStudioSimInit"
    static let nextName = "TLAStudioSimNext"
    static let constraintName = "TLAStudioSimConstraint"
    static let actionNamePrefix = "TLAStudioSimAction"

    /// Markers bracketing the PrintT'd value in an evaluation run. TLC prints
    /// the string value with quotes, so the parser matches the quoted form.
    static let evalBeginMarker = "TLASTUDIO_EVAL_BEGIN"
    static let evalEndMarker = "TLASTUDIO_EVAL_END"

    // MARK: - Modules

    /// Module that enumerates the user's initial states (depth bound 0: the
    /// dot dump contains exactly the Init states).
    static func initialStatesModule(context: SimulationSpecContext) -> String {
        let initPredicate = context.config.initPredicate.isEmpty ? "Init" : context.config.initPredicate
        let nextAction = context.config.nextAction.isEmpty ? "Next" : context.config.nextAction
        return """
        ---- MODULE \(moduleName) ----
        EXTENDS \(context.userModuleName), Naturals
        VARIABLE \(depthVariable)
        \(initName) ==
            /\\ \(depthVariable) = 0
            /\\ (\(initPredicate))
        \(nextName) ==
            /\\ \(depthVariable)' = \(depthVariable) + 1
            /\\ (\(nextAction))
        \(constraintName) == \(depthVariable) <= 0
        ====
        """
    }

    /// Module that expands one concrete state: INIT pins the state, NEXT is the
    /// (decomposed) user Next, depth bound 1 keeps origin + successors only.
    ///
    /// `EXTENDS … TLC` is required because TLC prints function values with the
    /// TLC-module operators `:>` and `@@`, which must resolve when the raw
    /// values are spliced back in.
    static func expansionModule(context: SimulationSpecContext, state: SimState) -> String {
        var lines: [String] = []
        lines.append("---- MODULE \(moduleName) ----")
        lines.append("EXTENDS \(context.userModuleName), Naturals, TLC")
        lines.append("VARIABLE \(depthVariable)")
        lines.append("\(initName) ==")
        lines.append("    /\\ \(depthVariable) = 0")
        for variable in state.variables {
            lines.append("    /\\ \(variable.name) = (\(variable.rawValue))")
        }

        let actionNames: [String]
        if let actions = context.actions, !actions.isEmpty {
            actionNames = actions.indices.map { "\(actionNamePrefix)\($0 + 1)" }
            for (index, action) in actions.enumerated() {
                lines.append("\(actionNames[index]) ==")
                lines.append("    /\\ \(depthVariable)' = \(depthVariable) + 1")
                lines.append(contentsOf: embedded(expression: action.expression))
            }
        } else {
            let nextAction = context.config.nextAction.isEmpty ? "Next" : context.config.nextAction
            actionNames = ["\(actionNamePrefix)1"]
            lines.append("\(actionNames[0]) ==")
            lines.append("    /\\ \(depthVariable)' = \(depthVariable) + 1")
            lines.append("    /\\ (\(nextAction))")
        }

        lines.append("\(nextName) ==")
        for name in actionNames {
            lines.append("    \\/ \(name)")
        }
        lines.append("\(constraintName) == \(depthVariable) <= 1")
        lines.append("====")
        return lines.joined(separator: "\n")
    }

    /// Module that evaluates `expression` in the context of `state` by pinning
    /// INIT to the state and PrintT-ing the value between sentinel markers.
    static func evaluationModule(
        context: SimulationSpecContext,
        state: SimState,
        expression: String
    ) throws -> String {
        let trimmed = expression.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            throw SimulationError.invalidExpression("Expression is empty")
        }
        // "====" would terminate the generated module early.
        guard !trimmed.contains("====") else {
            throw SimulationError.invalidExpression("Expression must not contain \"====\"")
        }

        var lines: [String] = []
        lines.append("---- MODULE \(moduleName) ----")
        lines.append("EXTENDS \(context.userModuleName), Naturals, TLC")
        lines.append("\(initName) ==")
        for variable in state.variables {
            lines.append("    /\\ \(variable.name) = (\(variable.rawValue))")
        }
        lines.append("    /\\ PrintT(\"\(evalBeginMarker)\")")
        lines.append("    /\\ PrintT(")
        for line in trimmed.components(separatedBy: "\n") {
            lines.append("        \(line)")
        }
        lines.append("       )")
        lines.append("    /\\ PrintT(\"\(evalEndMarker)\")")
        let allVariables = state.variables.map(\.name).joined(separator: ", ")
        lines.append("\(nextName) ==")
        lines.append("    /\\ FALSE")
        lines.append("    /\\ UNCHANGED <<\(allVariables)>>")
        lines.append("====")
        return lines.joined(separator: "\n")
    }

    /// TLC config matching the generated module.
    static func configFile(context: SimulationSpecContext, includeConstraint: Bool) -> String {
        context.config.generateSimulationConfigFile(
            initName: initName,
            nextName: nextName,
            constraintName: includeConstraint ? constraintName : nil
        )
    }

    // MARK: - Helpers

    /// Embed a (possibly multi-line) action expression as the second conjunct
    /// of a wrapper action. The block is parenthesized and shifted uniformly to
    /// column 8 — deeper than the wrapper's own bullets at column 4 — so the
    /// expression's internal junction alignment is preserved and can never
    /// terminate the wrapper's junction list early. The closing parenthesis
    /// goes on its own line so a trailing `\*` line comment inside the
    /// expression cannot swallow it.
    private static func embedded(expression: String) -> [String] {
        let lines = expression.components(separatedBy: "\n")
        if lines.count == 1 {
            return ["    /\\ (\(lines[0]))"]
        }
        var result = ["    /\\ ("]
        for line in lines {
            result.append(line.isEmpty ? "" : "        \(line)")
        }
        result.append("       )")
        return result
    }
}
