import XCTest
@testable import TLAStudioApp

final class SimulationModuleBuilderTests: XCTestCase {

    private func makeContext(
        actions: [SimActionDefinition]? = nil,
        constants: [String: ConstantValue] = [:]
    ) -> SimulationSpecContext {
        var config = ModelConfig(name: "Test", specFile: URL(fileURLWithPath: "/tmp/Probe.tla"))
        config.constants = constants
        return SimulationSpecContext(
            userModuleName: "Probe",
            searchPaths: [],
            config: config,
            actions: actions
        )
    }

    private let state = SimState(variables: [
        SimVariable(name: "x", rawValue: "1"),
        SimVariable(name: "y", rawValue: "<<0>>")
    ])

    // MARK: - Initial-states module

    func testInitialStatesModule() {
        let module = SimulationModuleBuilder.initialStatesModule(context: makeContext())
        XCTAssertTrue(module.contains("---- MODULE TLAStudioSim ----"))
        XCTAssertTrue(module.contains("EXTENDS Probe, Naturals"))
        XCTAssertTrue(module.contains("VARIABLE tlaStudioSimDepth"))
        XCTAssertTrue(module.contains("/\\ (Init)"))
        XCTAssertTrue(module.contains("/\\ (Next)"))
        XCTAssertTrue(module.contains("TLAStudioSimConstraint == tlaStudioSimDepth <= 0"))
        XCTAssertTrue(module.hasSuffix("===="))
    }

    // MARK: - Expansion module

    func testExpansionModulePinsStateAndWrapsActions() {
        let actions = [
            SimActionDefinition(label: "Inc", expression: "Inc"),
            SimActionDefinition(label: "Push", expression: "Push")
        ]
        let module = SimulationModuleBuilder.expansionModule(
            context: makeContext(actions: actions), state: state
        )

        XCTAssertTrue(module.contains("EXTENDS Probe, Naturals, TLC"))
        XCTAssertTrue(module.contains("/\\ x = (1)"))
        XCTAssertTrue(module.contains("/\\ y = (<<0>>)"))
        XCTAssertTrue(module.contains("TLAStudioSimAction1 =="))
        XCTAssertTrue(module.contains("TLAStudioSimAction2 =="))
        XCTAssertTrue(module.contains("/\\ (Inc)"))
        XCTAssertTrue(module.contains("/\\ (Push)"))
        XCTAssertTrue(module.contains("\\/ TLAStudioSimAction1"))
        XCTAssertTrue(module.contains("\\/ TLAStudioSimAction2"))
        XCTAssertTrue(module.contains("TLAStudioSimConstraint == tlaStudioSimDepth <= 1"))
    }

    func testExpansionModuleWithoutDecompositionWrapsNext() {
        let module = SimulationModuleBuilder.expansionModule(
            context: makeContext(actions: nil), state: state
        )
        XCTAssertTrue(module.contains("TLAStudioSimAction1 =="))
        XCTAssertTrue(module.contains("/\\ (Next)"))
        XCTAssertFalse(module.contains("TLAStudioSimAction2"))
    }

    func testExpansionModuleEmbedsMultiLineActionWithUniformShift() {
        let actions = [
            SimActionDefinition(label: "guarded", expression: "/\\ g\n/\\ h"),
            SimActionDefinition(label: "B", expression: "B")
        ]
        let module = SimulationModuleBuilder.expansionModule(
            context: makeContext(actions: actions), state: state
        )
        // Both bullets of the embedded block must land at the same column,
        // deeper than the wrapper's own bullets, with the closing parenthesis
        // on its own line.
        XCTAssertTrue(module.contains("    /\\ (\n        /\\ g\n        /\\ h\n       )"))
    }

    // MARK: - Evaluation module

    func testEvaluationModule() throws {
        let module = try SimulationModuleBuilder.evaluationModule(
            context: makeContext(), state: state, expression: "x + Len(y)"
        )
        XCTAssertTrue(module.contains("EXTENDS Probe, Naturals, TLC"))
        XCTAssertTrue(module.contains("/\\ PrintT(\"TLASTUDIO_EVAL_BEGIN\")"))
        XCTAssertTrue(module.contains("x + Len(y)"))
        XCTAssertTrue(module.contains("/\\ PrintT(\"TLASTUDIO_EVAL_END\")"))
        XCTAssertTrue(module.contains("UNCHANGED <<x, y>>"))
        XCTAssertFalse(module.contains("VARIABLE tlaStudioSimDepth"))
    }

    func testEvaluationModuleRejectsModuleTerminator() {
        XCTAssertThrowsError(try SimulationModuleBuilder.evaluationModule(
            context: makeContext(), state: state, expression: "x ==== y"
        )) { error in
            XCTAssertEqual(error as? SimulationError,
                           .invalidExpression("Expression must not contain \"====\""))
        }
    }

    func testEvaluationModuleRejectsEmptyExpression() {
        XCTAssertThrowsError(try SimulationModuleBuilder.evaluationModule(
            context: makeContext(), state: state, expression: "   "
        ))
    }

    // MARK: - Config

    func testSimulationConfigCarriesConstantsButNotInvariants() {
        var config = ModelConfig(name: "Test", specFile: URL(fileURLWithPath: "/tmp/Probe.tla"))
        config.constants = ["N": .int(3), "Procs": .modelValue("p1")]
        config.invariants = ["TypeOK"]
        config.temporalProperties = ["Liveness"]
        config.stateConstraint = "x < 10"

        let cfg = config.generateSimulationConfigFile(
            initName: "TLAStudioSimInit",
            nextName: "TLAStudioSimNext",
            constraintName: "TLAStudioSimConstraint"
        )

        XCTAssertTrue(cfg.contains("INIT TLAStudioSimInit"))
        XCTAssertTrue(cfg.contains("NEXT TLAStudioSimNext"))
        XCTAssertTrue(cfg.contains("CONSTRAINT TLAStudioSimConstraint"))
        XCTAssertTrue(cfg.contains("CONSTANT N = 3"))
        XCTAssertFalse(cfg.contains("INVARIANT"))
        XCTAssertFalse(cfg.contains("PROPERTY"))
        XCTAssertFalse(cfg.contains("x < 10"))
    }

    func testSimulationConfigOmitsConstraintWhenNil() {
        let cfg = ModelConfig(name: "Test", specFile: URL(fileURLWithPath: "/tmp/Probe.tla")).generateSimulationConfigFile(
            initName: "I", nextName: "N", constraintName: nil
        )
        XCTAssertFalse(cfg.contains("CONSTRAINT"))
    }
}
