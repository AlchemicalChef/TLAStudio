import XCTest
@testable import TLAStudioApp

/// End-to-end tests that run the real TLC toolchain (native binary or jar).
/// Skipped when neither is available.
final class SimulationIntegrationTests: TempDirectoryTestCase {

    private func skipUnlessToolchainAvailable() throws {
        let hasNative = BinaryDiscovery.find(named: "tlc-native") != nil
            || BinaryDiscovery.find(named: "tlc-native-fast") != nil
        let hasJVM = JavaProcessRunner.findTLA2Tools() != nil && JavaProcessRunner.findJava() != nil
        guard hasNative || hasJVM else {
            throw XCTSkip("No TLC toolchain available")
        }
    }

    private func writeProbeSpec() throws -> URL {
        let spec = """
        ---- MODULE Probe ----
        EXTENDS Naturals, Sequences
        VARIABLES x, y
        Init == x = 0 /\\ y = <<>>
        Inc == x < 3 /\\ x' = x + 1 /\\ y' = y
        Push == Len(y) < 2 /\\ x' = x /\\ y' = Append(y, x)
        Next == Inc \\/ Push
        ====
        """
        let url = tempDirectory.appendingPathComponent("Probe.tla")
        try spec.write(to: url, atomically: true, encoding: .utf8)
        return url
    }

    private func makeContext(specURL: URL, actions: [SimActionDefinition]?) -> SimulationSpecContext {
        SimulationSpecContext(
            userModuleName: "Probe",
            searchPaths: [specURL.deletingLastPathComponent()],
            config: ModelConfig(name: "Test", specFile: URL(fileURLWithPath: "/tmp/Probe.tla")),
            actions: actions
        )
    }

    func testInitialStatesExpandAndStep() async throws {
        try skipUnlessToolchainAvailable()
        let specURL = try writeProbeSpec()
        let actions = [
            SimActionDefinition(label: "Inc", expression: "Inc"),
            SimActionDefinition(label: "Push", expression: "Push")
        ]
        let context = makeContext(specURL: specURL, actions: actions)

        // Initial states: exactly one (x = 0, y = <<>>).
        let initial = await SimulationRunner.shared.enumerateInitialStates(context: context)
        guard case .success(let initExpansion) = initial else {
            return XCTFail("Initial-state enumeration failed: \(initial)")
        }
        XCTAssertEqual(initExpansion.origins.count, 1)
        let s0 = initExpansion.origins[0]
        XCTAssertEqual(s0.rawValue(of: "x"), "0")
        XCTAssertEqual(s0.rawValue(of: "y"), "<<>>")

        // Expansion: Inc and Push both enabled, correctly labeled.
        let expansion = await SimulationRunner.shared.expand(s0, context: context)
        guard case .success(let expanded) = expansion else {
            return XCTFail("Expansion failed: \(expansion)")
        }
        XCTAssertEqual(expanded.successors.count, 2)
        let byAction = Dictionary(grouping: expanded.successors, by: \.actionLabel)
        XCTAssertEqual(byAction["Inc"]?.first?.state.rawValue(of: "x"), "1")
        XCTAssertEqual(byAction["Push"]?.first?.state.rawValue(of: "y"), "<<0>>")

        // Step once more from the Push successor — raw values round-trip.
        let s1 = try XCTUnwrap(byAction["Push"]?.first?.state)
        let second = await SimulationRunner.shared.expand(s1, context: context)
        guard case .success(let secondExpansion) = second else {
            return XCTFail("Second expansion failed: \(second)")
        }
        XCTAssertFalse(secondExpansion.successors.isEmpty)
    }

    func testExpansionFallsBackWhenDecompositionIsBroken() async throws {
        try skipUnlessToolchainAvailable()
        let specURL = try writeProbeSpec()
        // Deliberately broken decomposition (unbalanced parenthesis) — the
        // runner must fall back to single-action Next and still succeed.
        let context = makeContext(specURL: specURL, actions: [
            SimActionDefinition(label: "broken", expression: "Inc ("),
            SimActionDefinition(label: "Push", expression: "Push")
        ])
        let s0 = SimState(variables: [
            SimVariable(name: "x", rawValue: "0"),
            SimVariable(name: "y", rawValue: "<<>>")
        ])

        let result = await SimulationRunner.shared.expand(s0, context: context)
        guard case .success(let expansion) = result else {
            return XCTFail("Fallback expansion failed: \(result)")
        }
        XCTAssertEqual(expansion.successors.count, 2)
        XCTAssertTrue(expansion.successors.allSatisfy { $0.actionLabel == "Next" })
    }

    func testEvaluateExpressionInState() async throws {
        try skipUnlessToolchainAvailable()
        let specURL = try writeProbeSpec()
        let context = makeContext(specURL: specURL, actions: nil)
        let state = SimState(variables: [
            SimVariable(name: "x", rawValue: "2"),
            SimVariable(name: "y", rawValue: "<<0, 1>>")
        ])

        let good = await SimulationRunner.shared.evaluate("x * 10 + Len(y)", in: state, context: context)
        XCTAssertEqual(good, .success("22"))

        let enabled = await SimulationRunner.shared.evaluate("x < 3", in: state, context: context)
        XCTAssertEqual(enabled, .success("TRUE"))

        let bad = await SimulationRunner.shared.evaluate("Head(<<>>)", in: state, context: context)
        guard case .failure(.tlcFailed(let message)) = bad else {
            return XCTFail("Expected evaluation error, got \(bad)")
        }
        XCTAssertTrue(message.contains("Head"), "unexpected message: \(message)")
    }
}
