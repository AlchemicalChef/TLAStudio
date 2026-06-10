import XCTest
@testable import TLAStudioApp

// MARK: - Mock Runner

private final class MockRunner: SimulationExpanding, @unchecked Sendable {
    private let lock = NSLock()

    var initialResult: Result<SimExpansion, SimulationError> = .failure(.noStates)
    var expansions: [SimState: Result<SimExpansion, SimulationError>] = [:]
    var evalResult: Result<String, SimulationError> = .success("TRUE")

    private(set) var expandCallCount = 0

    func enumerateInitialStates(context: SimulationSpecContext) async -> Result<SimExpansion, SimulationError> {
        lock.lock(); defer { lock.unlock() }
        return initialResult
    }

    func expand(_ state: SimState, context: SimulationSpecContext) async -> Result<SimExpansion, SimulationError> {
        lock.lock(); defer { lock.unlock() }
        expandCallCount += 1
        return expansions[state] ?? .failure(.noStates)
    }

    func evaluate(_ expression: String, in state: SimState, context: SimulationSpecContext) async -> Result<String, SimulationError> {
        lock.lock(); defer { lock.unlock() }
        return evalResult
    }
}

// MARK: - Tests

@MainActor
final class SimulationSessionTests: XCTestCase {

    private static func state(_ x: Int) -> SimState {
        SimState(variables: [SimVariable(name: "x", rawValue: "\(x)")])
    }

    private func makeContext() -> SimulationSpecContext {
        SimulationSpecContext(
            userModuleName: "M",
            searchPaths: [],
            config: ModelConfig(name: "Test", specFile: URL(fileURLWithPath: "/tmp/Probe.tla")),
            actions: nil
        )
    }

    private func waitUntil(
        timeout: TimeInterval = 2,
        _ condition: @MainActor () -> Bool
    ) async throws {
        let deadline = Date().addingTimeInterval(timeout)
        while !condition() {
            guard Date() < deadline else {
                return XCTFail("Timed out waiting for condition")
            }
            try await Task.sleep(nanoseconds: 10_000_000)
        }
    }

    func testStartWithSingleInitialStateAutoEnters() async throws {
        let s0 = Self.state(0)
        let s1 = Self.state(1)
        let mock = MockRunner()
        mock.initialResult = .success(SimExpansion(origins: [s0], successors: [], truncated: false))
        mock.expansions[s0] = .success(SimExpansion(
            origins: [s0],
            successors: [SimSuccessor(actionLabel: "Inc", state: s1)],
            truncated: false
        ))

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        try await waitUntil { session.phase == .ready }

        XCTAssertEqual(session.trace.count, 1)
        XCTAssertEqual(session.currentState, s0)
        XCTAssertEqual(session.successors.map(\.actionLabel), ["Inc"])
    }

    func testStartWithMultipleInitialStatesAsksForChoice() async throws {
        let mock = MockRunner()
        mock.initialResult = .success(SimExpansion(
            origins: [Self.state(0), Self.state(1)], successors: [], truncated: false
        ))
        mock.expansions[Self.state(1)] = .success(SimExpansion(
            origins: [Self.state(1)], successors: [], truncated: false
        ))

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        try await waitUntil { session.phase == .choosingInitialState }
        XCTAssertEqual(session.initialStates.count, 2)
        XCTAssertNil(session.currentState)

        session.chooseInitialState(Self.state(1))
        try await waitUntil { session.phase == .ready }
        XCTAssertEqual(session.currentState, Self.state(1))
    }

    func testStepAndStepBackUsesExpansionCache() async throws {
        let s0 = Self.state(0)
        let s1 = Self.state(1)
        let mock = MockRunner()
        let step01 = SimSuccessor(actionLabel: "Inc", state: s1)
        mock.initialResult = .success(SimExpansion(origins: [s0], successors: [], truncated: false))
        mock.expansions[s0] = .success(SimExpansion(origins: [s0], successors: [step01], truncated: false))
        mock.expansions[s1] = .success(SimExpansion(origins: [s1], successors: [], truncated: false))

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        try await waitUntil { session.phase == .ready }

        session.step(step01)
        try await waitUntil { session.phase == .ready && session.trace.count == 2 }
        XCTAssertEqual(session.currentState, s1)
        XCTAssertEqual(session.trace.last?.actionLabel, "Inc")
        XCTAssertEqual(mock.expandCallCount, 2)

        session.stepBack()
        try await waitUntil { session.phase == .ready && session.trace.count == 1 }
        XCTAssertEqual(session.currentState, s0)
        XCTAssertEqual(session.successors, [step01])
        // s0's expansion came from the cache — no third TLC run.
        XCTAssertEqual(mock.expandCallCount, 2)
    }

    func testStepIgnoresUnknownSuccessor() async throws {
        let s0 = Self.state(0)
        let mock = MockRunner()
        mock.initialResult = .success(SimExpansion(origins: [s0], successors: [], truncated: false))
        mock.expansions[s0] = .success(SimExpansion(origins: [s0], successors: [], truncated: false))

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        try await waitUntil { session.phase == .ready }

        session.step(SimSuccessor(actionLabel: "Bogus", state: Self.state(9)))
        XCTAssertEqual(session.trace.count, 1)
    }

    func testResetReturnsToInitialState() async throws {
        let s0 = Self.state(0)
        let s1 = Self.state(1)
        let step01 = SimSuccessor(actionLabel: "Inc", state: s1)
        let mock = MockRunner()
        mock.initialResult = .success(SimExpansion(origins: [s0], successors: [], truncated: false))
        mock.expansions[s0] = .success(SimExpansion(origins: [s0], successors: [step01], truncated: false))
        mock.expansions[s1] = .success(SimExpansion(origins: [s1], successors: [], truncated: false))

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        try await waitUntil { session.phase == .ready }
        session.step(step01)
        try await waitUntil { session.trace.count == 2 }

        session.reset()
        try await waitUntil { session.phase == .ready && session.trace.count == 1 }
        XCTAssertEqual(session.currentState, s0)
    }

    func testFailureSurfacesInPhase() async throws {
        let mock = MockRunner()
        mock.initialResult = .failure(.tlcFailed("Error: boom"))

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        try await waitUntil {
            if case .failed = session.phase { return true }
            return false
        }
        XCTAssertEqual(session.phase, .failed("Error: boom"))
    }

    func testEvaluateRecordsHistory() async throws {
        let s0 = Self.state(0)
        let mock = MockRunner()
        mock.initialResult = .success(SimExpansion(origins: [s0], successors: [], truncated: false))
        mock.expansions[s0] = .success(SimExpansion(origins: [s0], successors: [], truncated: false))
        mock.evalResult = .success("42")

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        try await waitUntil { session.phase == .ready }

        session.evaluate("x + 42")
        try await waitUntil { !session.evaluations.isEmpty }

        XCTAssertEqual(session.evaluations[0].expression, "x + 42")
        XCTAssertEqual(session.evaluations[0].result, .success("42"))
        XCTAssertEqual(session.evaluations[0].stateIndex, 0)
    }

    func testInvalidateDropsLateResults() async throws {
        let s0 = Self.state(0)
        let mock = MockRunner()
        mock.initialResult = .success(SimExpansion(origins: [s0], successors: [], truncated: false))
        mock.expansions[s0] = .success(SimExpansion(origins: [s0], successors: [], truncated: false))

        let session = SimulationSession(context: makeContext(), runner: mock)
        session.start()
        session.invalidate()

        // Give the in-flight task time to (not) commit.
        try await Task.sleep(nanoseconds: 100_000_000)
        XCTAssertEqual(session.phase, .loadingInitialStates)
        XCTAssertTrue(session.trace.isEmpty)
    }
}
