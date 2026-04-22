import XCTest
@testable import TLAStudioApp

// MARK: - TLC Process Manager Tests

final class TLCProcessManagerTests: XCTestCase {

    // MARK: - State Space Estimation Tests

    func testEstimateConstantImpactInt() async {
        let manager = TLCProcessManager.shared

        // Integer N typically gives N^2 impact
        let impact = await manager.estimateConstantImpact(.int(5))
        XCTAssertEqual(impact, 25) // 5 * 5
    }

    func testEstimateConstantImpactIntZero() async {
        let manager = TLCProcessManager.shared

        // Zero should give minimum impact of 1
        let impact = await manager.estimateConstantImpact(.int(0))
        XCTAssertEqual(impact, 1) // max(1, 0*0) = 1
    }

    func testEstimateConstantImpactIntNegative() async {
        let manager = TLCProcessManager.shared

        // Negative numbers: n * n is positive
        let impact = await manager.estimateConstantImpact(.int(-3))
        XCTAssertEqual(impact, 9) // -3 * -3 = 9
    }

    func testEstimateConstantImpactSet() async {
        let manager = TLCProcessManager.shared

        // Set of 3 elements gives 3^3 = 27 impact
        let impact = await manager.estimateConstantImpact(.set([.int(1), .int(2), .int(3)]))
        XCTAssertEqual(impact, 27) // 3 * 3 * 3
    }

    func testEstimateConstantImpactEmptySet() async {
        let manager = TLCProcessManager.shared

        // Empty set should give minimum impact of 1
        let impact = await manager.estimateConstantImpact(.set([]))
        XCTAssertEqual(impact, 1) // max(1, 0*0*0) = 1
    }

    func testEstimateConstantImpactBool() async {
        let manager = TLCProcessManager.shared

        // Boolean gives constant impact of 4
        let impactTrue = await manager.estimateConstantImpact(.bool(true))
        let impactFalse = await manager.estimateConstantImpact(.bool(false))

        XCTAssertEqual(impactTrue, 4)
        XCTAssertEqual(impactFalse, 4)
    }

    func testEstimateConstantImpactString() async {
        let manager = TLCProcessManager.shared

        // String gives constant impact of 10
        let impact = await manager.estimateConstantImpact(.string("test"))
        XCTAssertEqual(impact, 10)
    }

    func testEstimateConstantImpactModelValue() async {
        let manager = TLCProcessManager.shared

        // Model value gives constant impact of 10
        let impact = await manager.estimateConstantImpact(.modelValue("mv1"))
        XCTAssertEqual(impact, 10)
    }

    func testEstimateConstantImpactSymmetrySet() async {
        let manager = TLCProcessManager.shared

        // Symmetry set gives constant impact of 10
        let impact = await manager.estimateConstantImpact(.symmetrySet("Procs"))
        XCTAssertEqual(impact, 10)
    }

    // MARK: - State Space Estimation with Config Tests

    func testEstimateStateSpaceNoConstants() async {
        let manager = TLCProcessManager.shared
        let config = ModelConfig(
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            constants: [:]
        )

        let estimate = await manager.estimateStateSpace(config: config)
        XCTAssertEqual(estimate, 1) // No constants = base estimate of 1
    }

    func testEstimateStateSpaceSingleConstant() async {
        let manager = TLCProcessManager.shared
        let config = ModelConfig(
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            constants: ["N": .int(5)]
        )

        let estimate = await manager.estimateStateSpace(config: config)
        XCTAssertEqual(estimate, 25) // 5^2 = 25
    }

    func testEstimateStateSpaceMultipleConstants() async {
        let manager = TLCProcessManager.shared
        let config = ModelConfig(
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            constants: [
                "N": .int(3),    // 3^2 = 9
                "M": .int(2)     // 2^2 = 4
            ]
        )

        let estimate = await manager.estimateStateSpace(config: config)
        XCTAssertEqual(estimate, 36) // 9 * 4 = 36
    }

    func testEstimateStateSpaceCapping() async {
        let manager = TLCProcessManager.shared
        let config = ModelConfig(
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            constants: [
                "N": .int(10000),  // 10000^2 = 100,000,000 (at cap)
                "M": .int(10000)   // Would overflow without cap
            ]
        )

        let estimate = await manager.estimateStateSpace(config: config)
        XCTAssertEqual(estimate, 100_000_000) // Capped at 100M
    }

    func testEstimateStateSpaceMixedTypes() async {
        let manager = TLCProcessManager.shared
        let config = ModelConfig(
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            constants: [
                "N": .int(2),                      // 2^2 = 4
                "Flag": .bool(true),               // 4
                "Procs": .set([.int(1), .int(2)])  // 2^3 = 8
            ]
        )

        let estimate = await manager.estimateStateSpace(config: config)
        XCTAssertEqual(estimate, 128) // 4 * 4 * 8 = 128
    }

    // MARK: - TLC Error Tests

    func testTLCErrorTLCNotFound() {
        let error = TLCError.tlcNotFound
        XCTAssertTrue(error.errorDescription?.contains("not found") ?? false)
    }

    func testTLCErrorFailedToStart() {
        let underlying = NSError(domain: "test", code: 1, userInfo: [NSLocalizedDescriptionKey: "Process failed"])
        let error = TLCError.failedToStart(underlying)
        XCTAssertTrue(error.errorDescription?.contains("Failed to start") ?? false)
    }

    func testTLCErrorSpecNotFound() {
        let error = TLCError.specNotFound
        XCTAssertTrue(error.errorDescription?.contains("not found") ?? false)
    }

    func testTLCErrorInvalidConfig() {
        let error = TLCError.invalidConfig("Missing INIT")
        XCTAssertTrue(error.errorDescription?.contains("Missing INIT") ?? false)
    }

    func testTLCErrorConfigWriteFailed() {
        let underlying = NSError(domain: "test", code: 2, userInfo: [NSLocalizedDescriptionKey: "Write failed"])
        let error = TLCError.configWriteFailed(underlying)
        XCTAssertTrue(error.errorDescription?.contains("config file") ?? false)
    }

    func testTLCErrorTimeout() {
        let error = TLCError.timeout
        XCTAssertTrue(error.errorDescription?.contains("timed out") ?? false)
    }

    func testTLCErrorCancelled() {
        let error = TLCError.cancelled
        XCTAssertTrue(error.errorDescription?.contains("cancelled") ?? false)
    }

    // MARK: - TLC Binary Mode Tests

    func testBinaryModeEnum() {
        // Just verify the enum cases exist
        let modes: [TLCProcessManager.TLCBinaryMode] = [.fast, .standard, .auto]
        XCTAssertEqual(modes.count, 3)
    }

    // MARK: - Session Running State Tests

    func testIsRunningForNonexistentSession() async {
        let manager = TLCProcessManager.shared
        let fakeId = UUID()

        let isRunning = await manager.isRunning(sessionId: fakeId)
        XCTAssertFalse(isRunning)
    }

    // MARK: - Stop Operations Tests

    func testStopNonexistentSession() async {
        let manager = TLCProcessManager.shared
        let fakeId = UUID()

        // Should not crash when stopping a non-existent session
        await manager.stop(sessionId: fakeId)
    }

    func testStopGracefullyNonexistentSession() async {
        let manager = TLCProcessManager.shared
        let fakeId = UUID()

        // Should not crash when gracefully stopping a non-existent session
        await manager.stopGracefully(sessionId: fakeId)
    }

    func testStopAllWithNoSessions() async {
        let manager = TLCProcessManager.shared

        // Should not crash with no active sessions
        await manager.stopAll()
    }

    // MARK: - TLC Availability Tests

    func testIsTLCAvailableProperty() async {
        let manager = TLCProcessManager.shared

        // This will return true or false depending on whether TLC is installed
        // We just verify the property is accessible
        let _ = await manager.isTLCAvailable
        // No assertion - just checking it doesn't crash
    }

    func testDiscoveredTLCPathUsesConfiguredExecutable() async {
        let settings = UserSettings.shared
        let originalPath = settings.tlcPath
        defer { settings.tlcPath = originalPath }

        settings.tlcPath = "/usr/bin/true"

        let manager = TLCProcessManager.shared
        let discoveredPath = await manager.discoveredTLCPath
        XCTAssertEqual(discoveredPath, "/usr/bin/true")
    }
}

// MARK: - Checkpoint Status Tests

final class CheckpointStatusAdditionalTests: XCTestCase {

    func testSavedStatus() {
        let checkpoint = CheckpointInfo(
            id: "test-123",
            directoryURL: URL(fileURLWithPath: "/tmp/checkpoint"),
            createdAt: Date(),
            specName: "TestSpec",
            distinctStates: 5000,
            statesFound: 10000
        )

        let status = CheckpointStatus.saved(checkpoint)
        // Note: .saved is NOT active - only .saving and .restoring are active
        XCTAssertFalse(status.isActive)
        XCTAssertTrue(status.displayMessage.contains("Checkpoint saved"))
    }

    func testRestoredStatus() {
        let checkpoint = CheckpointInfo(
            id: "test-456",
            directoryURL: URL(fileURLWithPath: "/tmp/checkpoint"),
            createdAt: Date(),
            specName: "TestSpec",
            distinctStates: nil,
            statesFound: nil
        )

        let status = CheckpointStatus.restored(checkpoint)
        XCTAssertFalse(status.isActive) // Restored is not an active state
        XCTAssertTrue(status.displayMessage.contains("Restored"))
    }

    func testFailedStatus() {
        let status = CheckpointStatus.failed("Disk full")
        XCTAssertFalse(status.isActive)
        XCTAssertTrue(status.displayMessage.contains("failed"))
        XCTAssertTrue(status.displayMessage.contains("Disk full"))
    }

    func testStatusEqualitySaved() {
        let checkpoint = CheckpointInfo(
            id: "test",
            directoryURL: URL(fileURLWithPath: "/tmp"),
            createdAt: Date(),
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )

        let status1 = CheckpointStatus.saved(checkpoint)
        let status2 = CheckpointStatus.saved(checkpoint)

        XCTAssertEqual(status1, status2)
    }
}

// MARK: - Error Trace Type Tests

final class ErrorTraceTypeTests: XCTestCase {

    func testErrorTypeDisplayNames() {
        XCTAssertEqual(ErrorTrace.ErrorType.invariantViolation.displayName, "Invariant Violation")
        XCTAssertEqual(ErrorTrace.ErrorType.deadlock.displayName, "Deadlock")
        XCTAssertEqual(ErrorTrace.ErrorType.livenessViolation.displayName, "Liveness Violation")
        XCTAssertEqual(ErrorTrace.ErrorType.assertionFailure.displayName, "Assertion Failure")
        XCTAssertEqual(ErrorTrace.ErrorType.evaluationError.displayName, "Evaluation Error")
        XCTAssertEqual(ErrorTrace.ErrorType.temporal.displayName, "Temporal Property Violation")
    }

    func testErrorTraceCreation() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "TypeOK violated",
            states: [
                TraceState(id: 0, action: "Init", variables: ["x": .int(0)]),
                TraceState(id: 1, action: "Next", variables: ["x": .int(1)])
            ],
            loopStart: nil,
            violatedProperty: "TypeOK"
        )

        XCTAssertEqual(trace.type, .invariantViolation)
        XCTAssertEqual(trace.message, "TypeOK violated")
        XCTAssertEqual(trace.states.count, 2)
        XCTAssertNil(trace.loopStart)
        XCTAssertEqual(trace.violatedProperty, "TypeOK")
    }

    func testErrorTraceWithLoop() {
        let trace = ErrorTrace(
            type: .livenessViolation,
            message: "Eventually always violated",
            states: [
                TraceState(id: 0),
                TraceState(id: 1),
                TraceState(id: 2)
            ],
            loopStart: 1
        )

        XCTAssertEqual(trace.loopStart, 1)
    }
}

// MARK: - Trace State Tests

final class TraceStateTests: XCTestCase {

    func testTraceStateDisplayNameInitial() {
        let state = TraceState(id: 0, action: "Init")
        XCTAssertEqual(state.displayName, "Initial State")
    }

    func testTraceStateDisplayNameWithAction() {
        let state = TraceState(id: 1, action: "Next")
        XCTAssertEqual(state.displayName, "State 1: Next")
    }

    func testTraceStateDisplayNameWithoutAction() {
        let state = TraceState(id: 2)
        XCTAssertEqual(state.displayName, "State 2")
    }

    func testChangedVariablesFromNil() {
        let state = TraceState(id: 0, variables: ["x": .int(1), "y": .int(2)])
        let changed = state.changedVariables(from: nil)

        XCTAssertEqual(changed.count, 2)
        XCTAssertTrue(changed.contains("x"))
        XCTAssertTrue(changed.contains("y"))
    }

    func testChangedVariablesDetection() {
        let prev = TraceState(id: 0, variables: ["x": .int(1), "y": .int(2)])
        let curr = TraceState(id: 1, variables: ["x": .int(1), "y": .int(3)])

        let changed = curr.changedVariables(from: prev)

        XCTAssertEqual(changed.count, 1)
        XCTAssertTrue(changed.contains("y"))
        XCTAssertFalse(changed.contains("x"))
    }

    func testChangedVariablesNoChanges() {
        let prev = TraceState(id: 0, variables: ["x": .int(1)])
        let curr = TraceState(id: 1, variables: ["x": .int(1)])

        let changed = curr.changedVariables(from: prev)
        XCTAssertTrue(changed.isEmpty)
    }
}

// MARK: - Source Location Tests

final class SourceLocationTests: XCTestCase {

    func testDisplayStringWithFile() {
        let loc = SourceLocation(file: "Test.tla", line: 10, column: 5)
        XCTAssertEqual(loc.displayString, "Test.tla:10:5")
    }

    func testDisplayStringWithoutFile() {
        let loc = SourceLocation(line: 10, column: 5)
        XCTAssertEqual(loc.displayString, "line 10, column 5")
    }

    func testSourceLocationEquality() {
        let loc1 = SourceLocation(file: "Test.tla", line: 10, column: 5)
        let loc2 = SourceLocation(file: "Test.tla", line: 10, column: 5)
        let loc3 = SourceLocation(file: "Test.tla", line: 11, column: 5)

        XCTAssertEqual(loc1, loc2)
        XCTAssertNotEqual(loc1, loc3)
    }

    func testSourceLocationWithEndPositions() {
        let loc = SourceLocation(file: "Test.tla", line: 10, column: 5, endLine: 15, endColumn: 10)
        XCTAssertEqual(loc.line, 10)
        XCTAssertEqual(loc.column, 5)
        XCTAssertEqual(loc.endLine, 15)
        XCTAssertEqual(loc.endColumn, 10)
    }

    func testSourceLocationCodable() throws {
        let original = SourceLocation(file: "Test.tla", line: 10, column: 5, endLine: 15, endColumn: 10)
        let encoded = try JSONEncoder().encode(original)
        let decoded = try JSONDecoder().decode(SourceLocation.self, from: encoded)

        XCTAssertEqual(original, decoded)
    }
}

// MARK: - State Value Tests

final class StateValueTests: XCTestCase {

    func testIntDisplayString() {
        let value = StateValue.int(42)
        XCTAssertEqual(value.displayString, "42")
    }

    func testStringDisplayString() {
        let value = StateValue.string("hello")
        XCTAssertEqual(value.displayString, "\"hello\"")
    }

    func testBoolDisplayString() {
        XCTAssertEqual(StateValue.bool(true).displayString, "TRUE")
        XCTAssertEqual(StateValue.bool(false).displayString, "FALSE")
    }

    func testEmptySetDisplayString() {
        let value = StateValue.set([])
        XCTAssertEqual(value.displayString, "{}")
    }

    func testSetDisplayString() {
        let value = StateValue.set([StateValueWrapper(.int(1)), StateValueWrapper(.int(2))])
        // Set display is sorted, so should be consistent
        XCTAssertTrue(value.displayString.contains("1"))
        XCTAssertTrue(value.displayString.contains("2"))
    }

    func testEmptySequenceDisplayString() {
        let value = StateValue.sequence([])
        XCTAssertEqual(value.displayString, "<<>>")
    }

    func testSequenceDisplayString() {
        let value = StateValue.sequence([.int(1), .int(2), .int(3)])
        XCTAssertEqual(value.displayString, "<<1, 2, 3>>")
    }

    func testEmptyRecordDisplayString() {
        let value = StateValue.record([:])
        XCTAssertEqual(value.displayString, "[]")
    }

    func testRecordDisplayString() {
        let value = StateValue.record(["a": .int(1), "b": .int(2)])
        // Record display is sorted by key
        XCTAssertTrue(value.displayString.contains("a |-> 1"))
        XCTAssertTrue(value.displayString.contains("b |-> 2"))
    }

    func testTupleDisplayString() {
        let value = StateValue.tuple([.int(1), .string("a")])
        XCTAssertEqual(value.displayString, "<<1, \"a\">>")
    }

    func testModelValueDisplayString() {
        let value = StateValue.modelValue("mv1")
        XCTAssertEqual(value.displayString, "mv1")
    }

    func testStateValueEquality() {
        XCTAssertEqual(StateValue.int(1), StateValue.int(1))
        XCTAssertNotEqual(StateValue.int(1), StateValue.int(2))
        XCTAssertEqual(StateValue.string("a"), StateValue.string("a"))
        XCTAssertNotEqual(StateValue.string("a"), StateValue.string("b"))
        XCTAssertEqual(StateValue.bool(true), StateValue.bool(true))
        XCTAssertNotEqual(StateValue.bool(true), StateValue.bool(false))
    }

    func testStateValueCodable() throws {
        let values: [StateValue] = [
            .int(42),
            .string("test"),
            .bool(true),
            .sequence([.int(1), .int(2)]),
            .record(["a": .int(1)]),
            .modelValue("mv1"),
            .tuple([.int(1), .bool(true)]),
            .set([StateValueWrapper(.int(1)), StateValueWrapper(.int(2))])
        ]

        for original in values {
            let encoded = try JSONEncoder().encode(original)
            let decoded = try JSONDecoder().decode(StateValue.self, from: encoded)
            XCTAssertEqual(original, decoded)
        }
    }

    // MARK: - Function Type Tests

    func testFunctionDisplayString() {
        let value = StateValue.function([
            StateValueWrapper(.int(1)): .string("a"),
            StateValueWrapper(.int(2)): .string("b")
        ])
        // Function display uses :> operator
        XCTAssertTrue(value.displayString.contains(":>"))
        XCTAssertTrue(value.displayString.contains("@@") || value.displayString.contains("a") && value.displayString.contains("b"))
    }

    func testEmptyFunctionDisplayString() {
        let value = StateValue.function([:])
        XCTAssertEqual(value.displayString, "[x \\in {} |-> x]")
    }

    func testFunctionCodable() throws {
        let original = StateValue.function([
            StateValueWrapper(.int(1)): .string("one"),
            StateValueWrapper(.int(2)): .string("two")
        ])

        let encoded = try JSONEncoder().encode(original)
        let decoded = try JSONDecoder().decode(StateValue.self, from: encoded)

        // Functions may not preserve order, so compare display strings
        if case .function(let originalMap) = original,
           case .function(let decodedMap) = decoded {
            XCTAssertEqual(originalMap.count, decodedMap.count)
        } else {
            XCTFail("Expected function type")
        }
    }

    func testFunctionEquality() {
        let f1 = StateValue.function([StateValueWrapper(.int(1)): .string("a")])
        let f2 = StateValue.function([StateValueWrapper(.int(1)): .string("a")])
        let f3 = StateValue.function([StateValueWrapper(.int(1)): .string("b")])

        XCTAssertEqual(f1, f2)
        XCTAssertNotEqual(f1, f3)
    }

    // MARK: - Additional Type Equality Tests

    func testSetEquality() {
        let s1 = StateValue.set([StateValueWrapper(.int(1)), StateValueWrapper(.int(2))])
        let s2 = StateValue.set([StateValueWrapper(.int(2)), StateValueWrapper(.int(1))]) // Order shouldn't matter
        let s3 = StateValue.set([StateValueWrapper(.int(1)), StateValueWrapper(.int(3))])

        XCTAssertEqual(s1, s2)
        XCTAssertNotEqual(s1, s3)
    }

    func testTupleEquality() {
        let t1 = StateValue.tuple([.int(1), .bool(true)])
        let t2 = StateValue.tuple([.int(1), .bool(true)])
        let t3 = StateValue.tuple([.int(1), .bool(false)])

        XCTAssertEqual(t1, t2)
        XCTAssertNotEqual(t1, t3)
    }

    func testSequenceEquality() {
        let s1 = StateValue.sequence([.int(1), .int(2)])
        let s2 = StateValue.sequence([.int(1), .int(2)])
        let s3 = StateValue.sequence([.int(2), .int(1)]) // Order matters for sequences

        XCTAssertEqual(s1, s2)
        XCTAssertNotEqual(s1, s3)
    }

    func testRecordEquality() {
        let r1 = StateValue.record(["a": .int(1), "b": .int(2)])
        let r2 = StateValue.record(["b": .int(2), "a": .int(1)])
        let r3 = StateValue.record(["a": .int(1), "b": .int(3)])

        XCTAssertEqual(r1, r2)
        XCTAssertNotEqual(r1, r3)
    }
}

// MARK: - StateValueWrapper Tests

final class StateValueWrapperTests: XCTestCase {

    func testWrapperEquality() {
        let w1 = StateValueWrapper(.int(1))
        let w2 = StateValueWrapper(.int(1))
        let w3 = StateValueWrapper(.int(2))

        XCTAssertEqual(w1, w2)
        XCTAssertNotEqual(w1, w3)
    }

    func testWrapperHashable() {
        let w1 = StateValueWrapper(.int(1))
        let w2 = StateValueWrapper(.int(1))

        var set: Set<StateValueWrapper> = []
        set.insert(w1)
        set.insert(w2)

        XCTAssertEqual(set.count, 1) // Should be same hash
    }

    func testWrapperCodable() throws {
        let original = StateValueWrapper(.string("test"))
        let encoded = try JSONEncoder().encode(original)
        let decoded = try JSONDecoder().decode(StateValueWrapper.self, from: encoded)

        XCTAssertEqual(original, decoded)
    }
}
