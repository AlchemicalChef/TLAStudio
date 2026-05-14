import XCTest
@testable import TLAStudioApp

// MARK: - Trace Storage Manager Tests

final class TraceStorageManagerTests: XCTestCase {

    var manager: TraceStorageManager!

    override func setUp() {
        super.setUp()
        manager = TraceStorageManager.shared
    }

    override func tearDown() async throws {
        // Clean up any test traces
        try await super.tearDown()
    }

    // MARK: - Basic Trace Lifecycle Tests

    func testBeginAndFinalizeTrace() async throws {
        let sessionId = UUID()

        // Begin trace
        let writer = try await manager.beginTrace(sessionId: sessionId)
        XCTAssertEqual(writer.sessionId, sessionId)
        XCTAssertEqual(writer.count, 0)

        // Add some states
        let state1 = TraceState(id: 0, action: "Init", variables: ["x": .int(0)])
        let state2 = TraceState(id: 1, action: "Next", variables: ["x": .int(1)])

        try await writer.append(state1)
        try await writer.append(state2)
        XCTAssertEqual(writer.count, 2)

        // Finalize trace
        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test error",
            loopStart: nil,
            violatedProperty: "TypeOK"
        )

        XCTAssertEqual(lazyTrace.stateCount, 2)
        XCTAssertEqual(lazyTrace.type, .invariantViolation)
        XCTAssertEqual(lazyTrace.message, "Test error")
        XCTAssertEqual(lazyTrace.violatedProperty, "TypeOK")
        XCTAssertTrue(lazyTrace.isStoredOnDisk)

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    func testAppendMultipleStates() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        // Append 50 states
        for i in 0..<50 {
            let state = TraceState(id: i, action: "Step\(i)", variables: ["counter": .int(i)])
            try await writer.append(state)
        }

        XCTAssertEqual(writer.count, 50)

        // Finalize and verify
        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .deadlock,
            message: "Deadlock",
            loopStart: nil,
            violatedProperty: nil
        )

        XCTAssertEqual(lazyTrace.stateCount, 50)

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    // MARK: - State Loading Tests

    func testLoadStateByIndex() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        // Create states with distinct values
        for i in 0..<10 {
            let state = TraceState(
                id: i,
                action: "Action\(i)",
                variables: ["value": .int(i * 10)]
            )
            try await writer.append(state)
        }

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Load specific states
        let state0 = try await lazyTrace.loadState(at: 0)
        XCTAssertEqual(state0.id, 0)
        XCTAssertEqual(state0.action, "Action0")
        XCTAssertEqual(state0.variables["value"], .int(0))

        let state5 = try await lazyTrace.loadState(at: 5)
        XCTAssertEqual(state5.id, 5)
        XCTAssertEqual(state5.variables["value"], .int(50))

        let state9 = try await lazyTrace.loadState(at: 9)
        XCTAssertEqual(state9.id, 9)
        XCTAssertEqual(state9.variables["value"], .int(90))

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    func testLoadPage() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        // Create 150 states (spans multiple pages with default page size of 100)
        for i in 0..<150 {
            let state = TraceState(id: i, action: "Step", variables: ["i": .int(i)])
            try await writer.append(state)
        }

        // Keep a strong reference to the returned trace: LazyErrorTrace.deinit schedules
        // a detached cleanup Task that removes `traceFiles[sessionId]`, racing subsequent
        // loadPage calls if the trace is released immediately.
        let trace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Load first page
        let page0 = try await manager.loadPage(sessionId: sessionId, pageIndex: 0)
        XCTAssertEqual(page0.count, 100)
        XCTAssertEqual(page0.first?.id, 0)
        XCTAssertEqual(page0.last?.id, 99)

        // Load second page
        let page1 = try await manager.loadPage(sessionId: sessionId, pageIndex: 1)
        XCTAssertEqual(page1.count, 50)
        XCTAssertEqual(page1.first?.id, 100)
        XCTAssertEqual(page1.last?.id, 149)

        // Keep `trace` alive until here so its deinit cleanup doesn't race the test.
        _ = trace.stateCount

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    func testLoadStatesRange() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        for i in 0..<20 {
            let state = TraceState(id: i, action: "Step", variables: ["i": .int(i)])
            try await writer.append(state)
        }

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Load a range of states
        let range = try await lazyTrace.loadStates(range: 5..<10)
        XCTAssertEqual(range.count, 5)
        XCTAssertEqual(range.first?.id, 5)
        XCTAssertEqual(range.last?.id, 9)

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    func testLoadStatesRangeExceedsCount() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        for i in 0..<10 {
            let state = TraceState(id: i, action: "Step", variables: [:])
            try await writer.append(state)
        }

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Load range that exceeds state count
        let range = try await lazyTrace.loadStates(range: 5..<100)
        XCTAssertEqual(range.count, 5) // Only states 5-9 exist

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    // MARK: - toErrorTrace Tests

    func testToErrorTraceLoadsAllStates() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        for i in 0..<25 {
            let state = TraceState(id: i, action: "Step\(i)", variables: ["x": .int(i)])
            try await writer.append(state)
        }

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .livenessViolation,
            message: "Liveness failed",
            loopStart: 10,
            violatedProperty: "Eventually(done)"
        )

        // Convert to full ErrorTrace
        let errorTrace = try await lazyTrace.toErrorTrace()

        XCTAssertEqual(errorTrace.states.count, 25)
        XCTAssertEqual(errorTrace.type, .livenessViolation)
        XCTAssertEqual(errorTrace.message, "Liveness failed")
        XCTAssertEqual(errorTrace.loopStart, 10)
        XCTAssertEqual(errorTrace.violatedProperty, "Eventually(done)")

        // Verify state content
        XCTAssertEqual(errorTrace.states[0].id, 0)
        XCTAssertEqual(errorTrace.states[24].id, 24)

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    // MARK: - Cleanup Tests

    func testCleanupRemovesSession() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        let state = TraceState(id: 0, action: "Init", variables: [:])
        try await writer.append(state)

        _ = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Clean up
        await manager.cleanup(sessionId: sessionId)

        // Attempting to load should fail
        do {
            _ = try await manager.loadState(sessionId: sessionId, index: 0)
            XCTFail("Expected sessionNotFound error")
        } catch let error as TraceStorageError {
            if case .sessionNotFound(let id) = error {
                XCTAssertEqual(id, sessionId)
            } else {
                XCTFail("Expected sessionNotFound error, got \(error)")
            }
        }
    }

    // MARK: - Error Handling Tests

    func testSessionNotFoundError() async throws {
        let fakeSessionId = UUID()

        do {
            _ = try await manager.loadState(sessionId: fakeSessionId, index: 0)
            XCTFail("Expected sessionNotFound error")
        } catch let error as TraceStorageError {
            if case .sessionNotFound(let id) = error {
                XCTAssertEqual(id, fakeSessionId)
            } else {
                XCTFail("Expected sessionNotFound error")
            }
        }
    }

    func testStateNotFoundError() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        let state = TraceState(id: 0, action: "Init", variables: [:])
        try await writer.append(state)

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Try to load state beyond count
        do {
            _ = try await lazyTrace.loadState(at: 100)
            XCTFail("Expected stateNotFound error")
        } catch let error as TraceStorageError {
            if case .stateNotFound(let index) = error {
                XCTAssertEqual(index, 100)
            } else {
                XCTFail("Expected stateNotFound error")
            }
        }

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    func testNegativeStateIndexReturnsError() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)
        try await writer.append(TraceState(id: 0, action: "Init", variables: [:]))

        _ = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        do {
            _ = try await manager.loadState(sessionId: sessionId, index: -1)
            XCTFail("Expected stateNotFound error")
        } catch let error as TraceStorageError {
            if case .stateNotFound(let index) = error {
                XCTAssertEqual(index, -1)
            } else {
                XCTFail("Expected stateNotFound error")
            }
        }

        await manager.cleanup(sessionId: sessionId)
    }

    func testAppendToNonexistentSession() async throws {
        let fakeSessionId = UUID()

        do {
            let state = TraceState(id: 0, action: "Init", variables: [:])
            try await manager.appendState(state, sessionId: fakeSessionId)
            XCTFail("Expected sessionNotFound error")
        } catch let error as TraceStorageError {
            if case .sessionNotFound = error {
                // Expected
            } else {
                XCTFail("Expected sessionNotFound error")
            }
        }
    }

    func testFinalizeNonexistentSession() async throws {
        let fakeSessionId = UUID()

        do {
            _ = try await manager.finalizeTrace(
                sessionId: fakeSessionId,
                type: .invariantViolation,
                message: "Test",
                loopStart: nil,
                violatedProperty: nil
            )
            XCTFail("Expected sessionNotFound error")
        } catch let error as TraceStorageError {
            if case .sessionNotFound = error {
                // Expected
            } else {
                XCTFail("Expected sessionNotFound error")
            }
        }
    }

    // MARK: - Threshold Tests

    func testShouldStreamToDiskThreshold() async {
        // Below threshold
        let below500 = await manager.shouldStreamToDisk(stateCount: 500)
        XCTAssertFalse(below500)

        let atThreshold = await manager.shouldStreamToDisk(stateCount: 1000)
        XCTAssertFalse(atThreshold)

        // Above threshold
        let above1001 = await manager.shouldStreamToDisk(stateCount: 1001)
        XCTAssertTrue(above1001)

        let above5000 = await manager.shouldStreamToDisk(stateCount: 5000)
        XCTAssertTrue(above5000)
    }

    // MARK: - Complex Variable Types Tests

    func testComplexVariableTypesInTrace() async throws {
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)

        let complexState = TraceState(
            id: 0,
            action: "Init",
            variables: [
                "intVal": .int(42),
                "boolVal": .bool(true),
                "stringVal": .string("hello"),
                "seqVal": .sequence([.int(1), .int(2), .int(3)]),
                "recordVal": .record(["a": .int(1), "b": .string("test")]),
                "tupleVal": .tuple([.int(1), .bool(false)]),
                "modelVal": .modelValue("mv1")
            ]
        )

        try await writer.append(complexState)

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Load and verify
        let loadedState = try await lazyTrace.loadState(at: 0)

        XCTAssertEqual(loadedState.variables["intVal"], .int(42))
        XCTAssertEqual(loadedState.variables["boolVal"], .bool(true))
        XCTAssertEqual(loadedState.variables["stringVal"], .string("hello"))
        XCTAssertEqual(loadedState.variables["seqVal"], .sequence([.int(1), .int(2), .int(3)]))
        XCTAssertEqual(loadedState.variables["tupleVal"], .tuple([.int(1), .bool(false)]))
        XCTAssertEqual(loadedState.variables["modelVal"], .modelValue("mv1"))

        if case .record(let fields) = loadedState.variables["recordVal"] {
            XCTAssertEqual(fields["a"], .int(1))
            XCTAssertEqual(fields["b"], .string("test"))
        } else {
            XCTFail("Expected record value")
        }

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }
}

// MARK: - Lazy Error Trace Tests

final class LazyErrorTraceTests: XCTestCase {

    // MARK: - In-Memory Mode Tests

    func testInMemoryLazyTrace() async throws {
        let states = [
            TraceState(id: 0, action: "Init", variables: ["x": .int(0)]),
            TraceState(id: 1, action: "Next", variables: ["x": .int(1)]),
            TraceState(id: 2, action: "Next", variables: ["x": .int(2)])
        ]

        let lazyTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "TypeOK violated",
            states: states,
            loopStart: nil,
            violatedProperty: "TypeOK"
        )

        XCTAssertFalse(lazyTrace.isStoredOnDisk)
        XCTAssertEqual(lazyTrace.stateCount, 3)
        XCTAssertEqual(lazyTrace.type, .invariantViolation)
        XCTAssertEqual(lazyTrace.message, "TypeOK violated")
    }

    func testInMemoryLoadState() async throws {
        let states = [
            TraceState(id: 0, action: "Init", variables: ["x": .int(0)]),
            TraceState(id: 1, action: "Next", variables: ["x": .int(1)])
        ]

        let lazyTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: states,
            loopStart: nil,
            violatedProperty: nil
        )

        let state0 = try await lazyTrace.loadState(at: 0)
        XCTAssertEqual(state0.id, 0)
        XCTAssertEqual(state0.variables["x"], .int(0))

        let state1 = try await lazyTrace.loadState(at: 1)
        XCTAssertEqual(state1.id, 1)
        XCTAssertEqual(state1.variables["x"], .int(1))
    }

    func testInMemoryLoadStateOutOfBounds() async throws {
        let states = [TraceState(id: 0, action: "Init", variables: [:])]

        let lazyTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: states,
            loopStart: nil,
            violatedProperty: nil
        )

        do {
            _ = try await lazyTrace.loadState(at: 5)
            XCTFail("Expected stateNotFound error")
        } catch let error as TraceStorageError {
            if case .stateNotFound(let index) = error {
                XCTAssertEqual(index, 5)
            } else {
                XCTFail("Expected stateNotFound error")
            }
        }
    }

    func testInMemoryLoadStateNegativeIndex() async throws {
        let lazyTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: [TraceState(id: 0, action: "Init", variables: [:])],
            loopStart: nil,
            violatedProperty: nil
        )

        do {
            _ = try await lazyTrace.loadState(at: -1)
            XCTFail("Expected stateNotFound error")
        } catch let error as TraceStorageError {
            if case .stateNotFound(let index) = error {
                XCTAssertEqual(index, -1)
            } else {
                XCTFail("Expected stateNotFound error")
            }
        }
    }

    func testInMemoryLoadStatesRange() async throws {
        let states = (0..<10).map { i in
            TraceState(id: i, action: "Step", variables: ["i": .int(i)])
        }

        let lazyTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: states,
            loopStart: nil,
            violatedProperty: nil
        )

        let range = try await lazyTrace.loadStates(range: 3..<7)
        XCTAssertEqual(range.count, 4)
        XCTAssertEqual(range.first?.id, 3)
        XCTAssertEqual(range.last?.id, 6)
    }

    func testInMemoryRangeClamping() async throws {
        let states = (0..<5).map { i in
            TraceState(id: i, action: "Step", variables: [:])
        }

        let lazyTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: states,
            loopStart: nil,
            violatedProperty: nil
        )

        // Request range that exceeds bounds
        let range = try await lazyTrace.loadStates(range: 3..<100)
        XCTAssertEqual(range.count, 2) // Only states 3 and 4 exist
    }

    func testInMemoryToErrorTrace() async throws {
        let states = [
            TraceState(id: 0, action: "Init", variables: ["x": .int(0)]),
            TraceState(id: 1, action: "Loop", variables: ["x": .int(1)])
        ]

        let lazyTrace = LazyErrorTrace(
            type: .livenessViolation,
            message: "Liveness failed",
            states: states,
            loopStart: 0,
            violatedProperty: "Eventually(done)"
        )

        let errorTrace = try await lazyTrace.toErrorTrace()

        XCTAssertEqual(errorTrace.states.count, 2)
        XCTAssertEqual(errorTrace.type, .livenessViolation)
        XCTAssertEqual(errorTrace.message, "Liveness failed")
        XCTAssertEqual(errorTrace.loopStart, 0)
        XCTAssertEqual(errorTrace.violatedProperty, "Eventually(done)")
    }

    func testIsStoredOnDiskProperty() async throws {
        // In-memory trace
        let inMemoryTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: [TraceState(id: 0)],
            loopStart: nil,
            violatedProperty: nil
        )
        XCTAssertFalse(inMemoryTrace.isStoredOnDisk)

        // Disk-backed trace (needs to go through manager)
        let manager = TraceStorageManager.shared
        let sessionId = UUID()
        let writer = try await manager.beginTrace(sessionId: sessionId)
        try await writer.append(TraceState(id: 0, action: "Init", variables: [:]))

        let diskTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        XCTAssertTrue(diskTrace.isStoredOnDisk)

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }
}

// MARK: - Trace Writer Tests

final class TraceWriterTests: XCTestCase {

    func testWriterCountIncrementsOnAppend() async throws {
        let manager = TraceStorageManager.shared
        let sessionId = UUID()

        let writer = try await manager.beginTrace(sessionId: sessionId)
        XCTAssertEqual(writer.count, 0)

        try await writer.append(TraceState(id: 0, action: "Init", variables: [:]))
        XCTAssertEqual(writer.count, 1)

        try await writer.append(TraceState(id: 1, action: "Next", variables: [:]))
        XCTAssertEqual(writer.count, 2)

        try await writer.append(TraceState(id: 2, action: "Next", variables: [:]))
        XCTAssertEqual(writer.count, 3)

        // Clean up (need to finalize first)
        _ = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )
        await manager.cleanup(sessionId: sessionId)
    }

    func testWriterSessionId() async throws {
        let manager = TraceStorageManager.shared
        let sessionId = UUID()

        let writer = try await manager.beginTrace(sessionId: sessionId)
        XCTAssertEqual(writer.sessionId, sessionId)

        // Clean up
        _ = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )
        await manager.cleanup(sessionId: sessionId)
    }
}

// MARK: - Trace Storage Error Tests

final class TraceStorageErrorTests: XCTestCase {

    func testSessionNotFoundErrorDescription() {
        let id = UUID()
        let error = TraceStorageError.sessionNotFound(id)
        XCTAssertTrue(error.errorDescription?.contains(id.uuidString) ?? false)
    }

    func testStateNotFoundErrorDescription() {
        let error = TraceStorageError.stateNotFound(42)
        XCTAssertTrue(error.errorDescription?.contains("42") ?? false)
    }

    func testCorruptedFileErrorDescription() {
        let error = TraceStorageError.corruptedFile
        XCTAssertTrue(error.errorDescription?.contains("corrupted") ?? false)
    }

    func testManagerDeallocatedErrorDescription() {
        let error = TraceStorageError.managerDeallocated
        XCTAssertTrue(error.errorDescription?.contains("deallocated") ?? false)
    }
}

// MARK: - Large Trace Integration Tests

final class LargeTraceIntegrationTests: XCTestCase {

    func testLargeTraceStreaming() async throws {
        let manager = TraceStorageManager.shared
        let sessionId = UUID()

        let writer = try await manager.beginTrace(sessionId: sessionId)

        // Create a trace larger than the threshold (1000 states)
        let stateCount = 1500
        for i in 0..<stateCount {
            let state = TraceState(
                id: i,
                action: i == 0 ? "Init" : "Step",
                variables: [
                    "counter": .int(i),
                    "flag": .bool(i % 2 == 0)
                ]
            )
            try await writer.append(state)
        }

        XCTAssertEqual(writer.count, stateCount)

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Counter exceeded limit",
            loopStart: nil,
            violatedProperty: "CounterInRange"
        )

        XCTAssertEqual(lazyTrace.stateCount, stateCount)
        XCTAssertTrue(lazyTrace.isStoredOnDisk)

        // Verify we can load states from different positions
        let firstState = try await lazyTrace.loadState(at: 0)
        XCTAssertEqual(firstState.id, 0)
        XCTAssertEqual(firstState.action, "Init")

        let middleState = try await lazyTrace.loadState(at: 750)
        XCTAssertEqual(middleState.id, 750)
        XCTAssertEqual(middleState.variables["counter"], .int(750))

        let lastState = try await lazyTrace.loadState(at: stateCount - 1)
        XCTAssertEqual(lastState.id, stateCount - 1)

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }

    func testCacheEffectiveness() async throws {
        let manager = TraceStorageManager.shared
        let sessionId = UUID()

        let writer = try await manager.beginTrace(sessionId: sessionId)

        // Create enough states to span multiple pages
        for i in 0..<250 {
            let state = TraceState(id: i, action: "Step", variables: ["i": .int(i)])
            try await writer.append(state)
        }

        let lazyTrace = try await manager.finalizeTrace(
            sessionId: sessionId,
            type: .invariantViolation,
            message: "Test",
            loopStart: nil,
            violatedProperty: nil
        )

        // Access the same state multiple times - should hit cache
        for _ in 0..<10 {
            let state = try await lazyTrace.loadState(at: 50)
            XCTAssertEqual(state.id, 50)
        }

        // Access states across page boundaries
        let state0 = try await lazyTrace.loadState(at: 0)    // Page 0
        let state99 = try await lazyTrace.loadState(at: 99)  // Page 0
        let state100 = try await lazyTrace.loadState(at: 100) // Page 1
        let state199 = try await lazyTrace.loadState(at: 199) // Page 1

        XCTAssertEqual(state0.id, 0)
        XCTAssertEqual(state99.id, 99)
        XCTAssertEqual(state100.id, 100)
        XCTAssertEqual(state199.id, 199)

        // Clean up
        await manager.cleanup(sessionId: sessionId)
    }
}
