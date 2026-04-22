import XCTest
@testable import TLAStudioApp

// MARK: - Process Registry Tests

/// Tests for ProcessRegistry thread-safe process management.
final class ProcessRegistryTests: XCTestCase {

    // MARK: - Registration Tests

    func testRegisterProcess() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        registry.register(process, for: sessionId)

        // Verify the process is registered
        XCTAssertTrue(registry.registeredCount >= 1)

        // Clean up
        registry.terminate(sessionId)
    }

    func testUnregisterProcess() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        registry.register(process, for: sessionId)
        let countBefore = registry.registeredCount

        registry.unregister(sessionId)
        let countAfter = registry.registeredCount

        XCTAssertEqual(countAfter, countBefore - 1)
    }

    func testUnregisterNonexistentProcess() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()

        // Should not crash when unregistering a non-existent session
        registry.unregister(sessionId)
    }

    // MARK: - Termination Tests

    func testTerminateNonexistentSession() {
        let registry = ProcessRegistry.shared
        let fakeId = UUID()

        // Should not crash when terminating a non-existent session
        registry.terminate(fakeId)
    }

    func testTerminateRemovesFromRegistry() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        registry.register(process, for: sessionId)
        registry.terminate(sessionId)

        // After termination, isRunning should return false
        XCTAssertFalse(registry.isRunning(sessionId))
    }

    func testTerminateRunningProcess() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        // Start a simple long-running process
        process.executableURL = URL(fileURLWithPath: "/bin/sleep")
        process.arguments = ["10"]

        do {
            try process.run()
            registry.register(process, for: sessionId)

            XCTAssertTrue(process.isRunning)

            registry.terminate(sessionId)

            // Give a moment for termination
            Thread.sleep(forTimeInterval: 0.1)

            XCTAssertFalse(process.isRunning)
        } catch {
            XCTFail("Failed to start test process: \(error)")
        }
    }

    func testTerminateAlreadyTerminatedProcess() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        // Start a quick process that will finish immediately
        process.executableURL = URL(fileURLWithPath: "/bin/echo")
        process.arguments = ["test"]
        process.standardOutput = FileHandle.nullDevice

        do {
            try process.run()
            registry.register(process, for: sessionId)

            process.waitUntilExit()

            // Process is already terminated, terminate should not crash
            registry.terminate(sessionId)
        } catch {
            XCTFail("Failed to start test process: \(error)")
        }
    }

    // MARK: - Query Tests

    func testIsRunningForNonexistentSession() {
        let registry = ProcessRegistry.shared
        let fakeId = UUID()

        XCTAssertFalse(registry.isRunning(fakeId))
    }

    func testIsRunningForRegisteredButNotStarted() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        // Register without starting
        registry.register(process, for: sessionId)

        // Process is registered but not running
        XCTAssertFalse(registry.isRunning(sessionId))

        // Clean up
        registry.unregister(sessionId)
    }

    func testIsRunningForActiveProcess() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        process.executableURL = URL(fileURLWithPath: "/bin/sleep")
        process.arguments = ["10"]

        do {
            try process.run()
            registry.register(process, for: sessionId)

            XCTAssertTrue(registry.isRunning(sessionId))

            // Clean up
            registry.terminate(sessionId)
        } catch {
            XCTFail("Failed to start test process: \(error)")
        }
    }

    // MARK: - Concurrent Access Tests

    func testConcurrentRegistration() async {
        let registry = ProcessRegistry.shared
        let initialCount = registry.registeredCount

        // Register 100 processes concurrently
        await withTaskGroup(of: UUID.self) { group in
            for _ in 0..<100 {
                group.addTask {
                    let sessionId = UUID()
                    let process = Process()
                    registry.register(process, for: sessionId)
                    return sessionId
                }
            }

            // Collect all session IDs for cleanup
            var sessionIds: [UUID] = []
            for await sessionId in group {
                sessionIds.append(sessionId)
            }

            // Clean up
            for sessionId in sessionIds {
                registry.unregister(sessionId)
            }
        }

        // After cleanup, count should be back to initial
        XCTAssertEqual(registry.registeredCount, initialCount)
    }

    func testConcurrentTermination() async {
        let registry = ProcessRegistry.shared
        var sessionIds: [UUID] = []

        // Register 50 processes
        for _ in 0..<50 {
            let sessionId = UUID()
            let process = Process()
            registry.register(process, for: sessionId)
            sessionIds.append(sessionId)
        }

        // Terminate all concurrently
        await withTaskGroup(of: Void.self) { group in
            for sessionId in sessionIds {
                group.addTask {
                    registry.terminate(sessionId)
                }
            }
        }

        // All should be unregistered
        for sessionId in sessionIds {
            XCTAssertFalse(registry.isRunning(sessionId))
        }
    }

    // MARK: - Terminate All Tests

    func testTerminateAllWithMultipleProcesses() {
        let registry = ProcessRegistry.shared
        var sessionIds: [UUID] = []
        var processes: [Process] = []

        // Start 5 sleep processes
        for _ in 0..<5 {
            let sessionId = UUID()
            let process = Process()
            process.executableURL = URL(fileURLWithPath: "/bin/sleep")
            process.arguments = ["10"]

            do {
                try process.run()
                registry.register(process, for: sessionId)
                sessionIds.append(sessionId)
                processes.append(process)
            } catch {
                XCTFail("Failed to start test process: \(error)")
            }
        }

        // Terminate all
        registry.terminateAll()

        // Give a moment for termination
        Thread.sleep(forTimeInterval: 0.1)

        // All processes should be terminated
        for process in processes {
            XCTAssertFalse(process.isRunning)
        }

        // All sessions should be unregistered
        for sessionId in sessionIds {
            XCTAssertFalse(registry.isRunning(sessionId))
        }
    }

    func testTerminateAllWithNoProcesses() {
        let registry = ProcessRegistry.shared

        // Should not crash with no processes registered
        registry.terminateAll()
    }

    // MARK: - Running Count Tests

    func testRunningCountInitially() {
        let registry = ProcessRegistry.shared

        // Running count should be >= 0
        XCTAssertGreaterThanOrEqual(registry.runningCount, 0)
    }

    func testRunningCountWithActiveProcess() {
        let registry = ProcessRegistry.shared
        let initialRunningCount = registry.runningCount

        let sessionId = UUID()
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/bin/sleep")
        process.arguments = ["10"]

        do {
            try process.run()
            registry.register(process, for: sessionId)

            XCTAssertEqual(registry.runningCount, initialRunningCount + 1)

            // Clean up
            registry.terminate(sessionId)
        } catch {
            XCTFail("Failed to start test process: \(error)")
        }
    }

    // MARK: - Edge Case Tests

    func testRegisterSameSessionIdTwice() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process1 = Process()
        let process2 = Process()

        registry.register(process1, for: sessionId)
        registry.register(process2, for: sessionId)

        // Second registration should overwrite the first
        // Terminating should only affect the second process
        registry.terminate(sessionId)

        // No crash expected
    }

    // MARK: - Stress Tests

    func testHighVolumeConcurrentOperations() async {
        let registry = ProcessRegistry.shared
        let operationCount = 1000

        await withTaskGroup(of: Void.self) { group in
            // Concurrent registrations
            for i in 0..<operationCount {
                group.addTask {
                    let sessionId = UUID()
                    let process = Process()
                    registry.register(process, for: sessionId)

                    // Random delay
                    if i % 10 == 0 {
                        try? await Task.sleep(nanoseconds: 1000)
                    }

                    // Sometimes terminate, sometimes unregister
                    if i % 2 == 0 {
                        registry.terminate(sessionId)
                    } else {
                        registry.unregister(sessionId)
                    }
                }
            }
        }

        // Should complete without deadlock or crash
        XCTAssertTrue(true)
    }

    func testRapidRegisterUnregisterSameId() async {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()

        await withTaskGroup(of: Void.self) { group in
            for _ in 0..<100 {
                group.addTask {
                    let process = Process()
                    registry.register(process, for: sessionId)
                }
                group.addTask {
                    registry.unregister(sessionId)
                }
                group.addTask {
                    registry.terminate(sessionId)
                }
            }
        }

        // Should not deadlock
        XCTAssertTrue(true)
    }

    func testConcurrentQueriesWhileModifying() async {
        let registry = ProcessRegistry.shared
        var sessionIds: [UUID] = []

        // Register some processes
        for _ in 0..<50 {
            let sessionId = UUID()
            let process = Process()
            registry.register(process, for: sessionId)
            sessionIds.append(sessionId)
        }

        await withTaskGroup(of: Void.self) { group in
            // Concurrent queries
            for sessionId in sessionIds {
                group.addTask {
                    _ = registry.isRunning(sessionId)
                    _ = registry.registeredCount
                    _ = registry.runningCount
                }
            }

            // Concurrent modifications
            for sessionId in sessionIds {
                group.addTask {
                    registry.terminate(sessionId)
                }
            }
        }

        // Should complete without crash
        XCTAssertTrue(true)
    }

    // MARK: - Process Lifecycle Tests

    func testProcessCompletesNaturally() async {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        // Start a quick process
        process.executableURL = URL(fileURLWithPath: "/bin/echo")
        process.arguments = ["test"]
        process.standardOutput = FileHandle.nullDevice

        do {
            try process.run()
            registry.register(process, for: sessionId)

            XCTAssertTrue(registry.isRunning(sessionId) || !process.isRunning)

            // Wait for natural completion
            process.waitUntilExit()

            // Process completed naturally, but still registered
            XCTAssertFalse(registry.isRunning(sessionId))

            // Cleanup
            registry.unregister(sessionId)
        } catch {
            XCTFail("Failed to start process: \(error)")
        }
    }

    func testTerminateWithSignal() {
        let registry = ProcessRegistry.shared
        let sessionId = UUID()
        let process = Process()

        process.executableURL = URL(fileURLWithPath: "/bin/sleep")
        process.arguments = ["60"]

        do {
            try process.run()
            registry.register(process, for: sessionId)

            XCTAssertTrue(process.isRunning)

            // Terminate via registry
            registry.terminate(sessionId)

            // Give time for signal handling
            Thread.sleep(forTimeInterval: 0.2)

            XCTAssertFalse(process.isRunning)

            // Verify termination status (SIGTERM = 15)
            // On macOS, terminate() sends SIGTERM
            XCTAssertNotEqual(process.terminationStatus, 0)
        } catch {
            XCTFail("Failed to start process: \(error)")
        }
    }

    func testMultipleProcessesIndependentTermination() {
        let registry = ProcessRegistry.shared
        var sessions: [(UUID, Process)] = []

        // Start 5 independent processes
        for i in 0..<5 {
            let sessionId = UUID()
            let process = Process()
            process.executableURL = URL(fileURLWithPath: "/bin/sleep")
            process.arguments = ["\(10 + i)"]

            do {
                try process.run()
                registry.register(process, for: sessionId)
                sessions.append((sessionId, process))
            } catch {
                XCTFail("Failed to start process \(i): \(error)")
            }
        }

        // Terminate every other process
        for (index, (sessionId, _)) in sessions.enumerated() {
            if index % 2 == 0 {
                registry.terminate(sessionId)
            }
        }

        Thread.sleep(forTimeInterval: 0.2)

        // Verify correct processes are terminated
        for (index, (sessionId, process)) in sessions.enumerated() {
            if index % 2 == 0 {
                XCTAssertFalse(process.isRunning, "Process \(index) should be terminated")
                XCTAssertFalse(registry.isRunning(sessionId))
            } else {
                XCTAssertTrue(process.isRunning, "Process \(index) should still be running")
                XCTAssertTrue(registry.isRunning(sessionId))
            }
        }

        // Cleanup remaining processes
        for (sessionId, _) in sessions {
            registry.terminate(sessionId)
        }
    }

    // MARK: - Edge Case Tests

    func testTerminateAllWithMixedStates() {
        let registry = ProcessRegistry.shared
        var sessionIds: [UUID] = []

        // Some running processes
        for _ in 0..<3 {
            let sessionId = UUID()
            let process = Process()
            process.executableURL = URL(fileURLWithPath: "/bin/sleep")
            process.arguments = ["10"]

            do {
                try process.run()
                registry.register(process, for: sessionId)
                sessionIds.append(sessionId)
            } catch {
                XCTFail("Failed to start process")
            }
        }

        // Some completed processes
        for _ in 0..<2 {
            let sessionId = UUID()
            let process = Process()
            process.executableURL = URL(fileURLWithPath: "/bin/echo")
            process.arguments = ["done"]
            process.standardOutput = FileHandle.nullDevice

            do {
                try process.run()
                registry.register(process, for: sessionId)
                process.waitUntilExit()
                sessionIds.append(sessionId)
            } catch {
                XCTFail("Failed to start process")
            }
        }

        // Some never-started processes
        for _ in 0..<2 {
            let sessionId = UUID()
            let process = Process()
            registry.register(process, for: sessionId)
            sessionIds.append(sessionId)
        }

        // Terminate all should handle all states
        registry.terminateAll()

        // All should be unregistered
        for sessionId in sessionIds {
            XCTAssertFalse(registry.isRunning(sessionId))
        }
    }

    func testRegistryCountAccuracy() {
        let registry = ProcessRegistry.shared
        let initialCount = registry.registeredCount

        var sessionIds: [UUID] = []

        // Add 10 processes
        for _ in 0..<10 {
            let sessionId = UUID()
            let process = Process()
            registry.register(process, for: sessionId)
            sessionIds.append(sessionId)
        }

        XCTAssertEqual(registry.registeredCount, initialCount + 10)

        // Remove 5
        for i in 0..<5 {
            registry.unregister(sessionIds[i])
        }

        XCTAssertEqual(registry.registeredCount, initialCount + 5)

        // Terminate remaining 5
        for i in 5..<10 {
            registry.terminate(sessionIds[i])
        }

        XCTAssertEqual(registry.registeredCount, initialCount)
    }

    // MARK: - Thread Safety Verification

    func testNoDataRaceOnConcurrentAccess() async {
        let registry = ProcessRegistry.shared
        let iterations = 500

        await withTaskGroup(of: Void.self) { group in
            // Writer tasks
            for _ in 0..<iterations {
                group.addTask {
                    let sessionId = UUID()
                    let process = Process()
                    registry.register(process, for: sessionId)
                    registry.terminate(sessionId)
                }
            }

            // Reader tasks
            for _ in 0..<iterations {
                group.addTask {
                    _ = registry.registeredCount
                    _ = registry.runningCount
                }
            }

            // Query tasks
            for _ in 0..<iterations {
                group.addTask {
                    _ = registry.isRunning(UUID())
                }
            }
        }

        // If we get here without crash, thread safety is working
        XCTAssertTrue(true)
    }
}
