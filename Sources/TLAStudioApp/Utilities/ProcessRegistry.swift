import Foundation
import os

private let logger = Logger(subsystem: "com.tlastudio", category: "ProcessRegistry")

// MARK: - Process Registry

/// Thread-safe registry for managing subprocess lifecycles.
/// Enables synchronous process termination during app shutdown to prevent orphaned processes.
final class ProcessRegistry: @unchecked Sendable {
    static let shared = ProcessRegistry()

    private let lock = NSLock()
    private var processes: [UUID: Process] = [:]

    private init() {}

    // MARK: - Registration

    /// Register a process for tracking.
    /// Call this immediately after successfully starting a process.
    func register(_ process: Process, for sessionId: UUID) {
        lock.lock()
        defer { lock.unlock() }
        processes[sessionId] = process
        logger.debug("Registered process for session \(sessionId.uuidString)")
    }

    /// Unregister a process after it has terminated normally.
    /// Call this when a process completes (either successfully or with error).
    func unregister(_ sessionId: UUID) {
        lock.lock()
        defer { lock.unlock() }
        processes.removeValue(forKey: sessionId)
        logger.debug("Unregistered process for session \(sessionId.uuidString)")
    }

    // MARK: - Termination

    /// Terminate a specific process synchronously.
    /// Safe to call even if the process has already terminated or was never registered.
    func terminate(_ sessionId: UUID) {
        lock.lock()
        let process = processes.removeValue(forKey: sessionId)
        lock.unlock()

        if let process = process {
            if process.isRunning {
                process.terminate()
                logger.info("Terminated process for session \(sessionId.uuidString)")
            } else {
                logger.debug("Process for session \(sessionId.uuidString) already terminated")
            }
        }
    }

    /// Terminate all registered processes synchronously.
    /// Call this during app shutdown to ensure no orphaned processes.
    func terminateAll() {
        lock.lock()
        let allProcesses = processes
        processes.removeAll()
        lock.unlock()

        var terminatedCount = 0
        for (sessionId, process) in allProcesses {
            if process.isRunning {
                process.terminate()
                terminatedCount += 1
                logger.debug("Terminated process for session \(sessionId.uuidString)")
            }
        }

        if terminatedCount > 0 {
            logger.info("Terminated \(terminatedCount) running processes during shutdown")
        }
    }

    // MARK: - Queries

    /// Check if a process is registered and running.
    func isRunning(_ sessionId: UUID) -> Bool {
        lock.lock()
        defer { lock.unlock() }
        return processes[sessionId]?.isRunning ?? false
    }

    /// Get the count of currently registered processes.
    var registeredCount: Int {
        lock.lock()
        defer { lock.unlock() }
        return processes.count
    }

    /// Get the count of currently running processes.
    var runningCount: Int {
        lock.lock()
        defer { lock.unlock() }
        return processes.values.filter { $0.isRunning }.count
    }
}
