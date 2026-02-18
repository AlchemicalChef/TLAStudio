import Foundation
import os

private let logger = Log.logger(category: "ProcessRegistry")

// MARK: - Process Registry

/// Thread-safe registry for managing subprocess lifecycles.
/// Enables synchronous process termination during app shutdown to prevent orphaned processes.
/// Uses process group termination to ensure child processes are also killed.
/// @unchecked Sendable: thread safety ensured by NSLock
final class ProcessRegistry: @unchecked Sendable {
    static let shared = ProcessRegistry()

    private let lock = NSLock()
    private var processes: [UUID: Process] = [:]
    /// Store PIDs separately since processIdentifier becomes invalid after process exits
    private var pids: [UUID: pid_t] = [:]

    private init() {}

    // MARK: - Registration

    /// Register a process for tracking.
    /// Call this immediately after successfully starting a process.
    func register(_ process: Process, for sessionId: UUID) {
        lock.lock()
        defer { lock.unlock() }
        processes[sessionId] = process
        // Store PID separately since it becomes invalid after process exits
        pids[sessionId] = process.processIdentifier
        logger.debug("Registered process PID \(process.processIdentifier) for session \(sessionId.uuidString)")
    }

    /// Unregister a process after it has terminated normally.
    /// Call this when a process completes (either successfully or with error).
    func unregister(_ sessionId: UUID) {
        lock.lock()
        defer { lock.unlock() }
        processes.removeValue(forKey: sessionId)
        pids.removeValue(forKey: sessionId)
        logger.debug("Unregistered process for session \(sessionId.uuidString)")
    }

    // MARK: - Termination

    /// Terminate a specific process and its children synchronously.
    /// Safe to call even if the process has already terminated or was never registered.
    func terminate(_ sessionId: UUID) {
        lock.lock()
        let process = processes.removeValue(forKey: sessionId)
        let pid = pids.removeValue(forKey: sessionId)
        lock.unlock()

        if let process = process, let pid = pid {
            terminateProcessTree(process: process, pid: pid, sessionId: sessionId)
        }
    }

    /// Terminate all registered processes and their children synchronously.
    /// Call this during app shutdown to ensure no orphaned processes.
    func terminateAll() {
        lock.lock()
        let allProcesses = processes
        let allPids = pids
        processes.removeAll()
        pids.removeAll()
        lock.unlock()

        var terminatedCount = 0
        for (sessionId, process) in allProcesses {
            if let pid = allPids[sessionId] {
                if terminateProcessTree(process: process, pid: pid, sessionId: sessionId) {
                    terminatedCount += 1
                }
            }
        }

        if terminatedCount > 0 {
            logger.info("Terminated \(terminatedCount) process trees during shutdown")
        }
    }

    /// Terminate a process and all its child processes.
    /// Returns true if the process was running and terminated.
    @discardableResult
    private func terminateProcessTree(process: Process, pid: pid_t, sessionId: UUID) -> Bool {
        guard process.isRunning else {
            logger.debug("Process for session \(sessionId.uuidString) already terminated")
            // Even if the main process is dead, try to kill any orphaned children
            killChildProcesses(parentPid: pid)
            return false
        }

        logger.info("Terminating process tree for session \(sessionId.uuidString), PID \(pid)")

        // First, try graceful termination with SIGTERM
        // Kill the process group (negative PID kills all processes in the group)
        // This works if the process became its own process group leader
        kill(-pid, SIGTERM)

        // Also send SIGTERM directly to the process
        process.terminate()

        // Wait briefly for graceful shutdown
        let deadline = Date().addingTimeInterval(0.5)
        while process.isRunning && Date() < deadline {
            Thread.sleep(forTimeInterval: 0.05)
        }

        // If still running, escalate to SIGKILL
        if process.isRunning {
            logger.warning("Process \(pid) didn't respond to SIGTERM, sending SIGKILL")
            kill(-pid, SIGKILL)
            kill(pid, SIGKILL)

            // Wait for forced termination
            let killDeadline = Date().addingTimeInterval(0.5)
            while process.isRunning && Date() < killDeadline {
                Thread.sleep(forTimeInterval: 0.05)
            }
        }

        // Also kill any child processes that might have escaped the process group
        killChildProcesses(parentPid: pid)

        if process.isRunning {
            logger.error("Failed to terminate process \(pid)")
            return false
        }

        logger.debug("Successfully terminated process tree for session \(sessionId.uuidString)")
        return true
    }

    /// Kill all child processes of a given parent PID.
    /// Uses pgrep to find children and kills them recursively.
    private func killChildProcesses(parentPid: pid_t) {
        // Use pgrep to find child processes
        let pgrep = Process()
        pgrep.executableURL = URL(fileURLWithPath: "/usr/bin/pgrep")
        pgrep.arguments = ["-P", String(parentPid)]

        let pipe = Pipe()
        pgrep.standardOutput = pipe
        pgrep.standardError = FileHandle.nullDevice

        do {
            try pgrep.run()
            pgrep.waitUntilExit()

            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            if let output = String(data: data, encoding: .utf8) {
                let childPids = output.split(separator: "\n").compactMap { Int32($0) }
                for childPid in childPids {
                    // Verify the child's parent PID still matches before killing
                    // to guard against PID reuse between pgrep and kill
                    guard verifyParentPid(of: childPid, equals: parentPid) else {
                        logger.warning("PID \(childPid) parent changed (PID reuse detected), skipping kill")
                        continue
                    }
                    // Recursively kill grandchildren first
                    killChildProcesses(parentPid: childPid)
                    // Then kill the child
                    kill(childPid, SIGKILL)
                    logger.debug("Killed orphaned child process \(childPid)")
                }
            }
        } catch {
            // pgrep might not find any children, which is fine
        }
    }

    /// Verify that the given PID's parent matches the expected parent PID.
    /// Uses sysctl(KERN_PROC) for an atomic check, guarding against PID reuse.
    private func verifyParentPid(of pid: pid_t, equals expectedParent: pid_t) -> Bool {
        var mib: [Int32] = [CTL_KERN, KERN_PROC, KERN_PROC_PID, pid]
        var info = kinfo_proc()
        var size = MemoryLayout<kinfo_proc>.size
        guard sysctl(&mib, UInt32(mib.count), &info, &size, nil, 0) == 0 else {
            return false
        }
        return info.kp_eproc.e_ppid == expectedParent
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
