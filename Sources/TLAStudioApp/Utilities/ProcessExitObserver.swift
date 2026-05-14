import Foundation

/// Stores a process exit status until async code is ready to await it.
///
/// `Process.terminationHandler` is not a wait primitive if assigned after a fast
/// process exits. Install this observer before `run()` and await it afterwards.
final class ProcessExitObserver: @unchecked Sendable {
    private let lock = NSLock()
    private var continuations: [CheckedContinuation<Int32, Never>] = []
    private var status: Int32?

    func complete(status: Int32) {
        let continuationsToResume: [CheckedContinuation<Int32, Never>]

        lock.lock()
        if statusAlreadyRecorded {
            lock.unlock()
            return
        }
        self.status = status
        continuationsToResume = continuations
        continuations.removeAll()
        lock.unlock()

        for continuation in continuationsToResume {
            continuation.resume(returning: status)
        }
    }

    func wait(for process: Process) async -> Int32 {
        await withCheckedContinuation { continuation in
            let statusToResume: Int32?

            lock.lock()
            if let status {
                statusToResume = status
            } else if !process.isRunning {
                statusToResume = process.terminationStatus
                self.status = process.terminationStatus
            } else {
                continuations.append(continuation)
                statusToResume = nil
            }
            lock.unlock()

            if let statusToResume {
                continuation.resume(returning: statusToResume)
            }
        }
    }

    private var statusAlreadyRecorded: Bool {
        status != nil
    }
}
