import Foundation
import os

/// Source-compat alias: the runner started life as the java-tooling runner
/// (`pcal.trans`, `tla2sany.SANY`) and was generalized for all one-shot
/// subprocess spawns (TLAPM single-step checks, Graphviz renders). The jar/java
/// discovery helpers below are still reached through this alias.
typealias JavaProcessRunner = SubprocessRunner

/// Shared hardened runner for one-shot (batch) tool subprocesses: spawn, drain
/// both pipes into bounded accumulators, enforce a timeout, bridge Swift task
/// cancellation to SIGTERM, and register with ProcessRegistry for app-quit reaping.
///
/// NOT for long-lived streaming sessions (TLC model checks, full TLAPM proof runs)
/// — those need incremental parsing and throttled progress streams and keep their
/// own lifecycle (reuse review O6).
enum SubprocessRunner {

    private static let logger = Log.logger(category: "SubprocessRunner")

    /// Default cap on captured stdout/stderr per stream. The java tools are expected to
    /// emit at most a few KB; anything past this is almost certainly a pathological loop
    /// and should not be allowed to balloon memory. The remainder is dropped (per the
    /// stream's truncation policy) but the process continues so we still observe its
    /// exit status.
    static let maxCapturedBytes = 10 * 1024 * 1024  // 10 MB

    /// Bounded wait for the pipe drain handlers to reach EOF after the process
    /// exits, so the final buffered chunk is captured in order before we
    /// snapshot. A wedged pipe (rare: a grandchild inherited the write end)
    /// can't hang the pool thread longer than this.
    private static let residualDrainTimeout: TimeInterval = 3

    /// Thrown when the subprocess exceeds `timeout`. The process is SIGTERM'd (with
    /// ProcessRegistry SIGKILL escalation if it doesn't comply).
    struct TimeoutError: Error, LocalizedError {
        let timeout: TimeInterval
        var errorDescription: String? {
            "Process timed out after \(Int(timeout)) seconds"
        }
    }

    /// Drain a pipe into an accumulator. Past a bounded policy's cap the accumulator
    /// stops growing but the handler keeps consuming so the writer isn't
    /// back-pressured into a deadlock. `tap` observes every chunk regardless of the
    /// truncation policy (used for live output-panel logging).
    private static func drain(
        handle: FileHandle,
        into accumulator: BoundedOutputAccumulator,
        reachedEOF: DispatchSemaphore,
        tap: (@Sendable (Data) -> Void)? = nil
    ) {
        handle.readabilityHandler = { [weak accumulator] h in
            let data = h.availableData
            if data.isEmpty {
                // EOF: this handler is the SOLE reader of the pipe, so clearing
                // it here and signalling lets the run() flow snapshot only after
                // the tail is captured — no second reader to race (e2e M2).
                h.readabilityHandler = nil
                reachedEOF.signal()
                return
            }
            accumulator?.append(data)
            tap?(data)
        }
    }

    /// Run a subprocess to completion and capture its output.
    ///
    /// - Parameters:
    ///   - executableURL: Tool binary to launch.
    ///   - arguments: Argument vector.
    ///   - currentDirectoryURL: Working directory (nil = inherit).
    ///   - timeout: Wall-clock limit; on expiry the process is terminated and
    ///     `TimeoutError` is thrown. nil = no limit.
    ///   - environment: Exact environment for the child. Defaults to a sanitized
    ///     `ProcessEnvironment.minimal()` so children never inherit the parent's
    ///     secrets or dangerous loader/runtime vars (DYLD_*, _JAVA_OPTIONS,
    ///     CLASSPATH, …) — defense-in-depth across every spawn path. Pass an
    ///     explicit dictionary to override, or `nil` to deliberately inherit the
    ///     full parent environment.
    ///   - stdinData: Bytes written to the child's stdin, after which stdin is closed
    ///     to signal EOF (nil = no stdin pipe).
    ///   - registryId: ProcessRegistry session id to register the child under, so an
    ///     owning session's `stop`/`terminate` can reach it (nil = private UUID).
    ///   - stdoutPolicy: Truncation policy for captured stdout.
    ///   - stderrPolicy: Truncation policy for captured stderr.
    ///   - onStderrData: Live tap invoked with every stderr chunk on the pipe-handler
    ///     thread (e.g. for streaming tool output to the Output panel).
    static func run(
        executableURL: URL,
        arguments: [String],
        currentDirectoryURL: URL? = nil,
        timeout: TimeInterval? = nil,
        environment: [String: String]? = ProcessEnvironment.minimal(),
        stdinData: Data? = nil,
        registryId: UUID? = nil,
        stdoutPolicy: BoundedOutputAccumulator.TruncationPolicy = .keepHead(limit: maxCapturedBytes),
        stderrPolicy: BoundedOutputAccumulator.TruncationPolicy = .keepHead(limit: maxCapturedBytes),
        onStderrData: (@Sendable (Data) -> Void)? = nil
    ) async throws -> (terminationStatus: Int32, stdout: Data, stderr: Data) {
        // Don't even launch when the calling Task is already cancelled — a
        // superseded semantic check or simulation step must not spawn a JVM
        // whose result nobody will read.
        try Task.checkCancellation()

        let process = Process()
        process.executableURL = executableURL
        process.arguments = arguments
        process.currentDirectoryURL = currentDirectoryURL
        if let environment {
            process.environment = environment
        }

        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        process.standardOutput = stdoutPipe
        process.standardError = stderrPipe

        var stdinPipe: Pipe?
        if stdinData != nil {
            let pipe = Pipe()
            process.standardInput = pipe
            stdinPipe = pipe
        }

        let stdoutAccumulator = BoundedOutputAccumulator(policy: stdoutPolicy)
        let stderrAccumulator = BoundedOutputAccumulator(policy: stderrPolicy)
        // Signalled when each pipe handler reads EOF, making the drain handler
        // the single reader of each pipe (no second availableData read racing it).
        let stdoutEOF = DispatchSemaphore(value: 0)
        let stderrEOF = DispatchSemaphore(value: 0)
        drain(handle: stdoutPipe.fileHandleForReading, into: stdoutAccumulator, reachedEOF: stdoutEOF)
        drain(handle: stderrPipe.fileHandleForReading, into: stderrAccumulator, reachedEOF: stderrEOF, tap: onStderrData)

        // Register the subprocess with ProcessRegistry so app shutdown (Cmd-Q)
        // can reap it via SIGTERM → SIGKILL escalation. Without this, an in-flight
        // tool survives the parent and gets launchd-reparented. Callers that own a
        // session id pass it via `registryId` so their stop paths can reach the child.
        let registrySessionId = registryId ?? UUID()

        // Holds the timeout Task so the termination handler can cancel it once the
        // process exits normally, preventing the Task from running its full sleep
        // duration after we no longer care. Captured by reference so the closure
        // can mutate it on the outer continuation's thread.
        let timeoutTaskBox = TimeoutTaskBox()

        // Whether `register()` was reached. Used by the post-continuation cleanup so we
        // only `unregister` what was actually registered (process.run() can throw).
        var registered = false

        // Cleanup that must run regardless of how the continuation resolved (normal exit,
        // process.run failure, or timeout-throw). Without this, a thrown timeout error
        // would skip the unregister/pipe-drain path below.
        defer {
            timeoutTaskBox.cancel()
            process.terminationHandler = nil
            if registered {
                if process.isRunning {
                    // Timeout fired but the process didn't honor SIGTERM (process.terminate);
                    // delegate to ProcessRegistry for SIGKILL escalation — off this
                    // cooperative-pool thread so the SIGTERM→sleep→SIGKILL escalation
                    // doesn't block it for up to ~1s (e2e Low).
                    DispatchQueue.global(qos: .userInitiated).async {
                        ProcessRegistry.shared.terminate(registrySessionId)
                    }
                } else {
                    ProcessRegistry.shared.unregister(registrySessionId)
                }
            } else {
                // process.run() threw, so the background stdin writer (which
                // otherwise owns the close) never ran — close the handle here.
                try? stdinPipe?.fileHandleForWriting.close()
            }

            // The drain handlers self-clear on EOF; clear again (idempotent) in
            // case we exit before EOF (timeout/throw), then close. The success
            // path has already awaited EOF below, so the handler is quiescent.
            stdoutPipe.fileHandleForReading.readabilityHandler = nil
            stderrPipe.fileHandleForReading.readabilityHandler = nil
            try? stdoutPipe.fileHandleForReading.close()
            try? stderrPipe.fileHandleForReading.close()
        }

        // Propagate Swift task cancellation to the subprocess: without this, a
        // cancelled caller returns immediately while the JVM keeps running to
        // completion (or timeout), and rapid reschedules stack live JVMs. On
        // cancel we SIGTERM the process; its terminationHandler then resumes
        // the continuation through the normal path, and the `defer` above
        // escalates via ProcessRegistry if SIGTERM is ignored.
        let cancellationBox = ProcessCancellationBox()

        // Observe termination via the process's handler rather than polling. Resumption is
        // gated by `Atomic` semantics on the continuation so a concurrent timeout can't
        // resume twice.
        let terminationStatus = try await withTaskCancellationHandler(operation: {
            try await withCheckedThrowingContinuation { (cont: CheckedContinuation<Int32, Error>) in
            let didResume = ResumeGuard()

            process.terminationHandler = { finished in
                // Cancel the pending timeout Task — the process is done, the sleep is moot.
                timeoutTaskBox.cancel()
                guard didResume.tryConsume() else { return }
                cont.resume(returning: finished.terminationStatus)
            }

            do {
                try process.run()
                ProcessRegistry.shared.register(process, for: registrySessionId)
                registered = true
                cancellationBox.activate(process)
            } catch {
                guard didResume.tryConsume() else { return }
                cont.resume(throwing: error)
                return
            }

            // Feed stdin off the continuation thread: a payload larger than the kernel
            // pipe buffer would otherwise block continuation setup until the child
            // consumes it. Closing the handle signals EOF (e.g. `dot` reads to EOF).
            if let stdinData, let stdinHandle = stdinPipe?.fileHandleForWriting {
                DispatchQueue.global(qos: .userInitiated).async {
                    // write(contentsOf:) throws (instead of raising ObjC exceptions)
                    // if the child exited early and the pipe is broken.
                    try? stdinHandle.write(contentsOf: stdinData)
                    try? stdinHandle.close()
                }
            }

            guard let timeout else { return }

            // If the timeout fires first, terminate the process and report the error.
            // The terminationHandler will still fire afterwards, but `didResume` prevents a
            // double resume. Store the Task so the termination handler can cancel it on
            // a fast exit, and distinguish CancellationError from a real timeout.
            let timeoutTask = Task {
                do {
                    try await Task.sleep(nanoseconds: UInt64(timeout * 1_000_000_000))
                } catch is CancellationError {
                    // Process exited fast; nothing to do. Termination handler already resumed.
                    return
                } catch {
                    return
                }
                guard didResume.tryConsume() else { return }
                process.terminate()
                cont.resume(throwing: TimeoutError(timeout: timeout))
            }
            timeoutTaskBox.set(timeoutTask)
            }
        }, onCancel: {
            cancellationBox.cancel()
        })

        // Single-reader invariant (e2e M2): the drain handler is the SOLE reader
        // of each pipe. Wait for it to reach EOF so the buffered tail is captured
        // in order before we snapshot — no second availableData read racing the
        // handler. The wait runs on a GCD thread (not the cooperative pool) and
        // is bounded so a wedged pipe can't hang us. Only the normal-exit path
        // reaches here; the throw paths discard output anyway.
        if registered {
            await withCheckedContinuation { (cont: CheckedContinuation<Void, Never>) in
                DispatchQueue.global(qos: .userInitiated).async {
                    // Shared deadline so the two sequential waits together can't
                    // exceed the bound (the second inherits the absolute deadline).
                    let deadline = DispatchTime.now() + residualDrainTimeout
                    _ = stdoutEOF.wait(timeout: deadline)
                    _ = stderrEOF.wait(timeout: deadline)
                    cont.resume()
                }
            }
        }

        return (terminationStatus, stdoutAccumulator.snapshot(), stderrAccumulator.snapshot())
    }

    /// Bridges Swift task cancellation to subprocess termination. `cancel` may
    /// fire before the process has launched (`activate`); whichever happens
    /// second performs the terminate. Lock-guarded because `onCancel` runs on
    /// an arbitrary thread.
    private final class ProcessCancellationBox: @unchecked Sendable {
        private let lock = NSLock()
        private var process: Process?
        private var cancelled = false

        func activate(_ process: Process) {
            lock.lock()
            let shouldTerminate = cancelled
            self.process = process
            lock.unlock()
            if shouldTerminate, process.isRunning {
                process.terminate()
            }
        }

        func cancel() {
            lock.lock()
            cancelled = true
            let process = self.process
            lock.unlock()
            if let process, process.isRunning {
                process.terminate()
            }
        }
    }

    /// Thread-safe handle for the timeout Task so the termination handler can cancel it.
    /// Lock-guarded because `set` is called on the continuation closure's thread while
    /// `cancel` may fire from the process's termination thread.
    private final class TimeoutTaskBox: @unchecked Sendable {
        private let lock = NSLock()
        private var task: Task<Void, Never>?
        private var cancelled = false

        func set(_ task: Task<Void, Never>) {
            lock.lock()
            defer { lock.unlock() }
            if cancelled {
                task.cancel()
            } else {
                self.task = task
            }
        }

        func cancel() {
            lock.lock()
            let task = self.task
            self.task = nil
            cancelled = true
            lock.unlock()
            task?.cancel()
        }
    }

    /// Single-shot resume token used to prevent CheckedContinuation from being resumed twice
    /// when both the termination handler and the timeout path race to resume.
    private final class ResumeGuard: @unchecked Sendable {
        private let lock = NSLock()
        private var consumed = false

        func tryConsume() -> Bool {
            lock.lock()
            defer { lock.unlock() }
            guard !consumed else { return false }
            consumed = true
            return true
        }
    }

    // MARK: - Java Toolchain Discovery
    // (Used by the jar-invoking features via the `JavaProcessRunner` alias.)

    static func findTLA2Tools() -> URL? {
        // Check via BinaryDiscovery
        if let url = BinaryDiscovery.find(named: "tla2tools", extension: "jar", options: .init(
            bundleSubdirectories: ["Tools", "bin"],
            homeRelativePaths: [".tlaplus", ".tla"]
        )) {
            return url
        }

        // Development checkout fallback.
        if let url = BinaryDiscovery.findDevelopmentFile(relativePath: "Scripts/tla2tools.jar") {
            return url
        }

        // Also check standard locations
        let standardPaths = [
            "/usr/local/share/tla+/tla2tools.jar",
            "/opt/homebrew/share/tla+/tla2tools.jar"
        ]

        for path in standardPaths {
            if FileManager.default.fileExists(atPath: path) {
                return URL(fileURLWithPath: path)
            }
        }

        return nil
    }

    static func findJava() -> String? {
        // Check JAVA_HOME first (user's preferred Java version)
        if let javaHome = ProcessInfo.processInfo.environment["JAVA_HOME"] {
            let javaPath = "\(javaHome)/bin/java"
            if FileManager.default.isExecutableFile(atPath: javaPath) {
                return javaPath
            }
        }

        // Fall back to common system locations
        let javaPaths = [
            "/usr/bin/java",
            "/usr/local/bin/java",
            "/opt/homebrew/bin/java"
        ]

        for path in javaPaths {
            if FileManager.default.isExecutableFile(atPath: path) {
                return path
            }
        }

        return nil
    }
}
