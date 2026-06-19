import Foundation
import os

private let logger = Log.logger(category: "TLAPM")

private extension String {
    var nonEmptyOutputLines: [String] {
        components(separatedBy: .newlines).filter { !$0.isEmpty }
    }
}

// MARK: - TLAPM Process Manager

/// Actor that manages TLAPM (TLA+ Proof Manager) processes
///
/// This actor handles the lifecycle of TLAPM proof checking processes,
/// including binary discovery, process spawning, output parsing, and
/// cleanup. It supports both full specification proof checking and
/// checking individual proof steps.
actor TLAPMProcessManager {
    static let shared = TLAPMProcessManager()

    // MARK: - State

    private var activeProcesses: [UUID: Process] = [:]
    private var parsers: [UUID: TLAPMOutputParser] = [:]
    private var progressTasks: [UUID: Task<Void, Never>] = [:]
    private var streamStates: [UUID: StreamState<ProofCheckProgress>] = [:]

    /// Session ids of in-flight single-step checks. Their `Process` objects are owned
    /// by `SubprocessRunner` (registered with ProcessRegistry under the same id), so we
    /// track only the ids for stopAll/isRunning/activeSessionCount bookkeeping.
    private var activeStepSessions: Set<UUID> = []


    // MARK: - Binary Discovery

    private func configuredExecutableURL(
        forKey key: String,
        appending executableSuffix: String? = nil
    ) -> URL? {
        let configuredPath = UserDefaults.standard.string(forKey: key)?
            .trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        guard !configuredPath.isEmpty else { return nil }

        var url = URL(fileURLWithPath: configuredPath)
        if let executableSuffix {
            var isDirectory: ObjCBool = false
            if FileManager.default.fileExists(atPath: url.path, isDirectory: &isDirectory), isDirectory.boolValue {
                url.appendPathComponent(executableSuffix)
            }
        }

        guard FileManager.default.fileExists(atPath: url.path),
              FileManager.default.isExecutableFile(atPath: url.path) else {
            return nil
        }
        return url
    }

    /// Path to TLAPM binary
    private var tlapmPath: URL? {
        if let configured = configuredExecutableURL(forKey: UserSettings.Keys.tlapmPath) {
            return configured
        }
        return BinaryDiscovery.find(
            named: "tlapm",
            options: .init(
                bundleSubdirectories: ["bin", "Provers"],
                systemPaths: ["/usr/local/bin", "/opt/homebrew/bin"],
                homeRelativePaths: [".tla"]
            )
        )
    }

    /// Check if TLAPM is available
    var isTLAPMAvailable: Bool {
        tlapmPath != nil
    }

    /// Get the discovered TLAPM path for display
    var discoveredTLAPMPath: String? {
        tlapmPath?.path
    }

    /// Path to TLAPS standard library
    private var stdlibPath: URL? {
        // Upstream dune install uses `lib/tlapm/stdlib/`; our bundle flattens to `lib/tlapm/`.
        // Probe both, and require TLAPS.tla to actually exist so we never hand TLAPM a
        // ghost directory that silently fails the `EXTENDS TLAPS` lookup.
        let candidateSubdirs = ["lib/tlapm/stdlib", "lib/tlapm"]

        func firstValidStdlib(under base: URL) -> URL? {
            for subdir in candidateSubdirs {
                let libPath = base.appendingPathComponent(subdir)
                let tlapsFile = libPath.appendingPathComponent("TLAPS.tla")
                if FileManager.default.fileExists(atPath: tlapsFile.path) {
                    return libPath
                }
            }
            return nil
        }

        for root in Self.bundleResourceRoots() {
            if let found = firstValidStdlib(under: root) {
                return found
            }
        }

        // Check relative to tlapm binary (handles system-installed TLAPM via dune).
        if let tlapm = tlapmPath {
            let installPrefix = tlapm.deletingLastPathComponent().deletingLastPathComponent()
            if let found = firstValidStdlib(under: installPrefix) {
                return found
            }
        }

        return nil
    }

    /// All bundle roots that may contain our packaged resources.
    ///
    /// SPM's generated `Bundle.module` accessor only checks `Bundle.main.bundleURL` + the
    /// bundle name — it misses `Contents/Resources/TLAStudio_TLAStudioApp.bundle/`, which is
    /// where `build-app.sh` actually places the SPM bundle. So `Bundle.module` silently
    /// falls through to its build-time absolute path (e.g. `.build/.../release/...`). That
    /// means an installed .app still reaches into `.build/` for resources and breaks when
    /// `.build/` is deleted or the app is copied to another machine. We enumerate the
    /// nested SPM bundle under `Contents/Resources/` so lookups work regardless of what
    /// path `Bundle.module` resolved to.
    static func bundleResourceRoots() -> [URL] {
        let spmBundleName = "TLAStudio_TLAStudioApp.bundle"
        var roots: [URL] = []
        var seen = Set<String>()

        func append(_ url: URL) {
            let key = url.standardizedFileURL.path
            guard FileManager.default.fileExists(atPath: key), seen.insert(key).inserted else { return }
            roots.append(url)
        }

        // Use BinaryDiscovery's safe accessor, not SPM's `Bundle.module`: the latter
        // `fatalError`s in a distributed .app where the bundle lives under
        // Contents/Resources/ rather than the .app root or the build-time `.build/` path.
        if let modulePath = BinaryDiscovery.resourceBundle?.resourcePath {
            append(URL(fileURLWithPath: modulePath))
        }
        if let mainResources = Bundle.main.resourcePath {
            let mainURL = URL(fileURLWithPath: mainResources)
            append(mainURL.appendingPathComponent(spmBundleName))
            append(mainURL)
        }
        // Raw SPM exec with resource bundle alongside the executable.
        if let exec = Bundle.main.executableURL?.deletingLastPathComponent() {
            append(exec.appendingPathComponent(spmBundleName))
        }
        return roots
    }

    /// Matches TLAPM's "Executable "foo" not found" error surfaced via `@!!reason:`.
    /// The parser only captures the first line of `@!!reason:` so we look for this
    /// prefix (which is enough to disambiguate from a genuine proof failure).
    private static let executableNotFoundRegex = #"Executable "[^"]+" not found"#

    /// If any failed/timed-out obligation's reason indicates a missing tool, delete
    /// `.tlacache/<spec>.tlaps/fingerprints`. TLAPM caches the full failure reason and
    /// replays it with `@!!already:true` on subsequent runs — so once a fingerprint is
    /// poisoned by a tooling-environment error, it sticks even after the tool is
    /// installed, until the cache is cleared. `fingerprints.history/` is preserved.
    static func invalidateFingerprintsIfEnvironmentFailure(
        specURL: URL,
        obligations: [ProofObligation]
    ) {
        let hasEnvFailure = obligations.contains { obl in
            guard obl.status == .failed || obl.status == .timeout,
                  let msg = obl.errorMessage else { return false }
            return msg.range(of: executableNotFoundRegex, options: .regularExpression) != nil
        }
        guard hasEnvFailure else { return }

        let stem = specURL.deletingPathExtension().lastPathComponent
        let fingerprints = specURL.deletingLastPathComponent()
            .appendingPathComponent(".tlacache")
            .appendingPathComponent("\(stem).tlaps")
            .appendingPathComponent("fingerprints")

        guard FileManager.default.fileExists(atPath: fingerprints.path) else { return }
        do {
            try FileManager.default.removeItem(at: fingerprints)
            logger.warning("""
                Cleared TLAPM fingerprint cache at \(fingerprints.path): an obligation \
                failed with 'Executable not found', which is a tooling-environment error. \
                Re-run proof to recheck affected steps.
                """)
        } catch {
            logger.error("Failed to clear stale fingerprints at \(fingerprints.path): \(error.localizedDescription)")
        }
    }

    private var configuredModuleLibraryPaths: [URL] {
        BinaryDiscovery.configuredModuleLibraryDirectories()
    }

    private func appendLibrarySearchPaths(
        to args: inout [String],
        includeStdlib: Bool = true,
        additionalPaths: [URL] = []
    ) {
        var seen = Set<String>()

        for libraryPath in configuredModuleLibraryPaths {
            guard seen.insert(libraryPath.standardizedFileURL.path).inserted else { continue }
            args.append("-I")
            args.append(libraryPath.path)
        }

        for libraryPath in additionalPaths {
            guard FileManager.default.fileExists(atPath: libraryPath.path),
                  seen.insert(libraryPath.standardizedFileURL.path).inserted else { continue }
            args.append("-I")
            args.append(libraryPath.path)
        }

        if includeStdlib, let stdlib = stdlibPath,
           seen.insert(stdlib.standardizedFileURL.path).inserted {
            args.append("-I")
            args.append(stdlib.path)
        }
    }

    // MARK: - Prover Discovery

    /// Discovered paths to backend provers
    private var proverPaths: [ProverBackend: URL] = [:]

    /// Signature of the prover-path settings the cached `proverPaths` was built
    /// from; nil until the first scan. Re-scan only when it changes — the full
    /// ~6-backend filesystem sweep otherwise ran on every proof / single-step
    /// check (via buildTLAPMEnvironment) even though the prover set is static
    /// unless the user reconfigures a path.
    private var proverCacheSignature: String?

    /// The only mid-session-mutable inputs to discovery are the three configurable
    /// prover-path settings; everything else (bundle/system/home layout) is fixed
    /// for the app session. Keying the cache on their raw values never serves a
    /// stale path after the user reconfigures one.
    private func proverConfigSignature() -> String {
        let defaults = UserDefaults.standard
        return [UserSettings.Keys.zenonPath, UserSettings.Keys.z3Path, UserSettings.Keys.isabellePath]
            .map { defaults.string(forKey: $0) ?? "" }
            .joined(separator: "\u{1F}")
    }

    /// Discover paths to backend provers (cached; re-scans only when a configured
    /// prover path changes).
    private func discoverProvers() {
        let signature = proverConfigSignature()
        if proverCacheSignature == signature { return }

        proverPaths.removeAll()

        let provers: [(ProverBackend, String)] = [
            (.zenon, "zenon"),
            (.z3, "z3"),
            (.isabelle, "isabelle"),
            (.spass, "SPASS"),
            (.ls4, "ls4"),
            (.cvc5, "cvc5")
        ]

        for (backend, binaryName) in provers {
            if let path = findProverBinary(named: binaryName) {
                proverPaths[backend] = path
            }
        }

        proverCacheSignature = signature
    }

    private func findProverBinary(named name: String) -> URL? {
        switch name {
        case "zenon":
            if let configured = configuredExecutableURL(forKey: UserSettings.Keys.zenonPath) {
                return configured
            }
        case "z3":
            if let configured = configuredExecutableURL(forKey: UserSettings.Keys.z3Path) {
                return configured
            }
        case "isabelle":
            if let configured = configuredExecutableURL(
                forKey: UserSettings.Keys.isabellePath,
                appending: "bin/isabelle"
            ) {
                return configured
            }
        default:
            break
        }

        return BinaryDiscovery.find(
            named: name,
            options: .init(
                // Resource layout migrated from `lib/tlapm/backends/bin/` to a flat `bin/` dir;
                // check all three so either layout works until the bundle is fully normalized.
                bundleSubdirectories: ["bin", "Provers", "lib/tlapm/backends/bin"],
                systemPaths: ["/usr/local/bin", "/opt/homebrew/bin"],
                homeRelativePaths: [".tla/provers"]
            )
        )
    }

    /// Get available provers
    func availableProvers() -> [ProverBackend] {
        discoverProvers()
        return Array(proverPaths.keys).sorted { $0.rawValue < $1.rawValue }
    }

    /// Check if a specific prover is available
    func isProverAvailable(_ prover: ProverBackend) -> Bool {
        discoverProvers()
        return proverPaths[prover] != nil
    }

    // MARK: - Proof Checking

    /// Start a proof checking session for a specification
    /// - Parameters:
    ///   - specURL: URL to the TLA+ specification file
    ///   - options: Proof checking options
    ///   - sessionId: Unique identifier for this session
    ///   - progress: Callback for progress updates
    /// - Returns: Final result of proof checking
    func startProofCheck(
        spec specURL: URL,
        options: ProofCheckOptions = .default,
        sessionId: UUID = UUID(),
        progress: @escaping @Sendable (ProofCheckProgress) -> Void
    ) async throws -> ProofCheckResult {

        guard let tlapmPath = tlapmPath else {
            logger.error("TLAPM binary not found")
            throw TLAPMError.tlapmNotFound
        }

        logger.info("Using TLAPM at: \(tlapmPath.path)")
        logger.info("Spec URL: \(specURL.path)")
        if let stdlib = stdlibPath {
            logger.info("Using stdlib at: \(stdlib.path)")
        } else {
            logger.warning("TLAPS stdlib not found")
        }

        // Create parser
        let parser = TLAPMOutputParser()
        parser.setSessionId(sessionId)
        parser.setSpecFileURL(specURL)
        parsers[sessionId] = parser

        // Build arguments
        let arguments = buildArguments(for: options, specPath: specURL.path)
        logger.info("TLAPM arguments: \(arguments.joined(separator: " "))")

        // Create and configure process
        let process = Process()
        process.executableURL = tlapmPath
        process.arguments = arguments
        process.currentDirectoryURL = specURL.deletingLastPathComponent()

        // Set up minimal environment with prover paths
        let environment = buildTLAPMEnvironment()
        logger.debug("TLAPM environment PATH: \(environment["PATH"] ?? "nil")")
        process.environment = environment

        // Set up pipes
        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        process.standardOutput = stdoutPipe
        process.standardError = stderrPipe

        // Get file handles
        let stdoutHandle = stdoutPipe.fileHandleForReading
        let stderrHandle = stderrPipe.fileHandleForReading

        // Ensure handles are closed on error paths
        var processStarted = false
        defer {
            if !processStarted {
                try? stdoutHandle.close()
                try? stderrHandle.close()
            }
        }

        activeProcesses[sessionId] = process

        // Start time tracking
        let startTime = Date()

        // Create thread-safe stream state to prevent race conditions
        let streamState = StreamState<ProofCheckProgress>(throttle: .none)

        // Store state immediately (before AsyncStream to avoid race)
        streamStates[sessionId] = streamState

        // Signalled when each readability handler reads EOF, so the handlers are
        // the sole readers; teardown waits for these instead of a racy synchronous
        // availableData read (e2e M2).
        let stdoutEOF = DispatchSemaphore(value: 0)
        let stderrEOF = DispatchSemaphore(value: 0)

        // Create async stream for progress updates with proper termination
        let progressStream = AsyncStream<ProofCheckProgress> { continuation in
            // Store continuation in the thread-safe wrapper
            streamState.setContinuation(continuation)

            stdoutHandle.readabilityHandler = { [weak parser, weak streamState] handle in
                let data = handle.availableData
                if data.isEmpty {
                    // EOF reached. Self-clear the handler so a closed pipe can't keep firing.
                    handle.readabilityHandler = nil
                    stdoutEOF.signal()
                    return
                }
                guard let parser = parser, let state = streamState else { return }

                // Guard against yielding after stream is finished
                guard !state.isFinished else { return }

                // Log raw output to OutputManager
                if let str = String(data: data, encoding: .utf8) {
                    OutputManager.shared.logLines(str.nonEmptyOutputLines, source: .tlapm)
                }

                if let update = parser.parse(data) {
                    state.yield(update)
                }
            }

            stderrHandle.readabilityHandler = { [weak parser, weak streamState] handle in
                let data = handle.availableData
                if data.isEmpty {
                    handle.readabilityHandler = nil
                    stderrEOF.signal()
                    return
                }

                guard let parser = parser, let state = streamState else { return }

                // Guard against yielding after stream is finished
                guard !state.isFinished else { return }

                if let str = String(data: data, encoding: .utf8) {
                    // Log to OutputManager
                    OutputManager.shared.logLines(str.nonEmptyOutputLines, source: .tlapm)
                }

                // Parse stderr - TLAPM outputs proof results to stderr
                if let update = parser.parse(data) {
                    state.yield(update)
                }
            }

            continuation.onTermination = { _ in
                stdoutHandle.readabilityHandler = nil
                stderrHandle.readabilityHandler = nil
                // Unblock the teardown's bounded EOF wait if the stream is finished
                // externally (Stop / close) before the handlers observed EOF —
                // otherwise it parks for the full timeout (e2e Low).
                stdoutEOF.signal()
                stderrEOF.signal()
            }
        }

        // Start process
        let exitObserver = ProcessExitObserver()
        process.terminationHandler = { terminatedProcess in
            exitObserver.complete(status: terminatedProcess.terminationStatus)
        }

        do {
            try process.run()
            processStarted = true
            ProcessRegistry.shared.register(process, for: sessionId)
        } catch {
            process.terminationHandler = nil
            activeProcesses.removeValue(forKey: sessionId)
            parsers.removeValue(forKey: sessionId)
            streamStates.removeValue(forKey: sessionId)?.finish()
            throw TLAPMError.failedToStart(error)
        }

        // Send initial progress
        progress(ProofCheckProgress(
            sessionId: sessionId,
            phase: .parsing,
            totalObligations: 0,
            provedCount: 0,
            failedCount: 0,
            trivialCount: 0,
            currentObligation: nil,
            obligations: []
        ))

        // Forward progress updates in a tracked task
        let progressTask = Task {
            for await update in progressStream {
                progress(update)
            }
        }
        progressTasks[sessionId] = progressTask

        // Wait for completion using async termination handler
        let exitStatus = await exitObserver.wait(for: process)
        process.terminationHandler = nil

        // Single-reader invariant (e2e M2): the readability handlers are the sole
        // readers; wait (off the cooperative pool, bounded) for them to reach EOF
        // so the streamed tail is fully parsed/logged before teardown. Replaces a
        // synchronous availableData read that raced a still-live handler.
        await withCheckedContinuation { (cont: CheckedContinuation<Void, Never>) in
            DispatchQueue.global(qos: .userInitiated).async {
                let deadline = DispatchTime.now() + 3
                _ = stdoutEOF.wait(timeout: deadline)
                _ = stderrEOF.wait(timeout: deadline)
                cont.resume()
            }
        }

        // Handlers self-cleared on EOF; clear again (idempotent) and close.
        stdoutHandle.readabilityHandler = nil
        stderrHandle.readabilityHandler = nil
        try? stdoutHandle.close()
        try? stderrHandle.close()

        // Identity-gated teardown (e2e M3): unlike TLC (fresh id per run), a
        // ProofSession reuses its fixed id, so a Stop → Run-again can register a
        // new process under this sessionId while this stale tail is parked in the
        // await above. Always finish OUR OWN stream/progress task, but reclaim the
        // shared registry/dicts only if we still own the slot — otherwise we'd
        // unregister (orphan) the newer run's process.
        let weStillOwnSlot = activeProcesses[sessionId] === process
        streamState.finish()
        progressTask.cancel()
        if weStillOwnSlot {
            streamStates.removeValue(forKey: sessionId)
            progressTasks.removeValue(forKey: sessionId)
            ProcessRegistry.shared.unregister(sessionId)
            activeProcesses.removeValue(forKey: sessionId)
        }

        let duration = Date().timeIntervalSince(startTime)
        let trivialCount = parser.getTrivialCount()  // Get before finalResult
        let result = parser.finalResult(exitCode: exitStatus, duration: duration)

        // Drop TLAPM's fingerprint cache if any obligation failed with a tooling-environment
        // error (e.g. "Executable 'ls4' not found"). TLAPM stores the reason in the cache
        // and replays it with @!!already:true next run, so even after the tool is installed
        // the old failure persists until the cache is cleared.
        Self.invalidateFingerprintsIfEnvironmentFailure(
            specURL: specURL,
            obligations: result.obligations
        )

        if weStillOwnSlot {
            parsers.removeValue(forKey: sessionId)
        }

        // Send final progress with actual trivial count
        progress(ProofCheckProgress(
            sessionId: sessionId,
            phase: result.success ? .done : .error,
            totalObligations: result.obligations.count,
            provedCount: result.provedCount,
            failedCount: result.failedCount,
            trivialCount: trivialCount,
            currentObligation: nil,
            obligations: result.obligations
        ))

        return result
    }

    /// Check a single proof step at a specific location
    /// - Parameters:
    ///   - specURL: URL to the TLA+ specification file
    ///   - line: Line number of the proof step
    ///   - column: Column number of the proof step
    ///   - backend: Optional specific prover to use
    ///   - timeout: Timeout for the proof attempt
    /// - Returns: The proof obligation result
    func checkSingleStep(
        spec specURL: URL,
        line: Int,
        column: Int,
        backend: ProverBackend? = nil,
        timeout: TimeInterval = 30,
        sessionId: UUID = UUID(),
        additionalLibraryPaths: [URL] = []
    ) async throws -> ProofObligation {

        logger.info("checkSingleStep: line=\(line), column=\(column), sessionId=\(sessionId.uuidString)")

        guard let tlapmPath = tlapmPath else {
            logger.error("TLAPM binary not found for single step check")
            throw TLAPMError.tlapmNotFound
        }

        logger.info("Checking single step at line \(line), column \(column)")

        // Create parser
        let parser = TLAPMOutputParser()
        parser.setSessionId(sessionId)
        parser.setSpecFileURL(specURL)

        // Build arguments for single step
        var arguments: [String] = []

        appendLibrarySearchPaths(to: &arguments, additionalPaths: additionalLibraryPaths)

        // Toolbox mode with line range (check just this line)
        arguments.append("--toolbox")
        arguments.append("\(line)")
        arguments.append("\(line)")

        // Also use --line to focus on specific line
        arguments.append("--line")
        arguments.append("\(line)")

        // Single thread for step checking
        arguments.append("--threads")
        arguments.append("1")

        if let backend = backend {
            arguments.append(contentsOf: backend.tlapmArgument.split(separator: " ").map(String.init))
        }

        // Use stretch for timeout (default ~10s per obligation)
        if timeout > 10 {
            let stretchFactor = max(1.0, timeout / 10.0)
            arguments.append("--stretch")
            arguments.append(String(format: "%.1f", stretchFactor))
        }

        arguments.append(specURL.path)

        logger.info("Single step arguments: \(arguments.joined(separator: " "))")

        let startTime = Date()

        logger.info("checkSingleStep: Starting TLAPM process")

        // Track the step session so stopAll/isRunning/activeSessionCount cover it.
        // Unlike the streaming path we never store into `activeProcesses` — the
        // runner owns the Process — which also means a step check can no longer
        // clobber a streaming session's entry if the ids ever collide.
        activeStepSessions.insert(sessionId)
        defer { activeStepSessions.remove(sessionId) }

        // One-shot spawn/drain/timeout via the shared runner. It registers the
        // process with ProcessRegistry under `sessionId`, so `stop(sessionId:)` and
        // ProofSession's per-step terminate calls still reach the child. Tail-keep
        // truncation: if output ever exceeds the cap, the latest obligation results
        // are the ones worth keeping.
        let stdoutData: Data
        let stderrData: Data
        do {
            let result = try await SubprocessRunner.run(
                executableURL: tlapmPath,
                arguments: arguments,
                currentDirectoryURL: specURL.deletingLastPathComponent(),
                timeout: timeout,
                environment: buildTLAPMEnvironment(),
                registryId: sessionId,
                stdoutPolicy: .keepTail(limit: SubprocessRunner.maxCapturedBytes),
                stderrPolicy: .keepTail(limit: SubprocessRunner.maxCapturedBytes),
                onStderrData: { data in
                    // Live-log TLAPM's stderr (its primary output channel) to the Output panel.
                    if let str = String(data: data, encoding: .utf8) {
                        OutputManager.shared.logLines(str.nonEmptyOutputLines, source: .tlapm)
                    }
                }
            )
            stdoutData = result.stdout
            stderrData = result.stderr
            logger.info("checkSingleStep: Process exited with status \(result.terminationStatus)")
        } catch is SubprocessRunner.TimeoutError {
            logger.error("checkSingleStep: Process timed out after \(String(format: "%.1f", timeout))s")
            throw TLAPMError.timeout
        } catch is CancellationError {
            throw CancellationError()
        } catch {
            logger.error("checkSingleStep: Failed to start process: \(error.localizedDescription)")
            throw TLAPMError.failedToStart(error)
        }

        // Parse accumulated output - TLAPM outputs to stderr in toolbox mode
        _ = parser.parse(stdoutData)
        _ = parser.parse(stderrData)

        let duration = Date().timeIntervalSince(startTime)
        let obligations = parser.getAllObligations()

        Self.invalidateFingerprintsIfEnvironmentFailure(
            specURL: specURL,
            obligations: obligations
        )

        // Find the obligation matching our line
        if let obligation = obligations.first(where: { obl in
            obl.location.contains(line: line, column: column)
        }) {
            return obligation
        }

        let sameLineObligations = obligations.filter { obligation in
            line >= obligation.location.startLine && line <= obligation.location.endLine
        }
        if let nearestObligation = sameLineObligations.min(by: { lhs, rhs in
            distance(from: lhs.location, toLine: line, column: column) <
                distance(from: rhs.location, toLine: line, column: column)
        }) {
            return nearestObligation
        }

        // No obligation found - create a pending one
        return ProofObligation(
            id: UUID(),
            fingerprint: "fp_single_\(line)_\(column)",
            location: ProofSourceLocation(
                fileURL: specURL,
                startLine: line,
                startColumn: column,
                endLine: line,
                endColumn: column
            ),
            kind: .step,
            status: .pending,
            backend: backend,
            duration: duration,
            errorMessage: "No proof obligation found at specified location",
            parent: nil,
            children: [],
            obligationText: ""
        )
    }

    private func distance(from location: ProofSourceLocation, toLine line: Int, column: Int) -> Int {
        if line < location.startLine {
            return (location.startLine - line) * 10_000 + location.startColumn
        }
        if line > location.endLine {
            return (line - location.endLine) * 10_000 + location.endColumn
        }
        if line == location.startLine && column < location.startColumn {
            return location.startColumn - column
        }
        if line == location.endLine && column > location.endColumn {
            return column - location.endColumn
        }
        return 0
    }

    // MARK: - Process Control

    /// Stop a running proof check
    func stop(sessionId: UUID) {
        // Cancel progress task first
        progressTasks.removeValue(forKey: sessionId)?.cancel()

        // Mark stream as finished and clean up
        streamStates.removeValue(forKey: sessionId)?.finish()

        // Terminate the process using the registry (synchronous)
        ProcessRegistry.shared.terminate(sessionId)
        activeProcesses.removeValue(forKey: sessionId)
        parsers.removeValue(forKey: sessionId)
    }

    /// Stop all running proof checks
    func stopAll() {
        // Cancel all progress tasks
        for (_, task) in progressTasks {
            task.cancel()
        }
        progressTasks.removeAll()

        // Finish all streams
        for (_, state) in streamStates {
            state.finish()
        }
        streamStates.removeAll()

        // Terminate all processes using the registry
        for (sessionId, _) in activeProcesses {
            ProcessRegistry.shared.terminate(sessionId)
        }
        activeProcesses.removeAll()

        // In-flight single-step checks live in ProcessRegistry under their session id.
        for sessionId in activeStepSessions {
            ProcessRegistry.shared.terminate(sessionId)
        }

        parsers.removeAll()
    }

    /// Check if a session is running
    func isRunning(sessionId: UUID) -> Bool {
        if let process = activeProcesses[sessionId] {
            return process.isRunning
        }
        // Single-step sessions: the Process is owned by SubprocessRunner; the
        // registry tracks liveness under the same session id.
        return activeStepSessions.contains(sessionId) && ProcessRegistry.shared.isRunning(sessionId)
    }

    /// Get the number of active sessions
    var activeSessionCount: Int {
        activeProcesses.count + activeStepSessions.count
    }

    /// Polling wait for process exit. No longer used by `checkSingleStep` (which now
    /// goes through `SubprocessRunner`'s terminationHandler-based wait); retained only
    /// because `TLAPMProcessManagerTests` pins its timeout behavior directly. Candidate
    /// for deletion together with those two tests.
    static func waitForExit(of process: Process, timeout: TimeInterval? = nil) async throws -> Int32 {
        let startTime = Date()

        while process.isRunning {
            if let timeout, Date().timeIntervalSince(startTime) >= timeout {
                throw TLAPMError.timeout
            }
            try await Task.sleep(nanoseconds: 50_000_000)
        }

        return process.terminationStatus
    }

    // MARK: - Environment Building

    /// Build a minimal environment with prover paths prepended to PATH.
    /// Used by both `startProofCheck` and `checkSingleStep`.
    private func buildTLAPMEnvironment() -> [String: String] {
        var environment = ProcessEnvironment.minimal()

        // Add discovered prover env vars AND collect their parent directories into PATH.
        // TLAPM shells out `type zenon` / `type z3` etc., so those executables must be on
        // PATH regardless of which subdirectory BinaryDiscovery ultimately found them in.
        discoverProvers()
        var discoveredDirs: [String] = []
        for (prover, path) in proverPaths {
            let envVar = "\(prover.rawValue.uppercased())_PATH"
            let parentDir = path.deletingLastPathComponent().path
            environment[envVar] = parentDir
            if !discoveredDirs.contains(parentDir) {
                discoveredDirs.append(parentDir)
            }
        }

        // Add backend prover paths to PATH for TLAPM discovery. Both old
        // (`lib/tlapm/backends/bin`) and new (`bin`) layouts are supported so we don't
        // break users on either build. `Provers/` is the historical prover dir.
        var pathComponents: [String] = discoveredDirs
        for root in Self.bundleResourceRoots() {
            for subdir in ["bin", "Provers", "lib/tlapm/backends/bin"] {
                let candidate = root.appendingPathComponent(subdir).path
                if FileManager.default.fileExists(atPath: candidate),
                   !pathComponents.contains(candidate) {
                    pathComponents.append(candidate)
                }
            }
        }

        if !pathComponents.isEmpty {
            let existingPath = environment["PATH"] ?? "/usr/bin:/bin"
            pathComponents.append(existingPath)
            environment["PATH"] = pathComponents.joined(separator: ":")
        }

        return environment
    }

    // MARK: - Argument Building

    private func buildArguments(for options: ProofCheckOptions, specPath: String) -> [String] {
        var args: [String] = []

        appendLibrarySearchPaths(to: &args, additionalPaths: options.additionalLibraryPaths ?? [])

        // Toolbox mode for machine-readable output
        // --toolbox <start> <end> specifies line range (0 means start/end of file)
        args.append("--toolbox")
        args.append("\(options.checkFromLine ?? 1)")
        args.append("\(options.checkToLine ?? 0)")

        // Thread count
        args.append("--threads")
        args.append("\(options.threads)")

        // Timeout multiplier (stretch factor)
        // TLAPM uses --stretch to multiply default timeouts
        if options.timeout > 10 {
            // Use stretch factor based on timeout (default is ~10s per obligation)
            let stretchFactor = max(1.0, options.timeout / 10.0)
            args.append("--stretch")
            args.append(String(format: "%.1f", stretchFactor))
        }

        // Backend prover selection
        if let backend = options.backend {
            args.append(contentsOf: backend.tlapmArgument.split(separator: " ").map(String.init))
        }

        // Fingerprinting for caching
        // Use --safefp to verify prover versions match for fingerprints
        if options.fingerprints {
            args.append("--safefp")
        }

        // Verbose output
        if options.verbose {
            args.append("--verbose")
        }

        // Single line restriction (--toolbox already handles ranges)
        if options.checkFromLine != nil && options.checkFromLine == options.checkToLine {
            if let line = options.checkFromLine {
                args.append("--line")
                args.append("\(line)")
            }
        }

        // Specification file (must be last)
        args.append(specPath)

        return args
    }
}

// MARK: - TLAPM Errors

enum TLAPMError: Error, LocalizedError {
    case tlapmNotFound
    case failedToStart(Error)
    case specNotFound
    case proverNotFound(ProverBackend)
    case parseError(String)
    case timeout
    case cancelled
    case invalidLocation(line: Int, column: Int)

    var errorDescription: String? {
        switch self {
        case .tlapmNotFound:
            return "TLAPM proof manager not found. Please ensure TLAPM is installed."
        case .failedToStart(let error):
            return "Failed to start TLAPM: \(error.localizedDescription)"
        case .specNotFound:
            return "Specification file not found."
        case .proverNotFound(let prover):
            return "Backend prover '\(prover.displayName)' not found."
        case .parseError(let message):
            return "Failed to parse TLAPM output: \(message)"
        case .timeout:
            return "Proof checking timed out."
        case .cancelled:
            return "Proof checking was cancelled."
        case .invalidLocation(let line, let column):
            return "Invalid location: line \(line), column \(column)"
        }
    }
}
