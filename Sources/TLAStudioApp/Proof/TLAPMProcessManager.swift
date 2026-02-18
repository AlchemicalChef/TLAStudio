import Foundation
import os

private let logger = Log.logger(category: "TLAPM")

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


    // MARK: - Binary Discovery

    /// Path to TLAPM binary
    private var tlapmPath: URL? {
        BinaryDiscovery.find(
            named: "tlapm",
            options: .init(
                bundleSubdirectories: ["bin"],
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
        // Check app bundle Resources/lib/tlapm/stdlib
        if let bundlePath = Bundle.main.resourcePath {
            let libPath = URL(fileURLWithPath: bundlePath)
                .appendingPathComponent("lib/tlapm/stdlib")
            if FileManager.default.fileExists(atPath: libPath.path) {
                return libPath
            }
        }

        // Check relative to tlapm binary
        if let tlapm = tlapmPath {
            let relativePath = tlapm.deletingLastPathComponent()
                .deletingLastPathComponent()
                .appendingPathComponent("lib/tlapm/stdlib")
            if FileManager.default.fileExists(atPath: relativePath.path) {
                return relativePath
            }
        }

        return nil
    }

    // MARK: - Prover Discovery

    /// Discovered paths to backend provers
    private var proverPaths: [ProverBackend: URL] = [:]

    /// Discover paths to backend provers
    private func discoverProvers() {
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
    }

    private func findProverBinary(named name: String) -> URL? {
        BinaryDiscovery.find(
            named: name,
            options: .init(
                bundleSubdirectories: ["Provers"],
                systemPaths: ["/usr/local/bin", "/opt/homebrew/bin"],
                homeRelativePaths: [".tla/provers"]
            )
        )
    }

    /// Get available provers
    func availableProvers() -> [ProverBackend] {
        if proverPaths.isEmpty {
            discoverProvers()
        }
        return Array(proverPaths.keys).sorted { $0.rawValue < $1.rawValue }
    }

    /// Check if a specific prover is available
    func isProverAvailable(_ prover: ProverBackend) -> Bool {
        if proverPaths.isEmpty {
            discoverProvers()
        }
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

        // Create async stream for progress updates with proper termination
        let progressStream = AsyncStream<ProofCheckProgress> { continuation in
            // Store continuation in the thread-safe wrapper
            streamState.setContinuation(continuation)

            stdoutHandle.readabilityHandler = { [weak parser, weak streamState] handle in
                let data = handle.availableData
                if data.isEmpty {
                    // EOF reached
                    return
                }
                guard let parser = parser, let state = streamState else { return }

                // Guard against yielding after stream is finished
                guard !state.isFinished else { return }

                // Log raw output to OutputManager
                if let str = String(data: data, encoding: .utf8) {
                    for line in str.components(separatedBy: .newlines) where !line.isEmpty {
                        DispatchQueue.main.async {
                            OutputManager.shared.logTLAPM(line)
                        }
                    }
                }

                if let update = parser.parse(data) {
                    state.yield(update)
                }
            }

            stderrHandle.readabilityHandler = { [weak parser, weak streamState] handle in
                let data = handle.availableData
                if data.isEmpty { return }

                guard let parser = parser, let state = streamState else { return }

                // Guard against yielding after stream is finished
                guard !state.isFinished else { return }

                if let str = String(data: data, encoding: .utf8) {
                    // Log to OutputManager
                    for line in str.components(separatedBy: .newlines) where !line.isEmpty {
                        DispatchQueue.main.async {
                            OutputManager.shared.logTLAPM(line, isError: false)
                        }
                    }
                }

                // Parse stderr - TLAPM outputs proof results to stderr
                if let update = parser.parse(data) {
                    state.yield(update)
                }
            }

            continuation.onTermination = { _ in
                stdoutHandle.readabilityHandler = nil
                stderrHandle.readabilityHandler = nil
            }
        }

        // Start process
        do {
            try process.run()
            processStarted = true
            ProcessRegistry.shared.register(process, for: sessionId)
        } catch {
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
        let exitStatus = await withCheckedContinuation { (continuation: CheckedContinuation<Int32, Never>) in
            process.terminationHandler = { terminatedProcess in
                continuation.resume(returning: terminatedProcess.terminationStatus)
            }
        }

        // Drain any remaining buffered data before clearing handlers.
        // readabilityHandler may not fire for data already in the pipe buffer
        // after process exit, so we must read it synchronously.
        let lastStdout = stdoutHandle.availableData
        if !lastStdout.isEmpty {
            if let str = String(data: lastStdout, encoding: .utf8) {
                for line in str.components(separatedBy: .newlines) where !line.isEmpty {
                    DispatchQueue.main.async {
                        OutputManager.shared.logTLAPM(line)
                    }
                }
            }
            if let update = parser.parse(lastStdout) {
                streamState.yield(update)
            }
        }
        let lastStderr = stderrHandle.availableData
        if !lastStderr.isEmpty {
            if let str = String(data: lastStderr, encoding: .utf8) {
                for line in str.components(separatedBy: .newlines) where !line.isEmpty {
                    DispatchQueue.main.async {
                        OutputManager.shared.logTLAPM(line, isError: false)
                    }
                }
            }
            if let update = parser.parse(lastStderr) {
                streamState.yield(update)
            }
        }

        // Now safe to clear handlers and close
        stdoutHandle.readabilityHandler = nil
        stderrHandle.readabilityHandler = nil
        try? stdoutHandle.close()
        try? stderrHandle.close()

        // Mark stream as finished and clean up
        streamStates.removeValue(forKey: sessionId)?.finish()

        // Cancel progress task
        progressTasks.removeValue(forKey: sessionId)?.cancel()

        // Unregister process and clean up
        ProcessRegistry.shared.unregister(sessionId)
        activeProcesses.removeValue(forKey: sessionId)

        let duration = Date().timeIntervalSince(startTime)
        let trivialCount = parser.getTrivialCount()  // Get before finalResult
        let result = parser.finalResult(exitCode: exitStatus, duration: duration)

        parsers.removeValue(forKey: sessionId)

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
        sessionId: UUID = UUID()
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

        // Add TLAPS standard library path
        if let stdlib = stdlibPath {
            arguments.append("-I")
            arguments.append(stdlib.path)
        }

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

        // Create process
        let process = Process()
        process.executableURL = tlapmPath
        process.arguments = arguments
        process.currentDirectoryURL = specURL.deletingLastPathComponent()

        // Set up minimal environment with prover paths
        process.environment = buildTLAPMEnvironment()

        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        process.standardOutput = stdoutPipe
        process.standardError = stderrPipe

        let stdoutHandle = stdoutPipe.fileHandleForReading
        let stderrHandle = stderrPipe.fileHandleForReading

        // Ensure handles are closed on all paths
        defer {
            try? stdoutHandle.close()
            try? stderrHandle.close()
        }

        activeProcesses[sessionId] = process

        let startTime = Date()

        logger.info("checkSingleStep: Starting TLAPM process")

        // Accumulate output data using thread-safe storage
        // (pipes must be drained while process runs to avoid deadlock)
        let outputAccumulator = OutputAccumulator()

        // Set up readability handlers to drain pipes and prevent deadlock
        stdoutHandle.readabilityHandler = { [weak outputAccumulator] handle in
            let data = handle.availableData
            if !data.isEmpty {
                outputAccumulator?.appendStdout(data)
            }
        }

        stderrHandle.readabilityHandler = { [weak outputAccumulator] handle in
            let data = handle.availableData
            if !data.isEmpty {
                outputAccumulator?.appendStderr(data)
                // Log to output manager
                if let str = String(data: data, encoding: .utf8) {
                    for line in str.components(separatedBy: .newlines) where !line.isEmpty {
                        DispatchQueue.main.async {
                            OutputManager.shared.logTLAPM(line)
                        }
                    }
                }
            }
        }

        // Run process
        do {
            try process.run()
            ProcessRegistry.shared.register(process, for: sessionId)
            logger.info("checkSingleStep: Process started with PID \(process.processIdentifier)")
        } catch {
            stdoutHandle.readabilityHandler = nil
            stderrHandle.readabilityHandler = nil
            activeProcesses.removeValue(forKey: sessionId)
            logger.error("checkSingleStep: Failed to start process: \(error.localizedDescription)")
            throw TLAPMError.failedToStart(error)
        }

        // Wait for process to complete using async termination handler
        let exitStatus = await withCheckedContinuation { (continuation: CheckedContinuation<Int32, Never>) in
            process.terminationHandler = { terminatedProcess in
                continuation.resume(returning: terminatedProcess.terminationStatus)
            }
        }

        logger.info("checkSingleStep: Process exited with status \(exitStatus)")

        // Drain any remaining buffered pipe data before clearing handlers
        let lastStdout = stdoutHandle.availableData
        if !lastStdout.isEmpty {
            outputAccumulator.appendStdout(lastStdout)
        }
        let lastStderr = stderrHandle.availableData
        if !lastStderr.isEmpty {
            outputAccumulator.appendStderr(lastStderr)
        }

        // Clean up handlers
        stdoutHandle.readabilityHandler = nil
        stderrHandle.readabilityHandler = nil

        // Clean up process tracking
        ProcessRegistry.shared.unregister(sessionId)
        activeProcesses.removeValue(forKey: sessionId)

        // Get accumulated output and parse it
        let stdoutData = outputAccumulator.getStdout()
        let stderrData = outputAccumulator.getStderr()

        // Parse accumulated output - TLAPM outputs to stderr in toolbox mode
        _ = parser.parse(stdoutData)
        _ = parser.parse(stderrData)

        let duration = Date().timeIntervalSince(startTime)
        let obligations = parser.getAllObligations()

        // Find the obligation matching our line
        if let obligation = obligations.first(where: { obl in
            obl.location.contains(line: line, column: column)
        }) {
            return obligation
        }

        // If no specific obligation found, check if there's any result
        if let firstObligation = obligations.first {
            return firstObligation
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
        parsers.removeAll()
    }

    /// Check if a session is running
    func isRunning(sessionId: UUID) -> Bool {
        activeProcesses[sessionId]?.isRunning ?? false
    }

    /// Get the number of active sessions
    var activeSessionCount: Int {
        activeProcesses.count
    }

    // MARK: - Environment Building

    /// Build a minimal environment with prover paths prepended to PATH.
    /// Used by both `startProofCheck` and `checkSingleStep`.
    private func buildTLAPMEnvironment() -> [String: String] {
        var environment = ProcessEnvironment.minimal()

        // Add discovered prover env vars
        if proverPaths.isEmpty {
            discoverProvers()
        }
        for (prover, path) in proverPaths {
            let envVar = "\(prover.rawValue.uppercased())_PATH"
            environment[envVar] = path.deletingLastPathComponent().path
        }

        // Add backend prover paths to PATH for TLAPM discovery
        var pathComponents: [String] = []
        if let bundlePath = Bundle.main.resourcePath {
            let backendsPath = URL(fileURLWithPath: bundlePath)
                .appendingPathComponent("lib/tlapm/backends/bin").path
            if FileManager.default.fileExists(atPath: backendsPath) {
                pathComponents.append(backendsPath)
            }
            let proversPath = URL(fileURLWithPath: bundlePath)
                .appendingPathComponent("Provers").path
            if FileManager.default.fileExists(atPath: proversPath) {
                pathComponents.append(proversPath)
            }
            let binPath = URL(fileURLWithPath: bundlePath)
                .appendingPathComponent("bin").path
            if FileManager.default.fileExists(atPath: binPath) {
                pathComponents.append(binPath)
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

        // Add TLAPS standard library path
        if let stdlib = stdlibPath {
            args.append("-I")
            args.append(stdlib.path)
        }

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

// MARK: - Output Accumulator

/// Thread-safe accumulator for process output data.
/// Used to collect stdout/stderr while process runs to prevent pipe deadlock.
/// Limits buffer size to prevent unbounded memory growth.
/// @unchecked Sendable: thread safety ensured by NSLock
private final class OutputAccumulator: @unchecked Sendable {
    private let lock = NSLock()
    private var _stdout = Data()
    private var _stderr = Data()

    /// Maximum buffer size per stream (10MB) to prevent OOM
    private static let maxBufferSize = 10 * 1024 * 1024

    func appendStdout(_ data: Data) {
        lock.lock()
        defer { lock.unlock() }
        // Enforce buffer limit: keep last maxBufferSize bytes if exceeded
        if _stdout.count + data.count > Self.maxBufferSize {
            let overflow = (_stdout.count + data.count) - Self.maxBufferSize
            if overflow < _stdout.count {
                _stdout = Data(_stdout.suffix(_stdout.count - overflow))
            } else {
                _stdout = Data()
            }
        }
        _stdout.append(data)
    }

    func appendStderr(_ data: Data) {
        lock.lock()
        defer { lock.unlock() }
        // Enforce buffer limit: keep last maxBufferSize bytes if exceeded
        if _stderr.count + data.count > Self.maxBufferSize {
            let overflow = (_stderr.count + data.count) - Self.maxBufferSize
            if overflow < _stderr.count {
                _stderr = Data(_stderr.suffix(_stderr.count - overflow))
            } else {
                _stderr = Data()
            }
        }
        _stderr.append(data)
    }

    func getStdout() -> Data {
        lock.lock()
        defer { lock.unlock() }
        return _stdout
    }

    func getStderr() -> Data {
        lock.lock()
        defer { lock.unlock() }
        return _stderr
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

