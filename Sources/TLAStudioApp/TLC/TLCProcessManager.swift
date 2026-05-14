import Foundation
import os

private let logger = Log.logger(category: "TLC")

private extension String {
    var nonEmptyOutputLines: [String] {
        components(separatedBy: .newlines).filter { !$0.isEmpty }
    }
}

// MARK: - TLC Process Manager

/// Actor that manages TLC model checking processes
actor TLCProcessManager {
    static let shared = TLCProcessManager()

    // MARK: - State

    private var activeProcesses: [UUID: Process] = [:]
    private var parsers: [UUID: TLCOutputParser] = [:]
    private var progressTasks: [UUID: Task<Void, Never>] = [:]
    private var streamStates: [UUID: StreamState<ModelCheckProgress>] = [:]

    /// Cached Java path to avoid blocking `which java` calls (Issue #12)
    private var cachedJavaPath: URL?
    private var javaPathCacheValid = false

    /// Binary selection mode
    enum TLCBinaryMode {
        case fast      // Epsilon GC - no GC overhead, OOMs on very large specs
        case standard  // SerialGC+PGO - handles any size, ~40% GC overhead
        case auto      // Auto-select based on estimated state space
        case jvm       // Full JVM with tla2tools.jar - no 32GB limit, 2-3s startup
    }

    /// Threshold for auto-selecting standard binary (estimated states)
    /// Above this, we use SerialGC to avoid OOM with Epsilon GC
    private let autoSelectThreshold = 500_000

    private var configuredTLCPath: URL? {
        let configuredPath = UserSettings.shared.tlcPath
            .trimmingCharacters(in: .whitespacesAndNewlines)
        guard !configuredPath.isEmpty else { return nil }

        let url = URL(fileURLWithPath: configuredPath)
        guard FileManager.default.fileExists(atPath: url.path),
              FileManager.default.isExecutableFile(atPath: url.path) else {
            return nil
        }
        return url
    }

    /// Find a TLC binary by name
    private func findBinary(named name: String) -> URL? {
        BinaryDiscovery.find(named: name)
    }

    /// Path to fast TLC binary (Epsilon GC - best for small/medium specs)
    private var tlcFastPath: URL? {
        findBinary(named: "tlc-native-fast")
    }

    /// Path to standard TLC binary (SerialGC+PGO - best for large specs)
    private var tlcStandardPath: URL? {
        findBinary(named: "tlc-native")
    }

    /// Path to TLC binary (prefers fast, falls back to standard)
    private var tlcPath: URL? {
        configuredTLCPath ?? tlcFastPath ?? tlcStandardPath
    }

    /// Get the discovered TLC path for display and tests.
    var discoveredTLCPath: String? {
        tlcPath?.path
    }

    /// Path to tla2tools.jar for JVM fallback
    private var tla2toolsJarPath: URL? {
        BinaryDiscovery.find(
            named: "tla2tools",
            extension: "jar",
            options: .init(
                systemPaths: ["/usr/local/lib", "/usr/local/bin"],
                homeRelativePaths: [".tla"]
            )
        ) ?? BinaryDiscovery.findDevelopmentFile(relativePath: "Scripts/tla2tools.jar")
    }

    /// Path to Java executable (cached to avoid blocking actor with `which java`)
    /// FIX: Changed to async to avoid blocking the actor's executor during first lookup
    private func getJavaPath() async -> URL? {
        if javaPathCacheValid {
            return cachedJavaPath
        }
        let result = await lookupJavaPathAsync()
        cachedJavaPath = result
        javaPathCacheValid = true
        return result
    }

    /// Invalidate Java path cache (call if environment changes)
    func invalidateJavaPathCache() {
        javaPathCacheValid = false
        cachedJavaPath = nil
    }

    /// Perform the actual Java path lookup asynchronously
    /// FIX: Runs blocking `which java` process on a background thread to avoid blocking actor
    private func lookupJavaPathAsync() async -> URL? {
        // Check JAVA_HOME first (Issue #8: validate it's a real Java installation)
        // This is fast - just filesystem checks, no process spawning
        if let javaHome = ProcessInfo.processInfo.environment["JAVA_HOME"] {
            let javaExe = URL(fileURLWithPath: javaHome).appendingPathComponent("bin/java")
            let releaseFile = URL(fileURLWithPath: javaHome).appendingPathComponent("release")
            let libDir = URL(fileURLWithPath: javaHome).appendingPathComponent("lib")
            if FileManager.default.fileExists(atPath: javaExe.path) &&
               FileManager.default.isExecutableFile(atPath: javaExe.path) &&
               (FileManager.default.fileExists(atPath: releaseFile.path) ||
                FileManager.default.fileExists(atPath: libDir.path)) {
                return javaExe
            }
            logger.warning("JAVA_HOME set but doesn't appear to be a valid Java installation: \(javaHome)")
        }

        // Run `which java` on a background thread to avoid blocking the actor
        // Use readability handler to drain pipe BEFORE waitUntilExit to prevent deadlock
        return await withCheckedContinuation { continuation in
            DispatchQueue.global(qos: .userInitiated).async {
                let process = Process()
                process.executableURL = URL(fileURLWithPath: "/usr/bin/which")
                process.arguments = ["java"]
                let pipe = Pipe()
                process.standardOutput = pipe
                process.standardError = FileHandle.nullDevice

                // Accumulate output while process runs to prevent pipe buffer deadlock
                var outputData = Data()
                let outputLock = NSLock()
                pipe.fileHandleForReading.readabilityHandler = { handle in
                    let data = handle.availableData
                    if !data.isEmpty {
                        outputLock.lock()
                        outputData.append(data)
                        outputLock.unlock()
                    }
                }

                do {
                    try process.run()
                    process.waitUntilExit()

                    // Clean up handler
                    pipe.fileHandleForReading.readabilityHandler = nil
                    try? pipe.fileHandleForReading.close()

                    outputLock.lock()
                    let finalData = outputData
                    outputLock.unlock()

                    if let path = String(data: finalData, encoding: .utf8)?.trimmingCharacters(in: .whitespacesAndNewlines),
                       !path.isEmpty {
                        continuation.resume(returning: URL(fileURLWithPath: path))
                        return
                    }
                } catch {
                    pipe.fileHandleForReading.readabilityHandler = nil
                    try? pipe.fileHandleForReading.close()
                }
                continuation.resume(returning: nil)
            }
        }
    }

    /// Check if JVM fallback is available
    var isJVMAvailable: Bool {
        get async {
            await getJavaPath() != nil && tla2toolsJarPath != nil
        }
    }

    /// Select the appropriate TLC binary based on mode and config
    /// Returns nil for .jvm mode (JVM uses java executable instead)
    private func selectBinary(mode: TLCBinaryMode, config: ModelConfig) -> URL? {
        if let configuredTLCPath {
            return configuredTLCPath
        }

        switch mode {
        case .fast:
            return tlcFastPath ?? tlcStandardPath
        case .standard:
            return tlcStandardPath ?? tlcFastPath
        case .auto:
            let estimatedStates = estimateStateSpace(config: config)
            if estimatedStates > autoSelectThreshold {
                return tlcStandardPath ?? tlcFastPath
            } else {
                return tlcFastPath ?? tlcStandardPath
            }
        case .jvm:
            // JVM mode uses java executable, not native binary
            return nil
        }
    }

    /// Estimate state space size based on config constants
    /// This is a rough heuristic - actual state space can vary wildly
    /// Note: Made internal for testability
    func estimateStateSpace(config: ModelConfig) -> Int {
        let cap = 100_000_000
        var estimate = 1

        for (_, constantValue) in config.constants {
            let multiplier = estimateConstantImpact(constantValue)

            // Check for overflow before multiplication
            if multiplier > 0 && estimate > cap / multiplier {
                return cap
            }
            estimate *= multiplier

            // Cap to avoid overflow
            if estimate > cap {
                return cap
            }
        }

        return max(1, estimate)
    }

    /// Estimate the state space impact of a single constant value
    /// Note: Made internal for testability
    func estimateConstantImpact(_ value: ConstantValue) -> Int {
        switch value {
        case .int(let n):
            // Integer constants like N typically define ranges 0..(N-1)
            // State space grows roughly as N^k where k is number of variables
            return max(1, n * n)

        case .set(let elements):
            // Sets contribute based on their cardinality
            // Power set has 2^n subsets, but typically we see n^2 to n^3 impact
            let count = elements.count
            return max(1, count * count * count)

        case .bool:
            // Booleans double the state space per variable
            return 4

        case .string:
            // Strings are usually identifiers, moderate impact
            return 10

        case .modelValue, .symmetrySet:
            // Model values and symmetry sets - moderate impact
            // Symmetry actually reduces states but we estimate conservatively
            return 10
        }
    }

    /// Check if TLC is available
    var isTLCAvailable: Bool {
        get async {
            tlcPath != nil
        }
    }

    // MARK: - Model Checking

    /// Start a model checking session
    /// - Parameters:
    ///   - specURL: URL to the TLA+ specification file
    ///   - config: Model configuration
    ///   - sessionId: Unique identifier for this session
    ///   - binaryMode: Which TLC binary to use (.auto selects based on estimated state space)
    ///   - recoverFrom: Optional checkpoint to recover from
    ///   - progress: Callback for progress updates
    /// - Returns: Final result of model checking
    func startModelCheck(
        spec specURL: URL,
        config: ModelConfig,
        sessionId: UUID = UUID(),
        binaryMode: TLCBinaryMode = .auto,
        recoverFrom checkpoint: CheckpointInfo? = nil,
        progress: @escaping @Sendable (ModelCheckProgress) -> Void
    ) async throws -> ModelCheckResult {
        let isJVMMode = binaryMode == .jvm
        let executableURL: URL

        // Capture jar path early to avoid TOCTOU race (Issue #2)
        // The computed property re-evaluates filesystem state, so capture once
        let capturedJarPath = tla2toolsJarPath

        if isJVMMode {
            // JVM mode: use java executable with tla2tools.jar
            guard let java = await getJavaPath() else {
                logger.error("Java not found for JVM mode")
                throw TLCError.javaNotFound
            }
            guard let jarPath = capturedJarPath else {
                logger.error("tla2tools.jar not found for JVM mode")
                throw TLCError.tla2toolsNotFound
            }
            executableURL = java
            logger.info("Using JVM mode with Java at: \(java.path), jar at: \(jarPath.path)")
        } else {
            // Native binary mode
            guard let tlcPath = selectBinary(mode: binaryMode, config: config) else {
                logger.error("TLC binary not found")
                throw TLCError.tlcNotFound
            }
            executableURL = tlcPath
            logger.info("Using TLC at: \(tlcPath.path)")
        }
        let parser = TLCOutputParser()
        parser.sessionId = sessionId
        parsers[sessionId] = parser

        // Write config file next to spec with matching name (TLC native requires this)
        let specName = specURL.deletingPathExtension().lastPathComponent
        let specDir = specURL.deletingLastPathComponent()

        // Validate spec name doesn't contain path traversal sequences (Issue #10)
        guard !specName.contains("..") && !specName.contains("/") && !specName.contains("\\") else {
            logger.error("Invalid spec name contains path traversal: \(specName)")
            throw TLCError.invalidConfig("Spec name contains invalid characters")
        }

        let configURL = specDir.appendingPathComponent("\(specName).cfg")

        // Verify config URL is still within the spec directory (defense in depth)
        let resolvedConfigPath = configURL.standardized.path
        let resolvedSpecDir = specDir.standardized.path
        guard resolvedConfigPath.hasPrefix(resolvedSpecDir) else {
            logger.error("Config path escaped spec directory: \(resolvedConfigPath)")
            throw TLCError.invalidConfig("Config file path is outside spec directory")
        }

        // Always materialize the resolved model configuration before launching TLC.
        // TLC reads model semantics from the cfg file, not from CLI flags, so
        // preserving a stale on-disk cfg can execute different semantics than the UI shows.
        let configContent = config.generateConfigFile()

        do {
            try configContent.write(to: configURL, atomically: true, encoding: .utf8)
        } catch {
            throw TLCError.configWriteFailed(error)
        }

        var arguments: [String] = []
        let libraryArgument = BinaryDiscovery.configuredTLALibraryPropertyValue().map { "-DTLA-Library=\($0)" }

        if isJVMMode {
            if let libraryArgument {
                arguments.append(libraryArgument)
            }
            // JVM arguments: -Xmx, -jar, then TLC arguments
            let physicalMemoryBytes = ProcessInfo.processInfo.physicalMemory
            // JVM has no 32GB limit - use 85% of physical memory, capped at 64GB (Issue #6)
            // Cap prevents allocation failures on very high-memory machines or when other apps need RAM
            let memGB = min(64, max(4, Int(Double(physicalMemoryBytes) / (1024 * 1024 * 1024) * 0.85)))
            arguments.append("-Xmx\(memGB)g")
            arguments.append("-jar")
            // Use captured jar path to avoid TOCTOU race (Issue #2)
            arguments.append(capturedJarPath!.path)
            // Add TLC arguments after -jar
            arguments.append(contentsOf: buildArguments(for: config, configURL: configURL, isJVM: true))
        } else {
            arguments = buildArguments(for: config, configURL: configURL, isJVM: false)
            if let libraryArgument {
                arguments.insert(libraryArgument, at: 0)
            }
        }

        // Add recover argument if resuming from checkpoint (Issue #4: validate checkpoint ID)
        if let checkpoint = checkpoint {
            // Validate checkpoint ID format to prevent command injection
            // TLC checkpoint IDs are timestamps: YY-MM-DD-HH-MM-SS (e.g., "26-01-20-14-30-45")
            let validCheckpointPattern = try! NSRegularExpression(
                pattern: #"^[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}-[0-9]{2}$"#
            )
            let idRange = NSRange(checkpoint.id.startIndex..., in: checkpoint.id)
            guard validCheckpointPattern.firstMatch(in: checkpoint.id, range: idRange) != nil else {
                logger.error("Invalid checkpoint ID format: \(checkpoint.id)")
                throw TLCError.invalidConfig("Invalid checkpoint ID format: expected YY-MM-DD-HH-MM-SS")
            }
            arguments.append("-recover")
            arguments.append(checkpoint.id)
        }

        arguments.append(specURL.path)

        logger.info("TLC arguments: \(arguments.joined(separator: " "))")
        OutputManager.shared.log("TLC command: \(arguments.joined(separator: " "))", source: .system)

        let process = Process()
        process.executableURL = executableURL

        process.arguments = arguments
        process.currentDirectoryURL = specURL.deletingLastPathComponent()

        // Set minimal environment — don't inherit full parent environment
        process.environment = ProcessEnvironment.minimal()

        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        process.standardOutput = stdoutPipe
        process.standardError = stderrPipe

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

        let startTime = Date()

        // Create async stream for progress updates with proper termination
        // Use a thread-safe wrapper to prevent yielding after finish
        let streamState = StreamState<ModelCheckProgress>(throttle: .fps30)

        let progressStream = AsyncStream<ModelCheckProgress> { continuation in
            // Store continuation reference for the handlers
            streamState.setContinuation(continuation)

            stdoutHandle.readabilityHandler = { [weak parser, weak streamState] handle in
                let data = handle.availableData
                if data.isEmpty {
                    // EOF reached. Self-clear the handler so we don't keep getting scheduled
                    // on a dead pipe if `continuation.onTermination` didn't fire for any reason.
                    handle.readabilityHandler = nil
                    return
                }
                guard let parser = parser, let state = streamState else { return }

                // Log raw output to OutputManager
                if let str = String(data: data, encoding: .utf8) {
                    OutputManager.shared.logLines(str.nonEmptyOutputLines, source: .tlc)
                }

                // Guard against yielding after stream is finished
                guard !state.isFinished else { return }

                if let update = parser.parseThreadSafe(data) {
                    state.yield(update)
                }
            }

            stderrHandle.readabilityHandler = { [weak parser] handle in
                let data = handle.availableData
                if data.isEmpty {
                    handle.readabilityHandler = nil
                    return
                }
                if let str = String(data: data, encoding: .utf8) {
                    logger.error("TLC stderr: \(str)")
                    // Log errors to OutputManager and check for OOM
                    let lines = str.nonEmptyOutputLines
                    for line in lines {
                        // Check for OOM in stderr
                        parser?.parseStderr(line)
                    }
                    OutputManager.shared.logLines(lines, source: .tlc, isError: true)
                }
            }

            continuation.onTermination = { _ in
                stdoutHandle.readabilityHandler = nil
                stderrHandle.readabilityHandler = nil
            }
        }

        streamStates[sessionId] = streamState
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
            streamStates.removeValue(forKey: sessionId)
            streamState.finish()
            throw TLCError.failedToStart(error)
        }

        progress(ModelCheckProgress(sessionId: sessionId, phase: .parsing))

        let progressTask = Task {
            for await update in progressStream {
                progress(update)
            }
        }
        progressTasks[sessionId] = progressTask

        let exitStatus = await exitObserver.wait(for: process)
        process.terminationHandler = nil

        // Drain any remaining buffered data before clearing handlers.
        // readabilityHandler may not fire for data already in the pipe buffer
        // after process exit, so we must read it synchronously.
        let lastStdout = stdoutHandle.availableData
        if !lastStdout.isEmpty {
            if let str = String(data: lastStdout, encoding: .utf8) {
                OutputManager.shared.logLines(str.nonEmptyOutputLines, source: .tlc)
            }
            if let update = parser.parseThreadSafe(lastStdout) {
                streamState.yield(update)
            }
        }
        let lastStderr = stderrHandle.availableData
        if !lastStderr.isEmpty {
            if let str = String(data: lastStderr, encoding: .utf8) {
                let lines = str.nonEmptyOutputLines
                for line in lines {
                    parser.parseStderr(line)
                }
                OutputManager.shared.logLines(lines, source: .tlc, isError: true)
            }
        }

        // Now safe to clear handlers and close
        stdoutHandle.readabilityHandler = nil
        stderrHandle.readabilityHandler = nil
        try? stdoutHandle.close()
        try? stderrHandle.close()

        // Mark stream as finished and clean up
        streamStates.removeValue(forKey: sessionId)?.finish()

        progressTasks.removeValue(forKey: sessionId)?.cancel()

        ProcessRegistry.shared.unregister(sessionId)
        activeProcesses.removeValue(forKey: sessionId)

        parser.finalizeErrorTrace()

        let duration = Date().timeIntervalSince(startTime)

        // Use async result method for large trace support
        let result = await parser.finalResultWithStorage(exitCode: exitStatus, duration: duration)

        parsers.removeValue(forKey: sessionId)

        progress(ModelCheckProgress(
            sessionId: sessionId,
            phase: result.success ? .done : .error,
            statesFound: result.statesFound,
            distinctStates: result.distinctStates,
            statesLeft: 0,
            duration: duration,
            coverage: result.coverage
        ))

        return result
    }

    /// Stop a running model check
    func stop(sessionId: UUID) {
        progressTasks.removeValue(forKey: sessionId)?.cancel()
        streamStates.removeValue(forKey: sessionId)?.finish()
        ProcessRegistry.shared.terminate(sessionId)
        activeProcesses.removeValue(forKey: sessionId)
        parsers.removeValue(forKey: sessionId)
    }

    /// Stop a running model check gracefully (SIGINT to trigger checkpoint)
    /// - Parameter sessionId: The session to stop
    /// - Note: Sending SIGINT to TLC causes it to save a checkpoint before exiting
    func stopGracefully(sessionId: UUID) {
        if let process = activeProcesses[sessionId] {
            // Send SIGINT (interrupt) instead of SIGTERM
            // This causes TLC to save a checkpoint before exiting
            process.interrupt()
        }
    }

    /// Stop all running model checks
    func stopAll() {
        for (_, task) in progressTasks {
            task.cancel()
        }
        progressTasks.removeAll()

        // Finish all streams
        for (_, state) in streamStates {
            state.finish()
        }
        streamStates.removeAll()

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

    // MARK: - Argument Building

    private func buildArguments(for config: ModelConfig, configURL: URL, isJVM: Bool = false) -> [String] {
        var args: [String] = []

        if !isJVM {
            // Memory allocation for GraalVM native image
            // Note: Native image built with compressed references caps heap at 32GB
            let physicalMemoryBytes = ProcessInfo.processInfo.physicalMemory
            let maxNativeImageHeap: UInt64 = 32 * 1024 * 1024 * 1024  // 32GB limit due to compressed refs
            let desiredMemory = UInt64(Double(physicalMemoryBytes) * 0.85)
            let tlcMemoryBytes = min(maxNativeImageHeap, max(4 * 1024 * 1024 * 1024, desiredMemory))
            args.append("-XX:MaxHeapSize=\(tlcMemoryBytes)")
        }

        // Disk-based fingerprint storage for large state spaces
        // -fpmem controls what fraction of memory is used for fingerprints before spilling to disk
        if config.useDiskStorage {
            args.append("-fpmem")
            args.append("0.9")  // Use 90% of heap for fingerprints, rest spills to disk
        }

        args.append("-tool")

        args.append("-workers")
        args.append("\(config.workers)")

        if config.checkpointEnabled {
            let checkpointMinutes = Int(config.checkpointInterval / 60)
            if checkpointMinutes > 0 {
                args.append("-checkpoint")
                args.append("\(checkpointMinutes)")
            }
        }

        if config.depthFirst {
            args.append("-dfid")
            args.append("\(config.maxDepth ?? 100)")
        }

        if !config.checkDeadlock {
            args.append("-deadlock")
        }

        args.append("-config")
        args.append(configURL.path)

        if let checkpointDir = config.checkpointDir {
            args.append("-metadir")
            args.append(checkpointDir.path)
        }

        return args
    }
}

// MARK: - TLC Errors

enum TLCError: Error, LocalizedError {
    case tlcNotFound
    case failedToStart(Error)
    case specNotFound
    case invalidConfig(String)
    case configWriteFailed(Error)
    case timeout
    case cancelled
    case javaNotFound
    case tla2toolsNotFound
    case outOfMemory(suggestJVM: Bool)

    var errorDescription: String? {
        switch self {
        case .tlcNotFound:
            return "TLC model checker not found. The bundled tlc-native binary is missing."
        case .failedToStart(let error):
            return "Failed to start TLC: \(error.localizedDescription)"
        case .specNotFound:
            return "Specification file not found."
        case .invalidConfig(let message):
            return "Invalid model configuration: \(message)"
        case .configWriteFailed(let error):
            return "Failed to write config file: \(error.localizedDescription)"
        case .timeout:
            return "Model checking timed out."
        case .cancelled:
            return "Model checking was cancelled."
        case .javaNotFound:
            return "Java not found. JVM fallback requires Java to be installed."
        case .tla2toolsNotFound:
            return "tla2tools.jar not found. JVM fallback requires tla2tools.jar."
        case .outOfMemory(let suggestJVM):
            if suggestJVM {
                return "TLC ran out of memory. Consider enabling JVM fallback or disk storage for large state spaces."
            } else {
                return "TLC ran out of memory. Consider reducing model size or enabling disk storage."
            }
        }
    }
}

// MARK: - Progress Data Point

/// A single data point for the progress chart, sampled at ~1Hz
struct ProgressDataPoint: Identifiable {
    let id = UUID()
    let timestamp: TimeInterval  // seconds since start
    let statesFound: UInt64
    let distinctStates: UInt64
    let statesPerSecond: Double
    let memoryUsed: UInt64
}

// MARK: - TLC Session

/// Observable object for tracking a TLC session in the UI
@MainActor
class TLCSession: ObservableObject {
    let id: UUID
    let specURL: URL
    var config: ModelConfig

    @Published var isRunning = false
    @Published var progress: ModelCheckProgress?
    @Published var result: ModelCheckResult?
    @Published var error: Error?
    @Published var checkpointStatus: CheckpointStatus = .none
    @Published var progressHistory: [ProgressDataPoint] = []

    /// The binary mode to use for this session
    var binaryMode: TLCProcessManager.TLCBinaryMode = .auto

    private var task: Task<Void, Never>?
    private var recoveringFrom: CheckpointInfo?

    /// Tracks when we last appended a chart data point (for ~1Hz downsampling)
    private var lastChartUpdateTime: TimeInterval = 0
    /// Start time of the current model check run
    private var runStartTime: Date?

    init(specURL: URL, config: ModelConfig, binaryMode: TLCProcessManager.TLCBinaryMode = .auto) {
        self.id = UUID()
        self.specURL = specURL
        self.config = config
        self.binaryMode = binaryMode
    }

    func start() {
        guard !isRunning else { return }
        isRunning = true
        error = nil
        result = nil
        progressHistory = []
        lastChartUpdateTime = 0
        runStartTime = Date()

        // Capture values to avoid retain cycle - weak self in Task closure
        // means we shouldn't access self properties after await points
        let capturedSpecURL = specURL
        let capturedConfig = config
        let capturedSessionId = id
        let capturedBinaryMode = binaryMode
        let capturedRecoveringFrom = recoveringFrom
        let capturedStartTime = runStartTime!

        task = Task { @MainActor [weak self] in
            do {
                let finalResult = try await TLCProcessManager.shared.startModelCheck(
                    spec: capturedSpecURL,
                    config: capturedConfig,
                    sessionId: capturedSessionId,
                    binaryMode: capturedBinaryMode,
                    recoverFrom: capturedRecoveringFrom
                ) { [weak self] progressUpdate in
                    Task { @MainActor in
                        guard let self else { return }
                        self.progress = progressUpdate

                        // Downsample chart data to ~1 point/sec
                        let elapsed = Date().timeIntervalSince(capturedStartTime)
                        let isFinalUpdate = progressUpdate.phase == .done || progressUpdate.phase == .error
                        if isFinalUpdate || elapsed - self.lastChartUpdateTime >= 1.0 {
                            self.lastChartUpdateTime = elapsed
                            self.progressHistory.append(ProgressDataPoint(
                                timestamp: elapsed,
                                statesFound: progressUpdate.statesFound,
                                distinctStates: progressUpdate.distinctStates,
                                statesPerSecond: progressUpdate.statesPerSecond,
                                memoryUsed: progressUpdate.memoryUsed
                            ))
                        }
                    }
                }
                let effectiveResult = finalResult.outOfMemory
                    ? finalResult.withSuggestJVMRetry(finalResult.suggestJVMRetry && capturedConfig.useJVMFallback)
                    : finalResult

                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                // Guard against self being deallocated during await
                guard let self else { return }

                self.result = effectiveResult
                self.isRunning = false
                self.recoveringFrom = nil

                // Update checkpoint status if we were recovering
                if case .restoring(let checkpoint) = self.checkpointStatus {
                    self.checkpointStatus = .restored(checkpoint)
                }

                // Send completion notification
                let moduleName = capturedSpecURL.deletingPathExtension().lastPathComponent
                CompletionNotifier.shared.notifyTLCComplete(
                    success: effectiveResult.success,
                    moduleName: moduleName,
                    statesGenerated: Int(effectiveResult.statesFound),
                    duration: effectiveResult.duration
                )
            } catch {
                // Check for cancellation before updating state
                guard !Task.isCancelled else { return }

                // Guard against self being deallocated during await
                guard let self else { return }

                self.error = error
                self.isRunning = false
                self.recoveringFrom = nil
                self.checkpointStatus = .none

                // Send failure notification
                let moduleName = capturedSpecURL.deletingPathExtension().lastPathComponent
                CompletionNotifier.shared.notifyTLCComplete(
                    success: false,
                    moduleName: moduleName,
                    statesGenerated: nil,
                    duration: 0
                )
            }
        }
    }

    /// Resume model checking from a checkpoint
    func resume(from checkpoint: CheckpointInfo) {
        recoveringFrom = checkpoint
        checkpointStatus = .restoring(checkpoint)
        start()
    }

    /// Stop the session synchronously (fires async cleanup in background)
    func stop() {
        // Cancel the task first to prevent it from setting state after we clear it
        let taskToCancel = task
        task = nil
        taskToCancel?.cancel()

        // Use synchronous process termination via ProcessRegistry
        ProcessRegistry.shared.terminate(id)

        // Now safe to update state
        isRunning = false
        checkpointStatus = .none
    }

    /// Stop the session and wait for async cleanup to complete
    func stopAsync() async {
        task?.cancel()
        task = nil
        await TLCProcessManager.shared.stop(sessionId: id)
        isRunning = false
        checkpointStatus = .none
    }

    /// Stop the model check gracefully, triggering a checkpoint save
    func stopWithCheckpoint() {
        checkpointStatus = .saving
        Task {
            await TLCProcessManager.shared.stopGracefully(sessionId: id)
        }
        // Note: The process will exit after saving checkpoint
        // We'll update status when we detect the checkpoint file
    }

    /// Retry with JVM mode after OOM
    func retryWithJVM() {
        guard result?.outOfMemory == true, result?.suggestJVMRetry == true, !isRunning else { return }
        binaryMode = .jvm
        result = nil
        error = nil
        start()
    }

    /// Retry with disk storage enabled
    func retryWithDiskStorage() {
        guard result?.outOfMemory == true, !isRunning, !config.useDiskStorage else { return }
        config.useDiskStorage = true
        result = nil
        error = nil
        start()
    }

    /// Check if JVM retry is available
    var canRetryWithJVM: Bool {
        get async {
            await TLCProcessManager.shared.isJVMAvailable
        }
    }
}
