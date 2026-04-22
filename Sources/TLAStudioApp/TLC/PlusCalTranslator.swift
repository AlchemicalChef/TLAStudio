import Foundation
import os

// MARK: - PlusCal Translation Result

/// Result of a PlusCal translation
enum PlusCalTranslationResult {
    case success(translatedContent: String)
    case noChangeNeeded
    case error(String)
}

// MARK: - PlusCal Translator

/// Actor that manages PlusCal-to-TLA+ translation via tla2tools.jar.
///
/// Translates PlusCal algorithms embedded in TLA+ specifications by running
/// `java -cp tla2tools.jar pcal.trans <file>`, which modifies the file in-place
/// between `\* BEGIN TRANSLATION` and `\* END TRANSLATION` markers.
actor PlusCalTranslator {

    private let logger = Log.logger(category: "PlusCalTranslator")

    /// Shared instance
    static let shared = PlusCalTranslator()

    /// Cap on captured stdout/stderr per stream. `pcal.trans` is expected to emit at most
    /// a few KB; anything past this is almost certainly a pathological loop and should not
    /// be allowed to balloon memory. The remainder is dropped but the process continues so
    /// we still observe its exit status.
    private static let maxCapturedBytes = 10 * 1024 * 1024  // 10 MB

    /// Drain a pipe into a bounded accumulator. Reading stops growing past `maxCapturedBytes`
    /// but continues consuming so the writer isn't back-pressured into a deadlock.
    private static func drain(
        handle: FileHandle,
        into accumulator: OutputAccumulator
    ) {
        handle.readabilityHandler = { [weak accumulator] h in
            let data = h.availableData
            if data.isEmpty {
                h.readabilityHandler = nil
                return
            }
            accumulator?.append(data)
        }
    }

    /// Thread-safe bounded byte accumulator. Accepts data and stores up to `limit` bytes.
    /// Additional data is dropped. Callers retrieve the accumulated buffer once the process
    /// has exited and both pipe handlers have been cleared.
    final class OutputAccumulator: @unchecked Sendable {
        private let lock = NSLock()
        private var buffer = Data()
        private let limit: Int

        init(limit: Int) { self.limit = limit }

        func append(_ data: Data) {
            lock.lock()
            defer { lock.unlock() }
            guard buffer.count < limit else { return }
            let remaining = limit - buffer.count
            buffer.append(data.prefix(remaining))
        }

        func snapshot() -> Data {
            lock.lock()
            defer { lock.unlock() }
            return buffer
        }
    }

    static func runProcess(
        executableURL: URL,
        arguments: [String],
        currentDirectoryURL: URL? = nil,
        timeout: TimeInterval? = nil
    ) async throws -> (terminationStatus: Int32, stdout: Data, stderr: Data) {
        let process = Process()
        process.executableURL = executableURL
        process.arguments = arguments
        process.currentDirectoryURL = currentDirectoryURL

        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        process.standardOutput = stdoutPipe
        process.standardError = stderrPipe

        let stdoutAccumulator = OutputAccumulator(limit: maxCapturedBytes)
        let stderrAccumulator = OutputAccumulator(limit: maxCapturedBytes)
        drain(handle: stdoutPipe.fileHandleForReading, into: stdoutAccumulator)
        drain(handle: stderrPipe.fileHandleForReading, into: stderrAccumulator)

        do {
            try process.run()
        } catch {
            stdoutPipe.fileHandleForReading.readabilityHandler = nil
            stderrPipe.fileHandleForReading.readabilityHandler = nil
            throw error
        }

        // Observe termination via the process's handler rather than polling. Resumption is
        // gated by `Atomic` semantics on the continuation so a concurrent timeout can't
        // resume twice.
        let terminationStatus = try await withCheckedThrowingContinuation { (cont: CheckedContinuation<Int32, Error>) in
            let didResume = ResumeGuard()

            process.terminationHandler = { finished in
                guard didResume.tryConsume() else { return }
                cont.resume(returning: finished.terminationStatus)
            }

            guard let timeout else { return }

            // If the timeout fires first, terminate the process and report the error.
            // The terminationHandler will still fire afterwards, but `didResume` prevents a
            // double resume.
            Task {
                try? await Task.sleep(nanoseconds: UInt64(timeout * 1_000_000_000))
                guard didResume.tryConsume() else { return }
                process.terminate()
                cont.resume(throwing: NSError(
                    domain: "PlusCalTranslator",
                    code: 1,
                    userInfo: [NSLocalizedDescriptionKey: "Process timed out after \(Int(timeout)) seconds"]
                ))
            }
        }

        stdoutPipe.fileHandleForReading.readabilityHandler = nil
        stderrPipe.fileHandleForReading.readabilityHandler = nil
        try? stdoutPipe.fileHandleForReading.close()
        try? stderrPipe.fileHandleForReading.close()

        return (terminationStatus, stdoutAccumulator.snapshot(), stderrAccumulator.snapshot())
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

    // MARK: - Translation

    /// Translate PlusCal in the given spec content.
    ///
    /// The translation process:
    /// 1. Write content to a temporary file
    /// 2. Find tla2tools.jar via BinaryDiscovery
    /// 3. Run `java -cp tla2tools.jar pcal.trans <tempfile>`
    /// 4. Read back the modified file
    /// 5. Return the translated content
    ///
    /// - Parameters:
    ///   - content: The TLA+ specification content containing PlusCal
    ///   - specURL: Optional URL of the spec file (used for temp file naming)
    /// - Returns: Translation result with the new content or an error
    func translate(content: String, specURL: URL? = nil) async -> PlusCalTranslationResult {
        // Check that content has PlusCal markers
        guard content.contains("algorithm") else {
            return .error("No PlusCal algorithm found in the specification.")
        }

        // Find tla2tools.jar
        guard let toolsJar = findTLA2Tools() else {
            return .error("Could not find tla2tools.jar. Please install TLA+ tools or configure the path in Settings.")
        }

        // Find java
        guard let javaPath = findJava() else {
            return .error("Java not found. Please install Java to use PlusCal translation.")
        }

        // Create a temporary file for the translation
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent("TLAStudio-pcal-\(UUID().uuidString)")

        do {
            try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        } catch {
            return .error("Failed to create temporary directory: \(error.localizedDescription)")
        }

        let fileName = specURL?.lastPathComponent ?? "PlusCal.tla"
        let tempFile = tempDir.appendingPathComponent(fileName)

        defer {
            try? FileManager.default.removeItem(at: tempDir)
        }

        // Write content to temp file
        do {
            try content.write(to: tempFile, atomically: true, encoding: .utf8)
        } catch {
            return .error("Failed to write temporary file: \(error.localizedDescription)")
        }

        do {
            let result = try await Self.runProcess(
                executableURL: URL(fileURLWithPath: javaPath),
                arguments: ["-cp", toolsJar.path, "pcal.trans", tempFile.path],
                currentDirectoryURL: tempDir,
                timeout: 30
            )

            let stderrOutput = String(data: result.stderr, encoding: .utf8) ?? ""
            let stdoutOutput = String(data: result.stdout, encoding: .utf8) ?? ""

            if result.terminationStatus != 0 {
                let errorMsg = stderrOutput.isEmpty ? stdoutOutput : stderrOutput
                let cleanError = errorMsg
                    .components(separatedBy: "\n")
                    .filter { !$0.isEmpty }
                    .joined(separator: "\n")
                return .error("PlusCal translation failed:\n\(cleanError)")
            }
        } catch {
            return .error("Failed to run PlusCal translator: \(error.localizedDescription)")
        }

        // Read back the translated file
        do {
            let translatedContent = try String(contentsOf: tempFile, encoding: .utf8)
            if translatedContent == content {
                return .noChangeNeeded
            }
            logger.info("PlusCal translation succeeded")
            return .success(translatedContent: translatedContent)
        } catch {
            return .error("Failed to read translated file: \(error.localizedDescription)")
        }
    }

    // MARK: - Tool Discovery

    private func findTLA2Tools() -> URL? {
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

    private func findJava() -> String? {
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
