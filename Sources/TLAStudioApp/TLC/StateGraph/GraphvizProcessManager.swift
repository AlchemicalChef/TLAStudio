import Foundation

// MARK: - Graphviz Process Manager

/// Actor that manages Graphviz (dot) subprocess execution
actor GraphvizProcessManager {
    static let shared = GraphvizProcessManager()

    // MARK: - Graphviz Detection

    /// Common paths where Graphviz dot binary might be installed
    private static let dotPaths = [
        "/usr/local/bin/dot",
        "/opt/homebrew/bin/dot",
        "/usr/bin/dot",
        "/opt/local/bin/dot"
    ]

    /// Find the path to the dot executable
    private var dotPath: URL? {
        for path in Self.dotPaths {
            if FileManager.default.fileExists(atPath: path) {
                return URL(fileURLWithPath: path)
            }
        }
        return nil
    }

    /// Check if Graphviz is available
    var isGraphvizAvailable: Bool {
        dotPath != nil
    }

    /// Get the path to graphviz if installed
    var graphvizPath: String? {
        dotPath?.path
    }

    // MARK: - Rendering

    /// Render DOT source to the specified format
    /// - Parameters:
    ///   - dotSource: The DOT format source string
    ///   - format: Output format (svg, png, pdf)
    /// - Returns: The rendered output as Data
    func render(dotSource: String, format: GraphExportFormat) async throws -> Data {
        // DOT format is just the source, no rendering needed
        if format == .dot {
            guard let data = dotSource.data(using: .utf8) else {
                throw GraphvizError.encodingError
            }
            return data
        }

        guard let dotPath = dotPath else {
            throw GraphvizError.notInstalled
        }

        let process = Process()
        process.executableURL = dotPath
        process.arguments = ["-T\(format.graphvizFormat)"]

        // Set up pipes
        let inputPipe = Pipe()
        let outputPipe = Pipe()
        let errorPipe = Pipe()

        process.standardInput = inputPipe
        process.standardOutput = outputPipe
        process.standardError = errorPipe

        // Ensure file handles are closed to prevent resource leaks
        defer {
            try? outputPipe.fileHandleForReading.close()
            try? errorPipe.fileHandleForReading.close()
        }

        // Start process
        do {
            try process.run()
        } catch {
            throw GraphvizError.failedToStart(error)
        }

        // Write DOT source to stdin
        guard let inputData = dotSource.data(using: .utf8) else {
            process.terminate()
            throw GraphvizError.encodingError
        }

        // Write input and close pipe
        let inputHandle = inputPipe.fileHandleForWriting
        inputHandle.write(inputData)
        try inputHandle.close()

        // Wait for process to complete with timeout
        // Use generous timeout (10 min) - large traces with thousands of states can take time
        // User can cancel via UI if needed; this is just a safety net for hung processes
        let timeoutSeconds: Double = 600.0
        let startTime = Date()
        while process.isRunning {
            if Date().timeIntervalSince(startTime) > timeoutSeconds {
                process.terminate()
                throw GraphvizError.renderingFailed("Process timed out after \(Int(timeoutSeconds / 60)) minutes")
            }
            try await Task.sleep(nanoseconds: 100_000_000) // 100ms
        }

        // Check exit status
        if process.terminationStatus != 0 {
            let errorData = errorPipe.fileHandleForReading.readDataToEndOfFile()
            let errorMessage = String(data: errorData, encoding: .utf8) ?? "Unknown error"
            throw GraphvizError.renderingFailed(errorMessage)
        }

        // Read output - use readDataToEndOfFile for simplicity
        // Note: For extremely large traces (10,000+ states), consider streaming or pagination
        let outputData = outputPipe.fileHandleForReading.readDataToEndOfFile()

        if outputData.isEmpty {
            throw GraphvizError.emptyOutput
        }

        return outputData
    }

    /// Render an error trace to the specified format
    /// - Parameters:
    ///   - trace: The error trace to render
    ///   - format: Output format
    ///   - configuration: DOT generation configuration
    /// - Returns: The rendered output as Data
    func render(
        trace: ErrorTrace,
        format: GraphExportFormat,
        configuration: DOTGenerator.Configuration = DOTGenerator.Configuration()
    ) async throws -> Data {
        let generator = DOTGenerator(configuration: configuration)
        let dotSource = generator.generate(from: trace)
        return try await render(dotSource: dotSource, format: format)
    }

    /// Get Graphviz version information
    func version() async throws -> String {
        guard let dotPath = dotPath else {
            throw GraphvizError.notInstalled
        }

        let process = Process()
        process.executableURL = dotPath
        process.arguments = ["-V"]

        let outputPipe = Pipe()
        let errorPipe = Pipe()
        process.standardOutput = outputPipe
        process.standardError = errorPipe  // dot -V writes to stderr

        // Ensure file handles are closed
        defer {
            try? outputPipe.fileHandleForReading.close()
            try? errorPipe.fileHandleForReading.close()
        }

        do {
            try process.run()
        } catch {
            throw GraphvizError.failedToStart(error)
        }

        // Wait with timeout
        let timeoutSeconds: Double = 5.0
        let startTime = Date()
        while process.isRunning {
            if Date().timeIntervalSince(startTime) > timeoutSeconds {
                process.terminate()
                return "Unknown version (timeout)"
            }
            try await Task.sleep(nanoseconds: 50_000_000) // 50ms
        }

        // dot -V writes to stderr, not stdout
        let errorData = errorPipe.fileHandleForReading.readDataToEndOfFile()
        if let version = String(data: errorData, encoding: .utf8)?.trimmingCharacters(in: .whitespacesAndNewlines) {
            return version
        }

        return "Unknown version"
    }
}

// MARK: - Graphviz Errors

enum GraphvizError: Error, LocalizedError {
    case notInstalled
    case failedToStart(Error)
    case renderingFailed(String)
    case encodingError
    case emptyOutput

    var errorDescription: String? {
        switch self {
        case .notInstalled:
            return "Graphviz is not installed. Please install it using 'brew install graphviz' or download from graphviz.org."
        case .failedToStart(let error):
            return "Failed to start Graphviz: \(error.localizedDescription)"
        case .renderingFailed(let message):
            return "Graphviz rendering failed: \(message)"
        case .encodingError:
            return "Failed to encode DOT source."
        case .emptyOutput:
            return "Graphviz produced no output."
        }
    }
}

// MARK: - Installation Instructions

extension GraphvizProcessManager {
    /// Get installation instructions for the current platform
    static var installationInstructions: String {
        """
        Graphviz is required to render state graphs.

        Install using Homebrew:
            brew install graphviz

        Or download from:
            https://graphviz.org/download/

        After installation, restart TLA+ Studio.
        """
    }
}
