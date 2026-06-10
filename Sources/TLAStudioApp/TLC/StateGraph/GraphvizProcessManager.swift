import Foundation

// MARK: - Graphviz Process Manager

/// Actor that manages Graphviz (dot) subprocess execution
actor GraphvizProcessManager {
    static let shared = GraphvizProcessManager()

    // MARK: - Graphviz Detection

    /// Find the path to the dot executable
    private var dotPath: URL? {
        BinaryDiscovery.find(
            named: "dot",
            options: .systemOnly(paths: [
                "/usr/local/bin",
                "/opt/homebrew/bin",
                "/usr/bin",
                "/opt/local/bin"
            ])
        )
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

        guard let inputData = dotSource.data(using: .utf8) else {
            throw GraphvizError.encodingError
        }

        // One-shot spawn via the shared runner: DOT source on stdin, rendered bytes on
        // stdout. Stdout must be UNBOUNDED — a large state-graph SVG/PDF legitimately
        // exceeds the default 10 MB capture cap and truncation would corrupt it. Stderr
        // carries diagnostics only, so the default bounded head-keep is safe there.
        // The runner registers with ProcessRegistry (SIGTERM → SIGKILL escalation) and
        // bridges task cancellation, replacing the old 100 ms polling loop.
        let timeoutSeconds: Double = 600.0
        let result: (terminationStatus: Int32, stdout: Data, stderr: Data)
        do {
            result = try await SubprocessRunner.run(
                executableURL: dotPath,
                arguments: ["-T\(format.graphvizFormat)"],
                timeout: timeoutSeconds,
                stdinData: inputData,
                stdoutPolicy: .unbounded
            )
        } catch is SubprocessRunner.TimeoutError {
            throw GraphvizError.renderingFailed("Process timed out after \(Int(timeoutSeconds / 60)) minutes")
        } catch is CancellationError {
            throw CancellationError()
        } catch {
            throw GraphvizError.failedToStart(error)
        }

        // Check exit status
        if result.terminationStatus != 0 {
            let errorMessage = String(data: result.stderr, encoding: .utf8) ?? "Unknown error"
            throw GraphvizError.renderingFailed(errorMessage)
        }

        if result.stdout.isEmpty {
            throw GraphvizError.emptyOutput
        }

        return result.stdout
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

        // `dot -V` is a quick probe; a stalled one (wedged install) is terminated by
        // the runner's timeout with ProcessRegistry SIGKILL escalation.
        let result: (terminationStatus: Int32, stdout: Data, stderr: Data)
        do {
            result = try await SubprocessRunner.run(
                executableURL: dotPath,
                arguments: ["-V"],
                timeout: 5.0
            )
        } catch is SubprocessRunner.TimeoutError {
            return "Unknown version (timeout)"
        } catch is CancellationError {
            throw CancellationError()
        } catch {
            throw GraphvizError.failedToStart(error)
        }

        // dot -V writes to stderr, not stdout
        if let version = String(data: result.stderr, encoding: .utf8)?.trimmingCharacters(in: .whitespacesAndNewlines) {
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
