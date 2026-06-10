import Foundation
import os

// MARK: - SANY Analysis Result

/// Result of a SANY semantic analysis run.
enum SANYAnalysisResult {
    /// java or tla2tools.jar could not be located. Semantic analysis is simply
    /// unavailable — not an error worth surfacing in the UI.
    case unavailable(reason: String)
    /// The subprocess could not be started, or timed out.
    case failure(error: Error)
    /// SANY ran to completion. A non-zero termination status means it reported
    /// findings (with `-error-codes`: 2 = parse error, 4 = semantic/level error;
    /// aborts exit 255); the findings themselves are in `stdout`.
    case success(stdout: String, stderr: String, terminationStatus: Int32)
}

// MARK: - SANY Runner

/// Actor that runs `tla2sany.SANY` — the official TLA+ semantic analyzer inside
/// tla2tools.jar — against a spec on disk.
///
/// Mirrors `PlusCalTranslator` and shares its hardened subprocess machinery
/// (bounded capture, timeout, ProcessRegistry reaping) via `JavaProcessRunner`.
actor SANYRunner {

    private let logger = Log.logger(category: "SANYRunner")

    /// Shared instance
    static let shared = SANYRunner()

    /// Run SANY against the spec at `specFileURL`.
    ///
    /// SANY has no `-I` flag (verified against the bundled jar, SANY2 v2.2);
    /// module resolution beyond the spec's own directory goes through the
    /// `TLA-Library` JVM system property — the same colon-separated list TLC
    /// consumes via `-DTLA-Library`.
    ///
    /// - Parameters:
    ///   - specFileURL: On-disk spec whose basename must equal its `MODULE` name.
    ///   - searchPaths: Module search path, typically from `ProjectModuleResolver`.
    ///   - timeout: Wall-clock limit for the JVM run.
    func analyze(
        specFileURL: URL,
        searchPaths: [URL] = [],
        timeout: TimeInterval = 30
    ) async -> SANYAnalysisResult {
        guard let toolsJar = JavaProcessRunner.findTLA2Tools() else {
            return .unavailable(reason: "tla2tools.jar not found")
        }
        guard let javaPath = JavaProcessRunner.findJava() else {
            return .unavailable(reason: "java not found")
        }

        var arguments: [String] = []
        let libraryPaths = searchPaths.map(\.path).filter { !$0.isEmpty }
        if !libraryPaths.isEmpty {
            arguments.append("-DTLA-Library=\(libraryPaths.joined(separator: ":"))")
        }
        arguments += ["-cp", toolsJar.path, "tla2sany.SANY", "-error-codes", specFileURL.path]

        do {
            let result = try await JavaProcessRunner.run(
                executableURL: URL(fileURLWithPath: javaPath),
                arguments: arguments,
                currentDirectoryURL: specFileURL.deletingLastPathComponent(),
                timeout: timeout
            )
            return .success(
                stdout: String(data: result.stdout, encoding: .utf8) ?? "",
                stderr: String(data: result.stderr, encoding: .utf8) ?? "",
                terminationStatus: result.terminationStatus
            )
        } catch {
            logger.warning("SANY run failed: \(error.localizedDescription)")
            return .failure(error: error)
        }
    }
}
