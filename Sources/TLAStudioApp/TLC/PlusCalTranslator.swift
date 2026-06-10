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
///
/// Subprocess execution and java/jar discovery live in `JavaProcessRunner`,
/// shared with the SANY semantic analyzer.
actor PlusCalTranslator {

    private let logger = Log.logger(category: "PlusCalTranslator")

    /// Shared instance
    static let shared = PlusCalTranslator()

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
        guard let toolsJar = JavaProcessRunner.findTLA2Tools() else {
            return .error("Could not find tla2tools.jar. Please install TLA+ tools or configure the path in Settings.")
        }

        // Find java
        guard let javaPath = JavaProcessRunner.findJava() else {
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
            let result = try await JavaProcessRunner.run(
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
}
