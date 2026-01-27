import Foundation
import os

private let logger = Logger(subsystem: "com.tlastudio", category: "SafeArchiveExtractor")

// MARK: - Safe Archive Extractor

/// Provides secure tar archive extraction with path traversal protection.
/// Validates archive contents before extraction to prevent directory escape attacks.
enum SafeArchiveExtractor {

    // MARK: - Errors

    enum Error: Swift.Error, LocalizedError {
        case listingFailed(String)
        case pathTraversalDetected(String)
        case absolutePathDetected(String)
        case extractionFailed(String)
        case symlinkEscapeDetected(String)
        case targetDirectoryCreationFailed(Swift.Error)

        var errorDescription: String? {
            switch self {
            case .listingFailed(let message):
                return "Failed to list archive contents: \(message)"
            case .pathTraversalDetected(let path):
                return "Path traversal detected in archive: \(path)"
            case .absolutePathDetected(let path):
                return "Absolute path detected in archive: \(path)"
            case .extractionFailed(let message):
                return "Archive extraction failed: \(message)"
            case .symlinkEscapeDetected(let path):
                return "Symlink escaping target directory detected: \(path)"
            case .targetDirectoryCreationFailed(let error):
                return "Failed to create target directory: \(error.localizedDescription)"
            }
        }
    }

    // MARK: - Public API

    /// Safely extracts a tar archive to a target directory.
    /// - Parameters:
    ///   - archiveURL: URL to the archive file (.tar, .tar.gz, .tgz)
    ///   - targetDirectory: Directory to extract into
    ///   - stripComponents: Number of leading path components to strip (default 0)
    /// - Throws: SafeArchiveExtractor.Error if extraction fails or is unsafe
    static func extract(
        from archiveURL: URL,
        to targetDirectory: URL,
        stripComponents: Int = 0
    ) throws {
        // Step 1: List archive contents and validate paths
        let paths = try listArchiveContents(archiveURL)
        try validatePaths(paths)

        logger.info("Validated \(paths.count) paths in archive")

        // Step 2: Create target directory if needed
        let fileManager = FileManager.default
        if !fileManager.fileExists(atPath: targetDirectory.path) {
            do {
                try fileManager.createDirectory(at: targetDirectory, withIntermediateDirectories: true)
            } catch {
                throw Error.targetDirectoryCreationFailed(error)
            }
        }

        // Step 3: Extract with safe options
        try performExtraction(from: archiveURL, to: targetDirectory, stripComponents: stripComponents)

        // Step 4: Post-extraction validation - check for symlinks that escape target
        try validateNoEscapingSymlinks(in: targetDirectory)

        logger.info("Successfully extracted archive to \(targetDirectory.path)")
    }

    // MARK: - Private Helpers

    /// Lists all file paths in the archive without extracting.
    private static func listArchiveContents(_ archiveURL: URL) throws -> [String] {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tar")
        process.arguments = ["-tzf", archiveURL.path]

        let stdout = Pipe()
        let stderr = Pipe()
        process.standardOutput = stdout
        process.standardError = stderr

        do {
            try process.run()
            process.waitUntilExit()
        } catch {
            throw Error.listingFailed(error.localizedDescription)
        }

        if process.terminationStatus != 0 {
            let errorData = stderr.fileHandleForReading.readDataToEndOfFile()
            let errorMessage = String(data: errorData, encoding: .utf8) ?? "Unknown error"
            throw Error.listingFailed(errorMessage)
        }

        let outputData = stdout.fileHandleForReading.readDataToEndOfFile()
        guard let output = String(data: outputData, encoding: .utf8) else {
            throw Error.listingFailed("Failed to decode archive listing")
        }

        return output.components(separatedBy: .newlines).filter { !$0.isEmpty }
    }

    /// Validates that no paths escape the target directory.
    private static func validatePaths(_ paths: [String]) throws {
        for path in paths {
            // Check for absolute paths
            if path.hasPrefix("/") {
                throw Error.absolutePathDetected(path)
            }

            // Check for path traversal attempts
            let components = path.components(separatedBy: "/")
            var depth = 0
            for component in components {
                if component == ".." {
                    depth -= 1
                    if depth < 0 {
                        throw Error.pathTraversalDetected(path)
                    }
                } else if component != "." && !component.isEmpty {
                    depth += 1
                }
            }

            // Also check for encoded traversal attempts
            if path.contains("%2e%2e") || path.contains("%2E%2E") ||
               path.contains("..%2f") || path.contains("..%2F") ||
               path.contains("%2f..") || path.contains("%2F..") {
                throw Error.pathTraversalDetected(path)
            }
        }
    }

    /// Performs the actual extraction using tar.
    private static func performExtraction(
        from archiveURL: URL,
        to targetDirectory: URL,
        stripComponents: Int
    ) throws {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tar")

        var args = [
            "-xzf", archiveURL.path,
            "-C", targetDirectory.path,
            "--no-same-owner",        // Don't preserve file ownership
            "--no-same-permissions"   // Use umask instead of archive permissions
        ]

        if stripComponents > 0 {
            args.append("--strip-components=\(stripComponents)")
        }

        process.arguments = args

        let stderr = Pipe()
        process.standardError = stderr

        do {
            try process.run()
            process.waitUntilExit()
        } catch {
            throw Error.extractionFailed(error.localizedDescription)
        }

        if process.terminationStatus != 0 {
            let errorData = stderr.fileHandleForReading.readDataToEndOfFile()
            let errorMessage = String(data: errorData, encoding: .utf8) ?? "Unknown error"
            throw Error.extractionFailed(errorMessage)
        }
    }

    /// Validates that no symlinks in the extracted content point outside the target.
    private static func validateNoEscapingSymlinks(in directory: URL) throws {
        let fileManager = FileManager.default
        let targetPath = directory.path

        guard let enumerator = fileManager.enumerator(
            at: directory,
            includingPropertiesForKeys: [.isSymbolicLinkKey],
            options: []
        ) else {
            return
        }

        for case let fileURL as URL in enumerator {
            do {
                let resourceValues = try fileURL.resourceValues(forKeys: [.isSymbolicLinkKey])
                if resourceValues.isSymbolicLink == true {
                    // Resolve the symlink destination
                    let destination = try fileManager.destinationOfSymbolicLink(atPath: fileURL.path)

                    // Compute absolute path of destination
                    let absoluteDestination: String
                    if destination.hasPrefix("/") {
                        absoluteDestination = destination
                    } else {
                        // Relative symlink - resolve from symlink's parent directory
                        let parentDir = fileURL.deletingLastPathComponent().path
                        absoluteDestination = (parentDir as NSString).appendingPathComponent(destination)
                    }

                    // Normalize the path
                    let normalizedDestination = (absoluteDestination as NSString).standardizingPath

                    // Check if destination is within target directory
                    if !normalizedDestination.hasPrefix(targetPath) {
                        throw Error.symlinkEscapeDetected(fileURL.path)
                    }
                }
            } catch let error as Error {
                throw error
            } catch {
                // Ignore other errors (e.g., permission issues on individual files)
                logger.warning("Could not check symlink: \(fileURL.path) - \(error.localizedDescription)")
            }
        }
    }
}
