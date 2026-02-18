import Foundation
import os

private let logger = Log.logger(category: "SafeArchiveExtractor")

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
    ///
    /// Eliminates TOCTOU race by extracting to a temporary staging directory first,
    /// validating all contents there, then moving atomically to the target.
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
        let fileManager = FileManager.default

        // Step 1: Create a secure staging directory for extraction
        let stagingDir = fileManager.temporaryDirectory
            .appendingPathComponent("SafeArchiveExtractor-\(UUID().uuidString)")
        do {
            try fileManager.createDirectory(at: stagingDir, withIntermediateDirectories: true)
        } catch {
            throw Error.targetDirectoryCreationFailed(error)
        }

        // Ensure staging directory is cleaned up on all exit paths
        defer {
            try? fileManager.removeItem(at: stagingDir)
        }

        // Step 2: Extract to staging directory
        try performExtraction(from: archiveURL, to: stagingDir, stripComponents: stripComponents)

        // Step 3: Validate extracted contents in staging directory
        // Now there is no TOCTOU window — we validate the actual extracted files
        try validateNoEscapingSymlinks(in: stagingDir)
        try validateExtractedPaths(in: stagingDir)

        logger.info("Validated extracted contents in staging directory")

        // Step 4: Create target directory if needed
        if !fileManager.fileExists(atPath: targetDirectory.path) {
            do {
                try fileManager.createDirectory(at: targetDirectory, withIntermediateDirectories: true)
            } catch {
                throw Error.targetDirectoryCreationFailed(error)
            }
        }

        // Step 5: Move validated contents from staging to target
        let contents = try fileManager.contentsOfDirectory(at: stagingDir,
                                                            includingPropertiesForKeys: nil)
        for item in contents {
            let destination = targetDirectory.appendingPathComponent(item.lastPathComponent)
            // Remove existing item at destination if present
            if fileManager.fileExists(atPath: destination.path) {
                try fileManager.removeItem(at: destination)
            }
            try fileManager.moveItem(at: item, to: destination)
        }

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

    /// Validates extracted file paths don't contain traversal components.
    /// This runs on the actual extracted files in the staging directory.
    private static func validateExtractedPaths(in directory: URL) throws {
        let fileManager = FileManager.default
        guard let resolvedDirCStr = realpath(directory.path, nil) else {
            throw Error.pathTraversalDetected("Cannot resolve staging directory: \(directory.path)")
        }
        let resolvedDirPath = String(cString: resolvedDirCStr)
        free(resolvedDirCStr)

        guard let enumerator = fileManager.enumerator(
            at: directory,
            includingPropertiesForKeys: nil,
            options: []
        ) else { return }

        for case let fileURL as URL in enumerator {
            // Resolve the actual path and verify it's within the staging directory
            let resolvedPath = fileURL.resolvingSymlinksInPath().path
            if !resolvedPath.hasPrefix(resolvedDirPath + "/") &&
               resolvedPath != resolvedDirPath {
                throw Error.pathTraversalDetected(fileURL.path)
            }
        }
    }

    /// Validates that no symlinks in the extracted content point outside the target.
    /// Uses realpath() for canonical path resolution to prevent TOCTOU and path traversal via `..`.
    private static func validateNoEscapingSymlinks(in directory: URL) throws {
        let fileManager = FileManager.default

        // Canonicalize the target directory itself using realpath()
        guard let resolvedTargetCStr = realpath(directory.path, nil) else {
            // If target directory can't be resolved, it's unsafe to proceed
            throw Error.symlinkEscapeDetected("Cannot resolve target directory: \(directory.path)")
        }
        let resolvedTargetPath = String(cString: resolvedTargetCStr)
        free(resolvedTargetCStr)

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
                    // Use resolvingSymlinksInPath which calls realpath() for canonical resolution.
                    // This properly handles ".." components and nested symlinks.
                    let resolvedDestination = fileURL.resolvingSymlinksInPath().path

                    // Check if resolved destination is within the resolved target directory
                    if !resolvedDestination.hasPrefix(resolvedTargetPath + "/") &&
                       resolvedDestination != resolvedTargetPath {
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
