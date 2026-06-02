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

    /// Parent directory housing all transient staging dirs for archive extraction.
    /// Co-locates them under a single, namespaced directory so a startup sweep
    /// (`cleanupStaleStagingDirs`) can reap orphans from crashes / SIGKILL.
    private static var stagingParentDirectory: URL {
        FileManager.default.temporaryDirectory
            .appendingPathComponent("TLA+ Studio", isDirectory: true)
    }

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

        // Ensure the namespaced parent exists with 0o700 before we drop a staging
        // dir inside it. `temporaryDirectory` itself is already 0o700, but we want
        // to be explicit about the intermediate component too.
        do {
            try fileManager.createDirectory(
                at: stagingParentDirectory,
                withIntermediateDirectories: true,
                attributes: [.posixPermissions: 0o700]
            )
        } catch {
            throw Error.targetDirectoryCreationFailed(error)
        }

        // Stage the archive itself into our private parent first so that a
        // mid-listing archive swap on disk cannot misclassify entries between
        // the listing call and the extraction call.
        let stagedArchiveURL = stagingParentDirectory
            .appendingPathComponent("archive-\(UUID().uuidString).tar")
        do {
            try fileManager.copyItem(at: archiveURL, to: stagedArchiveURL)
        } catch {
            throw Error.listingFailed("Failed to stage archive copy: \(error.localizedDescription)")
        }
        defer { try? fileManager.removeItem(at: stagedArchiveURL) }

        // Step 1: Validate archive metadata before tar is allowed to write anything.
        let entries = try listArchiveEntries(stagedArchiveURL)
        try validatePaths(entries.map(\.path))
        try validatePaths(entries.compactMap { strippedPath(for: $0.path, stripComponents: stripComponents) })
        try validateLinkTargets(entries, stripComponents: stripComponents)

        // Step 2: Create a secure staging directory for extraction.
        // Explicit 0o700 instead of umask-derived perms (matches SecureTempFile precedent).
        let stagingDir = stagingParentDirectory
            .appendingPathComponent("SafeArchiveExtractor-\(UUID().uuidString)")
        do {
            try fileManager.createDirectory(
                at: stagingDir,
                withIntermediateDirectories: true,
                attributes: [.posixPermissions: 0o700]
            )
        } catch {
            throw Error.targetDirectoryCreationFailed(error)
        }

        // Ensure staging directory is cleaned up on all exit paths
        defer {
            try? fileManager.removeItem(at: stagingDir)
        }

        // Step 3: Extract to staging directory from the staged archive copy so the
        // file tar reads is the same one we listed (no on-disk swap window).
        try performExtraction(from: stagedArchiveURL, to: stagingDir, stripComponents: stripComponents)

        // Step 4: Validate extracted contents in staging directory
        // The preflight prevents unsafe writes; this verifies the actual extracted tree.
        try validateNoEscapingSymlinks(in: stagingDir)
        try validateExtractedPaths(in: stagingDir)

        logger.info("Validated extracted contents in staging directory")

        // Step 5: Create target directory if needed
        if !fileManager.fileExists(atPath: targetDirectory.path) {
            do {
                try fileManager.createDirectory(at: targetDirectory, withIntermediateDirectories: true)
            } catch {
                throw Error.targetDirectoryCreationFailed(error)
            }
        }

        // Step 6: Move validated contents from staging to target
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

    private enum ArchiveEntryType {
        case regular
        case symlink
        case hardlink
    }

    private struct ArchiveEntry {
        let path: String
        let type: ArchiveEntryType
        let linkTarget: String?
    }

    /// Lists all archive entries without extracting.
    ///
    /// Uses a single `tar -tvf` invocation and parses both the type prefix and the
    /// trailing path field from each verbose line. The previous implementation ran
    /// two separate `tar` calls and zipped the outputs by line index, which
    /// misclassified entries whenever the two outputs diverged on warnings, locale
    /// noise, or embedded `\n` in member names.
    private static func listArchiveEntries(_ archiveURL: URL) throws -> [ArchiveEntry] {
        let verboseOutput = try runTarList(archiveURL)
        var entries: [ArchiveEntry] = []

        for rawLine in verboseOutput.split(separator: "\n", omittingEmptySubsequences: true) {
            let line = String(rawLine)
            guard let typeChar = line.first else { continue }

            // bsdtar's verbose long format is: `<mode 10c> <links> <owner/group> <size> <date 3-fields> <path>[<-> target>]`.
            // The path field starts after the 9th whitespace-delimited token.
            // We split on whitespace with a max count high enough to keep the path intact.
            let components = line.split(separator: " ", maxSplits: 8, omittingEmptySubsequences: true)
            guard components.count == 9 else { continue }
            var pathField = String(components[8])

            let entryType: ArchiveEntryType
            let linkTarget: String?

            switch typeChar {
            case "l":
                entryType = .symlink
                if let arrowRange = pathField.range(of: " -> ") {
                    linkTarget = String(pathField[arrowRange.upperBound...])
                    pathField = String(pathField[..<arrowRange.lowerBound])
                } else {
                    linkTarget = nil
                }
            case "h":
                entryType = .hardlink
                if let arrowRange = pathField.range(of: " link to ") {
                    linkTarget = String(pathField[arrowRange.upperBound...])
                    pathField = String(pathField[..<arrowRange.lowerBound])
                } else {
                    linkTarget = nil
                }
            default:
                entryType = .regular
                linkTarget = nil
            }

            entries.append(ArchiveEntry(path: pathField, type: entryType, linkTarget: linkTarget))
        }

        return entries
    }

    /// Lists archive contents using libarchive-backed bsdtar. `-f` auto-detects gzip/plain tar.
    /// Sets `LC_ALL=C` so locale-dependent warning text on stderr never confuses parsing.
    private static func runTarList(_ archiveURL: URL) throws -> String {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tar")
        process.arguments = ["-tvf", archiveURL.path]
        var env = ProcessInfo.processInfo.environment
        env["LC_ALL"] = "C"
        env["LANG"] = "C"
        process.environment = env

        let stdout = Pipe()
        let stderr = Pipe()
        let outputLock = NSLock()
        var stdoutData = Data()
        var stderrData = Data()
        process.standardOutput = stdout
        process.standardError = stderr
        stdout.fileHandleForReading.readabilityHandler = { handle in
            let data = handle.availableData
            guard !data.isEmpty else { return }
            outputLock.lock()
            stdoutData.append(data)
            outputLock.unlock()
        }
        stderr.fileHandleForReading.readabilityHandler = { handle in
            let data = handle.availableData
            guard !data.isEmpty else { return }
            outputLock.lock()
            stderrData.append(data)
            outputLock.unlock()
        }

        do {
            try process.run()
            process.waitUntilExit()
        } catch {
            stdout.fileHandleForReading.readabilityHandler = nil
            stderr.fileHandleForReading.readabilityHandler = nil
            throw Error.listingFailed(error.localizedDescription)
        }

        stdout.fileHandleForReading.readabilityHandler = nil
        stderr.fileHandleForReading.readabilityHandler = nil
        outputLock.lock()
        stdoutData.append(stdout.fileHandleForReading.readDataToEndOfFile())
        stderrData.append(stderr.fileHandleForReading.readDataToEndOfFile())
        outputLock.unlock()

        if process.terminationStatus != 0 {
            let errorMessage = String(data: stderrData, encoding: .utf8) ?? "Unknown error"
            throw Error.listingFailed(errorMessage)
        }

        guard let output = String(data: stdoutData, encoding: .utf8) else {
            throw Error.listingFailed("Failed to decode archive listing")
        }

        return output
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

    /// Validates archive symlink and hardlink targets before extraction.
    private static func validateLinkTargets(_ entries: [ArchiveEntry], stripComponents: Int) throws {
        for entry in entries {
            guard let target = entry.linkTarget, !target.isEmpty else { continue }

            switch entry.type {
            case .symlink:
                if target.hasPrefix("/") {
                    throw Error.symlinkEscapeDetected("\(entry.path) -> \(target)")
                }
                try validateRelativeLinkTarget(path: entry.path, target: target, stripComponents: stripComponents)

            case .hardlink:
                try validatePaths([target])

            case .regular:
                continue
            }
        }
    }

    private static func validateRelativeLinkTarget(
        path: String,
        target: String,
        stripComponents: Int
    ) throws {
        guard let linkComponents = strippedComponents(for: path, stripComponents: stripComponents),
              !linkComponents.isEmpty else {
            return
        }

        var targetComponents = Array(linkComponents.dropLast())
        for component in target.components(separatedBy: "/") {
            if component.isEmpty || component == "." {
                continue
            }
            if component == ".." {
                guard !targetComponents.isEmpty else {
                    throw Error.symlinkEscapeDetected("\(path) -> \(target)")
                }
                targetComponents.removeLast()
            } else {
                targetComponents.append(component)
            }
        }
    }

    private static func strippedComponents(for path: String, stripComponents: Int) -> [String]? {
        let normalized = path.components(separatedBy: "/").filter { !$0.isEmpty && $0 != "." }
        guard normalized.count > stripComponents else { return nil }
        return Array(normalized.dropFirst(stripComponents))
    }

    private static func strippedPath(for path: String, stripComponents: Int) -> String? {
        strippedComponents(for: path, stripComponents: stripComponents)?.joined(separator: "/")
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
            "-xf", archiveURL.path,
            "-C", targetDirectory.path,
            "--no-same-owner",        // Don't preserve file ownership
            "--no-same-permissions"   // Use umask instead of archive permissions
        ]

        if stripComponents > 0 {
            args.append("--strip-components=\(stripComponents)")
        }

        process.arguments = args

        let stderr = Pipe()
        let stderrHandle = stderr.fileHandleForReading
        let stderrLock = NSLock()
        var stderrData = Data()
        process.standardError = stderr
        process.standardOutput = FileHandle.nullDevice

        stderrHandle.readabilityHandler = { handle in
            let data = handle.availableData
            guard !data.isEmpty else { return }
            stderrLock.lock()
            stderrData.append(data)
            stderrLock.unlock()
        }

        defer {
            stderrHandle.readabilityHandler = nil
            try? stderrHandle.close()
        }

        do {
            try process.run()
            process.waitUntilExit()
        } catch {
            stderrHandle.readabilityHandler = nil
            throw Error.extractionFailed(error.localizedDescription)
        }

        stderrHandle.readabilityHandler = nil
        stderrLock.lock()
        stderrData.append(stderrHandle.readDataToEndOfFile())
        let extractionErrorData = stderrData
        stderrLock.unlock()

        if process.terminationStatus != 0 {
            let errorMessage = String(data: extractionErrorData, encoding: .utf8) ?? "Unknown error"
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
            includingPropertiesForKeys: [.isSymbolicLinkKey],
            options: []
        ) else { return }

        for case let fileURL as URL in enumerator {
            if (try? fileURL.resourceValues(forKeys: [.isSymbolicLinkKey]).isSymbolicLink) == true {
                continue
            }

            // Resolve the actual path and verify it's within the staging directory.
            guard let resolvedFileCStr = realpath(fileURL.path, nil) else {
                throw Error.pathTraversalDetected(fileURL.path)
            }
            let resolvedPath = String(cString: resolvedFileCStr)
            free(resolvedFileCStr)

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

    // MARK: - Orphan Cleanup

    /// Wall-clock age above which a leftover entry in `stagingParentDirectory` is
    /// considered orphaned (and therefore safe to delete) at app launch.
    private static let staleStagingTTL: TimeInterval = 24 * 60 * 60

    /// Reaps stale staging directories and archive copies that crashed runs left
    /// behind under `<TMPDIR>/TLA+ Studio/`.
    ///
    /// Call from `applicationDidFinishLaunching` as a fire-and-forget Task. Safe
    /// to call repeatedly; only removes entries older than `staleStagingTTL`
    /// to avoid racing concurrent extractions started by the live process.
    static func cleanupStaleStagingDirs() {
        let fileManager = FileManager.default
        let parent = stagingParentDirectory

        guard fileManager.fileExists(atPath: parent.path) else { return }

        let cutoff = Date(timeIntervalSinceNow: -staleStagingTTL)
        let contents: [URL]
        do {
            contents = try fileManager.contentsOfDirectory(
                at: parent,
                includingPropertiesForKeys: [.contentModificationDateKey, .creationDateKey],
                options: [.skipsHiddenFiles]
            )
        } catch {
            logger.debug("cleanupStaleStagingDirs: enumerate failed: \(error.localizedDescription)")
            return
        }

        var removed = 0
        for entry in contents {
            let resourceValues = try? entry.resourceValues(forKeys: [.contentModificationDateKey, .creationDateKey])
            let mtime = resourceValues?.contentModificationDate ?? resourceValues?.creationDate ?? .distantFuture
            guard mtime < cutoff else { continue }
            do {
                try fileManager.removeItem(at: entry)
                removed += 1
            } catch {
                logger.debug("cleanupStaleStagingDirs: failed to remove \(entry.lastPathComponent): \(error.localizedDescription)")
            }
        }

        if removed > 0 {
            logger.info("Reaped \(removed) stale archive-extraction staging entries")
        }
    }
}
