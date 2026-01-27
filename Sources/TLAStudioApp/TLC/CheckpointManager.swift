import Foundation

// MARK: - Checkpoint Manager

/// Actor that manages TLC checkpoint discovery and cleanup
actor CheckpointManager {
    static let shared = CheckpointManager()

    // MARK: - Discovery

    /// Discover all checkpoints in a directory for a given spec
    /// - Parameters:
    ///   - directory: The metadir where checkpoints are stored
    ///   - specName: Name of the specification (used for display)
    /// - Returns: Array of discovered checkpoints, sorted by date (newest first)
    func discoverCheckpoints(in directory: URL, specName: String) async throws -> [CheckpointInfo] {
        let fileManager = FileManager.default

        guard fileManager.fileExists(atPath: directory.path) else {
            return []
        }

        let contents = try fileManager.contentsOfDirectory(
            at: directory,
            includingPropertiesForKeys: [.isDirectoryKey, .creationDateKey],
            options: [.skipsHiddenFiles]
        )

        var checkpoints: [CheckpointInfo] = []

        for itemURL in contents {
            let resourceValues = try itemURL.resourceValues(forKeys: [.isDirectoryKey])
            guard resourceValues.isDirectory == true else { continue }

            if let checkpoint = CheckpointInfo.from(directoryURL: itemURL, specName: specName) {
                checkpoints.append(checkpoint)
            }
        }

        // Sort by creation date, newest first
        return checkpoints.sorted { $0.createdAt > $1.createdAt }
    }

    /// Discover checkpoints for a spec file, using the default metadir location
    /// - Parameter specURL: URL to the TLA+ specification file
    /// - Returns: Array of discovered checkpoints
    func discoverCheckpoints(forSpec specURL: URL) async throws -> [CheckpointInfo] {
        let metadir = defaultMetadir(for: specURL)
        let specName = specURL.deletingPathExtension().lastPathComponent
        return try await discoverCheckpoints(in: metadir, specName: specName)
    }

    // MARK: - Validation

    /// Check if a checkpoint is valid and can be used for recovery
    /// - Parameter checkpoint: The checkpoint to validate
    /// - Returns: True if the checkpoint appears valid
    func validateCheckpoint(_ checkpoint: CheckpointInfo) -> Bool {
        let fileManager = FileManager.default

        // Check directory exists
        guard fileManager.fileExists(atPath: checkpoint.directoryURL.path) else {
            return false
        }

        // Check for expected checkpoint files
        let expectedFiles = ["queue.chkpt", "states.chkpt"]
        for fileName in expectedFiles {
            let filePath = checkpoint.directoryURL.appendingPathComponent(fileName).path
            if fileManager.fileExists(atPath: filePath) {
                return true  // At least one checkpoint file exists
            }
        }

        // If we got here, directory exists but no checkpoint files found
        // The directory might still be a valid checkpoint from an older TLC version
        return true
    }

    // MARK: - Cleanup

    /// Remove old checkpoints, keeping only the most recent ones
    /// - Parameters:
    ///   - directory: Directory containing checkpoints
    ///   - keepRecent: Number of recent checkpoints to keep
    /// - Returns: Number of checkpoints removed
    @discardableResult
    func cleanupOldCheckpoints(in directory: URL, keepRecent: Int = 3) async throws -> Int {
        let specName = "cleanup"  // Not used for cleanup
        let checkpoints = try await discoverCheckpoints(in: directory, specName: specName)

        guard checkpoints.count > keepRecent else {
            return 0
        }

        // Checkpoints are already sorted newest first, so skip the first `keepRecent`
        let toRemove = Array(checkpoints.dropFirst(keepRecent))

        var removedCount = 0
        for checkpoint in toRemove {
            do {
                try FileManager.default.removeItem(at: checkpoint.directoryURL)
                removedCount += 1
            } catch {
                print("Failed to remove checkpoint \(checkpoint.id): \(error)")
            }
        }

        return removedCount
    }

    /// Delete a specific checkpoint
    /// - Parameter checkpoint: The checkpoint to delete
    func deleteCheckpoint(_ checkpoint: CheckpointInfo) throws {
        try FileManager.default.removeItem(at: checkpoint.directoryURL)
    }

    // MARK: - Paths

    /// Get the default metadir path for a specification
    /// - Parameter specURL: URL to the TLA+ specification
    /// - Returns: URL to the default metadir
    func defaultMetadir(for specURL: URL) -> URL {
        let specDir = specURL.deletingLastPathComponent()
        let specName = specURL.deletingPathExtension().lastPathComponent
        return specDir.appendingPathComponent("\(specName).toolbox")
    }

    /// Create the metadir if it doesn't exist
    /// - Parameter specURL: URL to the TLA+ specification
    /// - Returns: URL to the created/existing metadir
    func ensureMetadir(for specURL: URL) throws -> URL {
        let metadir = defaultMetadir(for: specURL)
        try FileManager.default.createDirectory(at: metadir, withIntermediateDirectories: true)
        return metadir
    }
}

// MARK: - Checkpoint Errors

enum CheckpointError: Error, LocalizedError {
    case notFound(String)
    case invalidCheckpoint(String)
    case recoveryFailed(String)
    case cleanupFailed(String)

    var errorDescription: String? {
        switch self {
        case .notFound(let id):
            return "Checkpoint '\(id)' not found."
        case .invalidCheckpoint(let id):
            return "Checkpoint '\(id)' is invalid or corrupted."
        case .recoveryFailed(let message):
            return "Failed to recover from checkpoint: \(message)"
        case .cleanupFailed(let message):
            return "Failed to clean up checkpoints: \(message)"
        }
    }
}
