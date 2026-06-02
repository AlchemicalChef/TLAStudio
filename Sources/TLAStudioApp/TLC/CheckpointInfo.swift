import Foundation

// MARK: - Checkpoint Info

/// Information about a TLC checkpoint
struct CheckpointInfo: Codable, Identifiable, Equatable {
    /// Unique identifier (directory name, typically a timestamp)
    let id: String

    /// URL to the checkpoint directory
    let directoryURL: URL

    /// When the checkpoint was created
    let createdAt: Date

    /// Name of the specification that was being checked
    let specName: String

    /// Number of distinct states at checkpoint time (if known)
    let distinctStates: UInt64?

    /// Number of states found at checkpoint time (if known)
    let statesFound: UInt64?

    /// Whether this checkpoint appears valid
    var isValid: Bool {
        Self.containsCheckpointArtifacts(in: directoryURL)
    }

    /// Human-readable description of the checkpoint
    var displayName: String {
        let formatter = DateFormatter()
        formatter.dateStyle = .short
        formatter.timeStyle = .medium
        return "\(specName) - \(formatter.string(from: createdAt))"
    }

    /// Relative age description
    var ageDescription: String {
        let formatter = RelativeDateTimeFormatter()
        formatter.unitsStyle = .abbreviated
        return formatter.localizedString(for: createdAt, relativeTo: Date())
    }

    /// Size of checkpoint directory on disk
    var diskSize: UInt64? {
        do {
            var totalSize: UInt64 = 0
            let enumerator = FileManager.default.enumerator(
                at: directoryURL,
                includingPropertiesForKeys: [.isRegularFileKey, .fileSizeKey],
                options: [.skipsHiddenFiles]
            )

            while let fileURL = enumerator?.nextObject() as? URL {
                let resourceValues = try fileURL.resourceValues(forKeys: [.isRegularFileKey, .fileSizeKey])
                guard resourceValues.isRegularFile == true else { continue }
                totalSize += UInt64(resourceValues.fileSize ?? 0)
            }
            return totalSize
        } catch {
            return nil
        }
    }

    /// Formatted disk size string
    var formattedDiskSize: String {
        guard let size = diskSize else { return "Unknown" }
        return ByteCountFormatter.string(fromByteCount: Int64(size), countStyle: .file)
    }
}

// MARK: - Checkpoint Status

/// Status of checkpoint operations
enum CheckpointStatus: Equatable {
    case none
    case saving
    case saved(CheckpointInfo)
    case restoring(CheckpointInfo)
    case restored(CheckpointInfo)
    case failed(String)

    var isActive: Bool {
        switch self {
        case .saving, .restoring:
            return true
        default:
            return false
        }
    }

    var displayMessage: String {
        switch self {
        case .none:
            return ""
        case .saving:
            return "Creating checkpoint..."
        case .saved(let info):
            return "Checkpoint saved: \(info.displayName)"
        case .restoring(let info):
            return "Restoring from \(info.displayName)..."
        case .restored(let info):
            return "Restored from \(info.displayName)"
        case .failed(let message):
            return "Checkpoint failed: \(message)"
        }
    }
}

// MARK: - Checkpoint Directory Parsing

extension CheckpointInfo {
    /// TLC checkpoint directories are named with format: YY-MM-DD-HH-MM-SS[.SSS]
    static let directoryDateFormat = "yy-MM-dd-HH-mm-ss"
    static let directoryDateFormatWithMilliseconds = "yy-MM-dd-HH-mm-ss.SSS"

    /// Create a CheckpointInfo from a checkpoint directory URL
    /// - Parameters:
    ///   - directoryURL: URL to the checkpoint directory
    ///   - specName: Name of the specification
    /// - Returns: CheckpointInfo if the directory appears to be a valid checkpoint
    static func from(directoryURL: URL, specName: String) -> CheckpointInfo? {
        let dirName = directoryURL.lastPathComponent

        let createdAt: Date
        if let date = parseCheckpointDate(from: dirName) {
            createdAt = date
        } else {
            // Fall back to directory modification date
            do {
                let attrs = try FileManager.default.attributesOfItem(atPath: directoryURL.path)
                createdAt = attrs[.modificationDate] as? Date ?? Date()
            } catch {
                createdAt = Date()
            }
        }

        guard containsCheckpointArtifacts(in: directoryURL) else {
            return nil
        }

        return CheckpointInfo(
            id: dirName,
            directoryURL: directoryURL,
            createdAt: createdAt,
            specName: specName,
            distinctStates: nil,
            statesFound: nil
        )
    }

    static func parseCheckpointDate(from directoryName: String) -> Date? {
        for format in [directoryDateFormatWithMilliseconds, directoryDateFormat] {
            let formatter = DateFormatter()
            formatter.locale = Locale(identifier: "en_US_POSIX")
            formatter.dateFormat = format
            formatter.isLenient = false
            if let date = formatter.date(from: directoryName) {
                return date
            }
        }
        return nil
    }

    static func containsCheckpointArtifacts(in directoryURL: URL) -> Bool {
        var isDirectory: ObjCBool = false
        guard FileManager.default.fileExists(atPath: directoryURL.path, isDirectory: &isDirectory),
              isDirectory.boolValue else {
            return false
        }

        let expectedFiles = ["queue.chkpt", "states.chkpt"]
        if expectedFiles.contains(where: { fileName in
            FileManager.default.fileExists(atPath: directoryURL.appendingPathComponent(fileName).path)
        }) {
            return true
        }

        guard let contents = try? FileManager.default.contentsOfDirectory(
            at: directoryURL,
            includingPropertiesForKeys: [.isRegularFileKey],
            options: [.skipsHiddenFiles]
        ) else {
            return false
        }

        return contents.contains { url in
            guard (try? url.resourceValues(forKeys: [.isRegularFileKey]).isRegularFile) == true else {
                return false
            }
            return url.lastPathComponent.hasSuffix(".chkpt")
        }
    }
}
