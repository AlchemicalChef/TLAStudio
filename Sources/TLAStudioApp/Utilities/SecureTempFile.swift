import Foundation
import os

private let logger = Log.logger(category: "SecureTempFile")

// MARK: - Secure Temp File

/// Provides secure temporary file creation that prevents symlink attacks.
/// Uses POSIX open() with O_CREAT | O_EXCL to atomically create files.
enum SecureTempFile {

    // MARK: - Errors

    enum Error: Swift.Error, LocalizedError {
        case directoryCreationFailed(Swift.Error)
        case directoryOwnershipMismatch
        case directoryPermissionsMismatch(actual: UInt16, expected: UInt16)
        case fileCreationFailed(Swift.Error)
        case writeError(Swift.Error)

        var errorDescription: String? {
            switch self {
            case .directoryCreationFailed(let error):
                return "Failed to create secure temp directory: \(error.localizedDescription)"
            case .directoryOwnershipMismatch:
                return "Temp directory ownership verification failed"
            case .directoryPermissionsMismatch(let actual, let expected):
                return String(
                    format: "Temp directory has insecure permissions (mode 0o%o, expected 0o%o)",
                    actual, expected
                )
            case .fileCreationFailed(let error):
                return "Failed to create secure temp file: \(error.localizedDescription)"
            case .writeError(let error):
                return "Failed to write to temp file: \(error.localizedDescription)"
            }
        }
    }

    // MARK: - Configuration

    /// Base directory for secure temp files (inside /tmp with user-specific subdirectory)
    private static var secureTempDirectory: URL {
        let uid = getuid()
        return URL(fileURLWithPath: "/tmp/TLAStudio-\(uid)", isDirectory: true)
    }

    // MARK: - Public API

    /// Creates a secure temporary file with the given content.
    /// - Parameters:
    ///   - prefix: Prefix for the filename (e.g., "MyModule")
    ///   - extension: File extension (e.g., "tla")
    ///   - content: Content to write to the file
    /// - Returns: URL to the created file
    /// - Throws: SecureTempFile.Error if creation fails
    static func create(prefix: String, extension ext: String, content: String) throws -> URL {
        // Ensure secure directory exists with proper ownership
        try ensureSecureDirectory()

        // Generate unique filename with UUID
        let filename = "\(sanitizeFilename(prefix))-\(UUID().uuidString).\(ext)"
        let fileURL = secureTempDirectory.appendingPathComponent(filename)

        // Create file atomically using POSIX open with O_EXCL
        // This prevents TOCTOU race conditions and symlink attacks
        let fd = fileURL.path.withCString { path in
            open(path, O_WRONLY | O_CREAT | O_EXCL, 0o600)
        }

        guard fd >= 0 else {
            let error = NSError(domain: NSPOSIXErrorDomain, code: Int(errno),
                              userInfo: [NSLocalizedDescriptionKey: String(cString: strerror(errno))])
            throw Error.fileCreationFailed(error)
        }

        // Write content to the file
        defer { Darwin.close(fd) }

        guard let data = content.data(using: .utf8) else {
            throw Error.writeError(NSError(domain: "SecureTempFile", code: 1,
                                          userInfo: [NSLocalizedDescriptionKey: "Failed to encode content as UTF-8"]))
        }

        // Handle empty data case - nothing to write, return early (file is created but empty)
        guard !data.isEmpty else {
            logger.debug("Created empty secure temp file: \(fileURL.path)")
            return fileURL
        }

        let bytesWritten = data.withUnsafeBytes { buffer in
            // Safe: we've checked data is not empty, so baseAddress is guaranteed non-nil
            guard let baseAddress = buffer.baseAddress else { return -1 }
            return write(fd, baseAddress, data.count)
        }

        guard bytesWritten == data.count else {
            // Clean up the partially written file
            try? FileManager.default.removeItem(at: fileURL)
            let error = NSError(domain: NSPOSIXErrorDomain, code: Int(errno),
                              userInfo: [NSLocalizedDescriptionKey: "Write incomplete: \(bytesWritten)/\(data.count) bytes"])
            throw Error.writeError(error)
        }

        logger.debug("Created secure temp file: \(fileURL.path)")
        return fileURL
    }

    /// Creates a secure temporary file from data.
    /// - Parameters:
    ///   - prefix: Prefix for the filename
    ///   - extension: File extension
    ///   - data: Data to write to the file
    /// - Returns: URL to the created file
    static func create(prefix: String, extension ext: String, data: Data) throws -> URL {
        try ensureSecureDirectory()

        let filename = "\(sanitizeFilename(prefix))-\(UUID().uuidString).\(ext)"
        let fileURL = secureTempDirectory.appendingPathComponent(filename)

        let fd = fileURL.path.withCString { path in
            open(path, O_WRONLY | O_CREAT | O_EXCL, 0o600)
        }

        guard fd >= 0 else {
            let error = NSError(domain: NSPOSIXErrorDomain, code: Int(errno),
                              userInfo: [NSLocalizedDescriptionKey: String(cString: strerror(errno))])
            throw Error.fileCreationFailed(error)
        }

        defer { Darwin.close(fd) }

        // Handle empty data case - nothing to write, return early (file is created but empty)
        guard !data.isEmpty else {
            logger.debug("Created empty secure temp file: \(fileURL.path)")
            return fileURL
        }

        let bytesWritten = data.withUnsafeBytes { buffer in
            // Safe: we've checked data is not empty, so baseAddress is guaranteed non-nil
            guard let baseAddress = buffer.baseAddress else { return -1 }
            return write(fd, baseAddress, data.count)
        }

        guard bytesWritten == data.count else {
            try? FileManager.default.removeItem(at: fileURL)
            let error = NSError(domain: NSPOSIXErrorDomain, code: Int(errno),
                              userInfo: [NSLocalizedDescriptionKey: "Write incomplete"])
            throw Error.writeError(error)
        }

        logger.debug("Created secure temp file: \(fileURL.path)")
        return fileURL
    }

    /// Creates a secure temp file with an *exact* filename (no UUID suffix) by placing it
    /// inside a unique per-call subdirectory. Required when an external tool enforces
    /// `filename == moduleName` (e.g., TLA+ SANY rejects `MyModule-<UUID>.tla`).
    ///
    /// - Parameters:
    ///   - name: Exact filename base (no extension), e.g. `"MutualExclusion"`.
    ///   - extension: File extension, e.g. `"tla"`.
    ///   - content: Text content to write.
    /// - Returns: URL to the created file at `<tempDir>/<UUID>/<name>.<ext>`.
    static func createWithExactName(
        name: String,
        extension ext: String,
        content: String
    ) throws -> URL {
        try ensureSecureDirectory()

        let sanitized = sanitizeFilename(name)
        guard !sanitized.isEmpty else {
            throw Error.fileCreationFailed(NSError(
                domain: "SecureTempFile", code: 2,
                userInfo: [NSLocalizedDescriptionKey: "Exact-name file requires a non-empty name after sanitization"]
            ))
        }

        // Per-call subdirectory isolates the stable filename from collisions with other runs.
        let subdirectory = secureTempDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        do {
            try FileManager.default.createDirectory(
                at: subdirectory,
                withIntermediateDirectories: true,
                attributes: [.posixPermissions: 0o700]
            )
        } catch {
            throw Error.directoryCreationFailed(error)
        }

        let fileURL = subdirectory.appendingPathComponent("\(sanitized).\(ext)")

        let fd = fileURL.path.withCString { path in
            open(path, O_WRONLY | O_CREAT | O_EXCL, 0o600)
        }

        guard fd >= 0 else {
            let error = NSError(domain: NSPOSIXErrorDomain, code: Int(errno),
                              userInfo: [NSLocalizedDescriptionKey: String(cString: strerror(errno))])
            try? FileManager.default.removeItem(at: subdirectory)
            throw Error.fileCreationFailed(error)
        }

        defer { Darwin.close(fd) }

        guard let data = content.data(using: .utf8) else {
            try? FileManager.default.removeItem(at: subdirectory)
            throw Error.writeError(NSError(domain: "SecureTempFile", code: 1,
                userInfo: [NSLocalizedDescriptionKey: "Failed to encode content as UTF-8"]))
        }

        guard !data.isEmpty else {
            logger.debug("Created empty secure temp file: \(fileURL.path)")
            return fileURL
        }

        let bytesWritten = data.withUnsafeBytes { buffer in
            guard let baseAddress = buffer.baseAddress else { return -1 }
            return write(fd, baseAddress, data.count)
        }

        guard bytesWritten == data.count else {
            try? FileManager.default.removeItem(at: subdirectory)
            let error = NSError(domain: NSPOSIXErrorDomain, code: Int(errno),
                              userInfo: [NSLocalizedDescriptionKey: "Write incomplete: \(bytesWritten)/\(data.count) bytes"])
            throw Error.writeError(error)
        }

        logger.debug("Created secure temp file with exact name: \(fileURL.path)")
        return fileURL
    }

    /// Cleans up a secure temp file.
    /// - Parameter url: URL of the file to remove
    static func cleanup(_ url: URL) {
        // Only clean up files in our secure temp directory. Use the robust
        // membership check (standardized path + trailing slash) so a sibling
        // directory like `<secure>-evil/…` can't satisfy a bare prefix (e2e Low).
        guard isManagedTemporaryFile(url) else {
            logger.warning("Refusing to clean up file outside secure temp directory: \(url.path)")
            return
        }

        do {
            try FileManager.default.removeItem(at: url)
            logger.debug("Cleaned up secure temp file: \(url.path)")
        } catch {
            logger.warning("Failed to clean up temp file: \(error.localizedDescription)")
        }
    }

    static func isManagedTemporaryFile(_ url: URL) -> Bool {
        url.standardized.path.hasPrefix(secureTempDirectory.standardized.path + "/")
    }

    static func cleanupContainer(for url: URL?) {
        guard let url else { return }
        let standardizedDirectory = secureTempDirectory.standardized
        let parent = url.deletingLastPathComponent().standardized

        guard parent.deletingLastPathComponent().path == standardizedDirectory.path,
              parent.path.hasPrefix(standardizedDirectory.path + "/") else {
            cleanup(url)
            return
        }

        do {
            try FileManager.default.removeItem(at: parent)
            logger.debug("Cleaned up secure temp container: \(parent.path)")
        } catch {
            logger.warning("Failed to clean up temp container: \(error.localizedDescription)")
        }
    }

    /// Cleans up all temp files created by this app.
    static func cleanupAll() {
        let fileManager = FileManager.default
        let directory = secureTempDirectory

        guard fileManager.fileExists(atPath: directory.path) else { return }

        do {
            let files = try fileManager.contentsOfDirectory(at: directory, includingPropertiesForKeys: nil)
            for file in files {
                try? fileManager.removeItem(at: file)
            }
            logger.info("Cleaned up \(files.count) temp files")
        } catch {
            logger.warning("Failed to enumerate temp directory: \(error.localizedDescription)")
        }
    }

    // MARK: - Private Helpers

    /// Ensures the secure temp directory exists with proper ownership AND permissions.
    ///
    /// Both checks are required for defense-in-depth: ownership stops a foreign UID
    /// from siting an attacker-controlled dir at our path, while the 0o700 mode check
    /// stops a previously-created dir that has since been chmod'd looser (user error,
    /// malware artifact, third-party tool) from being silently re-used.
    private static func ensureSecureDirectory() throws {
        let fileManager = FileManager.default
        let directory = secureTempDirectory
        let uid = getuid()
        let requiredMode: UInt16 = 0o700

        if fileManager.fileExists(atPath: directory.path) {
            // Verify ownership AND permissions - existing dir must be ours AND restricted.
            do {
                let attrs = try fileManager.attributesOfItem(atPath: directory.path)
                if let ownerID = attrs[.ownerAccountID] as? NSNumber,
                   ownerID.uint32Value != uid {
                    // Directory exists but is owned by someone else - security risk
                    logger.error("Temp directory owned by UID \(ownerID) instead of \(uid)")
                    throw Error.directoryOwnershipMismatch
                }
                // POSIX permissions are stored as NSNumber under FileAttributeKey.posixPermissions.
                if let perms = attrs[.posixPermissions] as? NSNumber {
                    let actual = perms.uint16Value & 0o777
                    if actual != requiredMode {
                        logger.error("Temp directory has mode 0o\(String(actual, radix: 8)) (expected 0o\(String(requiredMode, radix: 8)))")
                        throw Error.directoryPermissionsMismatch(actual: actual, expected: requiredMode)
                    }
                }
            } catch let error as Error {
                throw error
            } catch {
                throw Error.directoryCreationFailed(error)
            }
        } else {
            // Create directory with restrictive permissions
            do {
                try fileManager.createDirectory(
                    at: directory,
                    withIntermediateDirectories: true,
                    attributes: [.posixPermissions: 0o700]
                )
                logger.debug("Created secure temp directory: \(directory.path)")
            } catch {
                throw Error.directoryCreationFailed(error)
            }
        }
    }

    /// Sanitizes a filename by removing unsafe characters.
    private static func sanitizeFilename(_ name: String) -> String {
        // Allow only alphanumeric characters, underscores, and hyphens
        let allowed = CharacterSet.alphanumerics.union(CharacterSet(charactersIn: "_-"))
        return String(name.unicodeScalars.filter { allowed.contains($0) })
    }
}
