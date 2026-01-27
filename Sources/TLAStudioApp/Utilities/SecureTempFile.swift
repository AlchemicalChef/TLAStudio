import Foundation
import os

private let logger = Logger(subsystem: "com.tlastudio", category: "SecureTempFile")

// MARK: - Secure Temp File

/// Provides secure temporary file creation that prevents symlink attacks.
/// Uses POSIX open() with O_CREAT | O_EXCL to atomically create files.
enum SecureTempFile {

    // MARK: - Errors

    enum Error: Swift.Error, LocalizedError {
        case directoryCreationFailed(Swift.Error)
        case directoryOwnershipMismatch
        case fileCreationFailed(Swift.Error)
        case writeError(Swift.Error)

        var errorDescription: String? {
            switch self {
            case .directoryCreationFailed(let error):
                return "Failed to create secure temp directory: \(error.localizedDescription)"
            case .directoryOwnershipMismatch:
                return "Temp directory ownership verification failed"
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

    /// Cleans up a secure temp file.
    /// - Parameter url: URL of the file to remove
    static func cleanup(_ url: URL) {
        // Only clean up files in our secure temp directory
        guard url.path.hasPrefix(secureTempDirectory.path) else {
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

    /// Ensures the secure temp directory exists with proper ownership.
    private static func ensureSecureDirectory() throws {
        let fileManager = FileManager.default
        let directory = secureTempDirectory
        let uid = getuid()

        if fileManager.fileExists(atPath: directory.path) {
            // Verify ownership - directory must be owned by current user
            do {
                let attrs = try fileManager.attributesOfItem(atPath: directory.path)
                if let ownerID = attrs[.ownerAccountID] as? NSNumber {
                    if ownerID.uint32Value != uid {
                        // Directory exists but is owned by someone else - security risk
                        logger.error("Temp directory owned by UID \(ownerID) instead of \(uid)")
                        throw Error.directoryOwnershipMismatch
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
