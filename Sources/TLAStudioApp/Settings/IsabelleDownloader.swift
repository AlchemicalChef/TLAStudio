import CryptoKit
import Foundation
import os

private let logger = Log.logger(category: "IsabelleDownloader")

/// Manages downloading and installing Isabelle on-demand
@MainActor
final class IsabelleDownloader: ObservableObject {
    static let shared = IsabelleDownloader()

    // MARK: - State

    enum State: Equatable {
        case notInstalled
        case checking
        case downloading(progress: Double)
        case extracting
        case installed(path: String)
        case error(String)

        var isInstalled: Bool {
            if case .installed = self { return true }
            return false
        }

        var isWorking: Bool {
            switch self {
            case .checking, .downloading, .extracting:
                return true
            default:
                return false
            }
        }
    }

    @Published private(set) var state: State = .notInstalled
    @Published private(set) var downloadedBytes: Int64 = 0
    @Published private(set) var totalBytes: Int64 = 0

    private var downloadTask: URLSessionDownloadTask?
    private var progressObservation: NSKeyValueObservation?

    // FIX: Clean up download task and observation on deallocation to prevent resource leaks
    deinit {
        downloadTask?.cancel()
        progressObservation?.invalidate()
    }

    // MARK: - Configuration

    private static let isabelleVersion = "Isabelle2024"
    private static let downloadURL: URL = {
        #if arch(arm64)
        guard let url = URL(string: "https://isabelle.in.tum.de/website-Isabelle2024/dist/Isabelle2024_macos_arm64.tar.gz") else {
            fatalError("Invalid hardcoded Isabelle download URL")
        }
        return url
        #else
        guard let url = URL(string: "https://isabelle.in.tum.de/website-Isabelle2024/dist/Isabelle2024_macos.tar.gz") else {
            fatalError("Invalid hardcoded Isabelle download URL")
        }
        return url
        #endif
    }()

    /// Expected SHA-256 hash of the downloaded archive for integrity verification.
    /// Update these hashes when upgrading the Isabelle version.
    private static let expectedSHA256: String = {
        #if arch(arm64)
        return "dcc0149e815158e6e3dbab67aff9a9cdf0e498a771194325a8ed75cd7d24ad4c"
        #else
        return "c1db0e86fa2fb39ed52e18c60e49a32e52474dd53e2e4d4b1e88850d4e60a01c"
        #endif
    }()

    /// Verifies the SHA-256 hash of a downloaded file.
    /// - Parameters:
    ///   - fileURL: URL to the downloaded file
    /// - Returns: true if the hash matches the expected value
    private func verifySHA256(of fileURL: URL) throws -> Bool {
        let fileData = try Data(contentsOf: fileURL)
        let digest = SHA256.hash(data: fileData)
        let hashString = digest.map { String(format: "%02x", $0) }.joined()
        let matches = hashString == Self.expectedSHA256
        if !matches {
            logger.error("SHA-256 mismatch: expected \(Self.expectedSHA256), got \(hashString)")
        }
        return matches
    }

    /// Where Isabelle gets installed (Application Support)
    private var installDirectory: URL {
        guard let appSupport = FileManager.default.urls(for: .applicationSupportDirectory, in: .userDomainMask).first else {
            fatalError("Application Support directory unavailable")
        }
        return appSupport.appendingPathComponent("TLA+ Studio/Provers", isDirectory: true)
    }

    /// Path to installed Isabelle
    var isabellePath: URL {
        installDirectory.appendingPathComponent("isabelle", isDirectory: true)
    }

    /// Path to Isabelle binary
    var isabelleBinaryPath: URL {
        isabellePath.appendingPathComponent("bin/isabelle")
    }

    // MARK: - Initialization

    init() {
        checkInstallation()
    }

    // MARK: - Check Installation

    func checkInstallation() {
        state = .checking

        Task {
            let fileManager = FileManager.default

            // Check if Isabelle directory exists
            let isabelleDir = isabellePath
            let isabelleBin = isabelleBinaryPath

            if fileManager.fileExists(atPath: isabelleDir.path) &&
               fileManager.fileExists(atPath: isabelleBin.path) {
                // Verify it's executable
                if fileManager.isExecutableFile(atPath: isabelleBin.path) {
                    state = .installed(path: isabelleDir.path)
                    logger.info("Isabelle found at: \(isabelleDir.path)")
                    return
                }
            }

            // Check bundled location (in case it was included in build)
            if let bundlePath = Bundle.main.resourcePath {
                let bundledIsabelle = URL(fileURLWithPath: bundlePath)
                    .appendingPathComponent("Provers/Isabelle")
                if fileManager.fileExists(atPath: bundledIsabelle.path) {
                    state = .installed(path: bundledIsabelle.path)
                    logger.info("Bundled Isabelle found at: \(bundledIsabelle.path)")
                    return
                }
            }

            state = .notInstalled
            logger.info("Isabelle not installed")
        }
    }

    // MARK: - Download

    func download() {
        guard !state.isWorking else { return }

        state = .downloading(progress: 0)
        downloadedBytes = 0
        totalBytes = 0

        logger.info("Starting Isabelle download from: \(Self.downloadURL)")

        let session = URLSession(configuration: .default)
        let task = session.downloadTask(with: Self.downloadURL) { [weak self] tempURL, response, error in
            Task { @MainActor in
                guard let self = self else { return }

                if let error = error {
                    if (error as NSError).code == NSURLErrorCancelled {
                        self.state = .notInstalled
                    } else {
                        self.state = .error("Download failed: \(error.localizedDescription)")
                        logger.error("Isabelle download failed: \(error.localizedDescription)")
                    }
                    return
                }

                guard let tempURL = tempURL else {
                    self.state = .error("Download failed: No file received")
                    return
                }

                // Verify archive integrity before extraction
                do {
                    guard try self.verifySHA256(of: tempURL) else {
                        self.state = .error("Download integrity check failed: SHA-256 hash mismatch. The download may be corrupted or tampered with.")
                        try? FileManager.default.removeItem(at: tempURL)
                        return
                    }
                    logger.info("SHA-256 verification passed")
                } catch {
                    self.state = .error("Failed to verify download integrity: \(error.localizedDescription)")
                    try? FileManager.default.removeItem(at: tempURL)
                    return
                }

                // Extract the archive
                await self.extractArchive(from: tempURL)
            }
        }

        // Observe progress
        progressObservation = task.progress.observe(\.fractionCompleted) { [weak self] progress, _ in
            Task { @MainActor in
                guard let self = self else { return }
                self.state = .downloading(progress: progress.fractionCompleted)
                self.downloadedBytes = progress.completedUnitCount
                self.totalBytes = progress.totalUnitCount
            }
        }

        downloadTask = task
        task.resume()
    }

    // MARK: - Cancel

    func cancel() {
        downloadTask?.cancel()
        downloadTask = nil
        progressObservation?.invalidate()
        progressObservation = nil
        state = .notInstalled
    }

    // MARK: - Extract

    private func extractArchive(from tempURL: URL) async {
        state = .extracting

        logger.info("Extracting Isabelle archive...")

        do {
            let fileManager = FileManager.default

            // Create install directory
            try fileManager.createDirectory(at: installDirectory, withIntermediateDirectories: true)

            // Remove existing Isabelle if present
            let targetDir = isabellePath
            if fileManager.fileExists(atPath: targetDir.path) {
                try fileManager.removeItem(at: targetDir)
            }

            // Extract using SafeArchiveExtractor (validates paths and prevents symlink attacks)
            try SafeArchiveExtractor.extract(from: tempURL, to: installDirectory)

            // Rename extracted directory to "isabelle"
            let contents = try fileManager.contentsOfDirectory(at: installDirectory, includingPropertiesForKeys: nil)
            if let extractedDir = contents.first(where: { $0.lastPathComponent.hasPrefix("Isabelle") }) {
                try fileManager.moveItem(at: extractedDir, to: targetDir)
            }

            // Clean up temp file
            try? fileManager.removeItem(at: tempURL)

            // Verify installation
            if fileManager.isExecutableFile(atPath: isabelleBinaryPath.path) {
                state = .installed(path: targetDir.path)
                logger.info("Isabelle installed successfully at: \(targetDir.path)")
            } else {
                state = .error("Installation verification failed")
            }

        } catch {
            state = .error("Extraction failed: \(error.localizedDescription)")
            logger.error("Isabelle extraction failed: \(error.localizedDescription)")
        }
    }

    // MARK: - Uninstall

    func uninstall() {
        guard state.isInstalled else { return }

        do {
            let fileManager = FileManager.default
            if fileManager.fileExists(atPath: isabellePath.path) {
                try fileManager.removeItem(at: isabellePath)
            }
            state = .notInstalled
            logger.info("Isabelle uninstalled")
        } catch {
            state = .error("Failed to uninstall: \(error.localizedDescription)")
        }
    }

    // MARK: - Helpers

    var formattedProgress: String {
        guard totalBytes > 0 else { return "Starting..." }
        let downloaded = ByteCountFormatter.string(fromByteCount: downloadedBytes, countStyle: .file)
        let total = ByteCountFormatter.string(fromByteCount: totalBytes, countStyle: .file)
        return "\(downloaded) / \(total)"
    }

    var estimatedSize: String {
        // Isabelle is approximately 1GB compressed, 3GB uncompressed
        return "~1 GB download, ~3 GB installed"
    }
}
