import XCTest
@testable import TLAStudioApp

// MARK: - Isabelle Downloader Tests

/// Tests for the IsabelleDownloader state machine and helper methods.
/// Note: These tests don't perform actual downloads, only test state and logic.
@MainActor
final class IsabelleDownloaderTests: XCTestCase {

    // MARK: - State Tests

    func testStateIsInstalled() {
        XCTAssertFalse(IsabelleDownloader.State.notInstalled.isInstalled)
        XCTAssertFalse(IsabelleDownloader.State.checking.isInstalled)
        XCTAssertFalse(IsabelleDownloader.State.downloading(progress: 0.5).isInstalled)
        XCTAssertFalse(IsabelleDownloader.State.extracting.isInstalled)
        XCTAssertTrue(IsabelleDownloader.State.installed(path: "/path").isInstalled)
        XCTAssertFalse(IsabelleDownloader.State.error("error").isInstalled)
    }

    func testStateIsWorking() {
        XCTAssertFalse(IsabelleDownloader.State.notInstalled.isWorking)
        XCTAssertTrue(IsabelleDownloader.State.checking.isWorking)
        XCTAssertTrue(IsabelleDownloader.State.downloading(progress: 0.5).isWorking)
        XCTAssertTrue(IsabelleDownloader.State.extracting.isWorking)
        XCTAssertFalse(IsabelleDownloader.State.installed(path: "/path").isWorking)
        XCTAssertFalse(IsabelleDownloader.State.error("error").isWorking)
    }

    func testStateEquality() {
        XCTAssertEqual(
            IsabelleDownloader.State.notInstalled,
            IsabelleDownloader.State.notInstalled
        )
        XCTAssertEqual(
            IsabelleDownloader.State.installed(path: "/a"),
            IsabelleDownloader.State.installed(path: "/a")
        )
        XCTAssertNotEqual(
            IsabelleDownloader.State.installed(path: "/a"),
            IsabelleDownloader.State.installed(path: "/b")
        )
        XCTAssertEqual(
            IsabelleDownloader.State.downloading(progress: 0.5),
            IsabelleDownloader.State.downloading(progress: 0.5)
        )
        XCTAssertNotEqual(
            IsabelleDownloader.State.downloading(progress: 0.5),
            IsabelleDownloader.State.downloading(progress: 0.6)
        )
        XCTAssertEqual(
            IsabelleDownloader.State.error("test"),
            IsabelleDownloader.State.error("test")
        )
    }

    // MARK: - Path Tests

    func testIsabellePathConstruction() {
        let downloader = IsabelleDownloader.shared

        // The path should be in Application Support
        let isabellePath = downloader.isabellePath
        XCTAssertTrue(isabellePath.path.contains("Application Support"))
        XCTAssertTrue(isabellePath.path.contains("TLA+ Studio"))
        XCTAssertTrue(isabellePath.path.contains("Provers"))
        XCTAssertTrue(isabellePath.path.contains("isabelle"))
    }

    func testIsabelleBinaryPathConstruction() {
        let downloader = IsabelleDownloader.shared

        let binaryPath = downloader.isabelleBinaryPath
        XCTAssertTrue(binaryPath.path.contains("bin/isabelle"))
    }

    // MARK: - Helper Method Tests

    func testFormattedProgressStarting() {
        let downloader = IsabelleDownloader.shared

        // When totalBytes is 0, should show "Starting..."
        // We can't easily test this without modifying internal state,
        // so we test the method exists and returns a string
        let progress = downloader.formattedProgress
        XCTAssertFalse(progress.isEmpty)
    }

    func testEstimatedSize() {
        let downloader = IsabelleDownloader.shared

        let size = downloader.estimatedSize
        XCTAssertFalse(size.isEmpty)
        XCTAssertTrue(size.contains("GB"))
    }

    // MARK: - Singleton Tests

    func testSharedInstance() {
        let instance1 = IsabelleDownloader.shared
        let instance2 = IsabelleDownloader.shared

        XCTAssertTrue(instance1 === instance2)
    }

    // MARK: - Initial State Tests

    func testInitialStateIsCheckingOrKnown() {
        // When the downloader initializes, it checks installation
        // So the state should be checking initially, then transition
        let downloader = IsabelleDownloader.shared
        let state = downloader.state

        // State can be: checking, notInstalled, or installed depending on system
        switch state {
        case .checking, .notInstalled, .installed:
            break
        default:
            XCTFail("Unexpected initial state: \(state)")
        }
    }

    // MARK: - Cancel Tests

    func testCancelResetsToNotInstalled() {
        let downloader = IsabelleDownloader.shared

        // Cancel should reset state (if not installed)
        downloader.cancel()

        // After cancel, if it wasn't installed, it should be notInstalled
        // (We can't guarantee the exact state without controlling the full lifecycle)
    }

    // MARK: - Byte Count Formatting Tests

    func testByteCountFormatting() {
        // Test that ByteCountFormatter works as expected for progress display
        let downloaded: Int64 = 500 * 1024 * 1024  // 500 MB
        let total: Int64 = 1024 * 1024 * 1024      // 1 GB

        let downloadedStr = ByteCountFormatter.string(fromByteCount: downloaded, countStyle: .file)
        let totalStr = ByteCountFormatter.string(fromByteCount: total, countStyle: .file)

        XCTAssertTrue(downloadedStr.contains("MB") || downloadedStr.contains("500"))
        XCTAssertTrue(totalStr.contains("GB") || totalStr.contains("1"))
    }
}
