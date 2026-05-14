import XCTest
@testable import TLAStudioApp

final class TLAPMProcessManagerTests: XCTestCase {

    func testWaitForExitReturnsTerminationStatusForCompletedProcess() async throws {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/true")

        try process.run()

        let exitStatus = try await TLAPMProcessManager.waitForExit(of: process, timeout: 1)
        XCTAssertEqual(exitStatus, 0)
    }

    func testWaitForExitThrowsTimeoutForLongRunningProcess() async throws {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/bin/sleep")
        process.arguments = ["2"]

        try process.run()
        defer {
            if process.isRunning {
                process.terminate()
                process.waitUntilExit()
            }
        }

        do {
            _ = try await TLAPMProcessManager.waitForExit(of: process, timeout: 0.1)
            XCTFail("Expected waitForExit to time out")
        } catch let error as TLAPMError {
            switch error {
            case .timeout:
                break
            default:
                XCTFail("Expected timeout error, got \(error)")
            }
        } catch {
            XCTFail("Expected TLAPMError.timeout, got \(error)")
        }
    }
}

/// Tests for the fingerprint-invalidation logic that triggers when TLAPM reports a
/// "Executable not found" error. The cache on disk would otherwise replay the stale
/// failure with `@!!already:true` indefinitely even after the tool is installed.
final class TLAPMFingerprintInvalidationTests: TempDirectoryTestCase {

    /// Builds `<dir>/.tlacache/<stem>.tlaps/fingerprints` and returns its URL.
    private func stageFingerprints(specName: String, contents: String = "fp data") throws -> (spec: URL, fingerprints: URL) {
        let spec = tempDirectory.appendingPathComponent(specName)
        try "---- MODULE \(spec.deletingPathExtension().lastPathComponent) ----\n====".write(to: spec, atomically: true, encoding: .utf8)

        let stem = spec.deletingPathExtension().lastPathComponent
        let cacheDir = tempDirectory
            .appendingPathComponent(".tlacache")
            .appendingPathComponent("\(stem).tlaps")
        try FileManager.default.createDirectory(at: cacheDir, withIntermediateDirectories: true)
        let fp = cacheDir.appendingPathComponent("fingerprints")
        try contents.write(to: fp, atomically: true, encoding: .utf8)
        return (spec, fp)
    }

    func testClearsFingerprintsWhenObligationFailsWithExecutableNotFound() throws {
        let (spec, fp) = try stageFingerprints(specName: "Demo.tla")

        let obligations = [
            TestFactories.makeProofObligation(
                startLine: 10,
                status: .failed,
                errorMessage: #"Executable "ls4" not found in this PATH:"#,
                fileURL: spec
            )
        ]

        TLAPMProcessManager.invalidateFingerprintsIfEnvironmentFailure(
            specURL: spec,
            obligations: obligations
        )

        XCTAssertFalse(FileManager.default.fileExists(atPath: fp.path),
                       "fingerprints should be removed when a failure reports a missing executable")
    }

    func testKeepsFingerprintsForGenuineProofFailure() throws {
        let (spec, fp) = try stageFingerprints(specName: "Demo.tla")

        let obligations = [
            TestFactories.makeProofObligation(
                startLine: 10,
                status: .failed,
                errorMessage: "SMT backend could not prove the obligation within timeout",
                fileURL: spec
            )
        ]

        TLAPMProcessManager.invalidateFingerprintsIfEnvironmentFailure(
            specURL: spec,
            obligations: obligations
        )

        XCTAssertTrue(FileManager.default.fileExists(atPath: fp.path),
                      "fingerprints must survive genuine proof failures — only tooling errors invalidate the cache")
    }

    func testIgnoresExecutableNotFoundOnSuccessfulObligation() throws {
        // Defensive: status != failed/timeout should not trigger invalidation even if
        // errorMessage happens to contain the pattern (e.g. a warning surfaced separately).
        let (spec, fp) = try stageFingerprints(specName: "Demo.tla")

        let obligations = [
            TestFactories.makeProofObligation(
                startLine: 10,
                status: .proved,
                errorMessage: #"Executable "isabelle" not found"#,
                fileURL: spec
            )
        ]

        TLAPMProcessManager.invalidateFingerprintsIfEnvironmentFailure(
            specURL: spec,
            obligations: obligations
        )

        XCTAssertTrue(FileManager.default.fileExists(atPath: fp.path))
    }

    func testDoesNothingWhenNoCacheExists() throws {
        let spec = tempDirectory.appendingPathComponent("Nocache.tla")
        try "---- MODULE Nocache ----\n====".write(to: spec, atomically: true, encoding: .utf8)

        let obligations = [
            TestFactories.makeProofObligation(
                startLine: 10,
                status: .failed,
                errorMessage: #"Executable "ls4" not found"#,
                fileURL: spec
            )
        ]

        // Should not throw or log errors; absent cache is a no-op.
        TLAPMProcessManager.invalidateFingerprintsIfEnvironmentFailure(
            specURL: spec,
            obligations: obligations
        )
    }

    func testTimeoutStatusAlsoTriggersInvalidation() throws {
        // TLAPM reports timeout when `type ls4` shell check itself times out under load.
        let (spec, fp) = try stageFingerprints(specName: "Demo.tla")

        let obligations = [
            TestFactories.makeProofObligation(
                startLine: 10,
                status: .timeout,
                errorMessage: #"Executable "zenon" not found"#,
                fileURL: spec
            )
        ]

        TLAPMProcessManager.invalidateFingerprintsIfEnvironmentFailure(
            specURL: spec,
            obligations: obligations
        )

        XCTAssertFalse(FileManager.default.fileExists(atPath: fp.path))
    }
}
