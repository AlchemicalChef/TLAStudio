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
