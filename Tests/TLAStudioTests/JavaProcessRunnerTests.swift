import XCTest
@testable import TLAStudioApp

final class JavaProcessRunnerTests: XCTestCase {

    /// Cancelling the calling Task must terminate the subprocess promptly —
    /// otherwise superseded semantic checks / simulation steps stack live JVMs
    /// (bug-review-2026-06-09b, finding #1).
    func testTaskCancellationTerminatesProcess() async throws {
        let started = Date()
        let task = Task {
            try await JavaProcessRunner.run(
                executableURL: URL(fileURLWithPath: "/bin/sleep"),
                arguments: ["30"],
                timeout: 60
            )
        }

        // Let the process launch, then cancel the task.
        try await Task.sleep(nanoseconds: 300_000_000)
        task.cancel()

        let result = try? await task.value
        let elapsed = Date().timeIntervalSince(started)

        XCTAssertLessThan(elapsed, 5, "cancellation should terminate the subprocess, not wait out the sleep")
        if let result {
            // SIGTERM'd — anything but a clean zero exit.
            XCTAssertNotEqual(result.terminationStatus, 0)
        }
    }

    /// A Task cancelled before the call starts must not launch a process.
    func testPreCancelledTaskDoesNotRun() async {
        let task = Task {
            try await JavaProcessRunner.run(
                executableURL: URL(fileURLWithPath: "/bin/sleep"),
                arguments: ["30"],
                timeout: 60
            )
        }
        task.cancel()

        let started = Date()
        _ = try? await task.value
        XCTAssertLessThan(Date().timeIntervalSince(started), 5)
    }
}
