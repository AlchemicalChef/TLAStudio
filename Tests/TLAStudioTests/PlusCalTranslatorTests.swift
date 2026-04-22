import XCTest
@testable import TLAStudioApp

final class PlusCalTranslatorTests: TempDirectoryTestCase {

    func testRunProcessCapturesLargeStdoutAndStderrConcurrently() async throws {
        let scriptURL = tempDirectory.appendingPathComponent("emit-large-output")
        let script = """
        #!/bin/zsh
        /usr/bin/python3 -c 'import sys; sys.stdout.write("o"*70000); sys.stderr.write("e"*70000)'
        """
        try script.write(to: scriptURL, atomically: true, encoding: .utf8)
        try FileManager.default.setAttributes([.posixPermissions: 0o755], ofItemAtPath: scriptURL.path)

        let result = try await PlusCalTranslator.runProcess(
            executableURL: scriptURL,
            arguments: [],
            currentDirectoryURL: tempDirectory,
            timeout: 5
        )

        XCTAssertEqual(result.terminationStatus, 0)
        XCTAssertEqual(result.stdout.count, 70_000)
        XCTAssertEqual(result.stderr.count, 70_000)
    }
}
