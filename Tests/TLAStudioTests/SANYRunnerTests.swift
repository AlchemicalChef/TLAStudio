import XCTest
@testable import TLAStudioApp

/// Integration tests that run the real SANY analyzer. Skipped when java or
/// tla2tools.jar is not available (mirrors PlusCalTranslatorTests' JVM gating).
final class SANYRunnerTests: TempDirectoryTestCase {

    private func skipUnlessToolchainAvailable() throws {
        guard JavaProcessRunner.findJava() != nil,
              JavaProcessRunner.findTLA2Tools() != nil else {
            throw XCTSkip("java or tla2tools.jar not available")
        }
    }

    func testAnalyzeReportsUnknownOperatorAtCorrectRange() async throws {
        try skipUnlessToolchainAvailable()

        let spec = """
        ---- MODULE ProbeSpec ----
        Op == UndefinedThing
        ====
        """
        let specURL = tempDirectory.appendingPathComponent("ProbeSpec.tla")
        try spec.write(to: specURL, atomically: true, encoding: .utf8)

        let result = await SANYRunner.shared.analyze(specFileURL: specURL)

        guard case .success(let stdout, let stderr, let status) = result else {
            return XCTFail("Expected .success, got \(result)")
        }
        XCTAssertNotEqual(status, 0, "SANY should signal the semantic error via -error-codes")

        let diagnostics = SANYOutputParser.parse(
            stdout: stdout, stderr: stderr, moduleName: "ProbeSpec"
        )
        XCTAssertEqual(diagnostics.count, 1)
        let diagnostic = try XCTUnwrap(diagnostics.first)
        XCTAssertEqual(diagnostic.severity, .error)
        XCTAssertTrue(diagnostic.message.contains("UndefinedThing"))
        XCTAssertTrue(diagnostic.isSemantic)
        // `UndefinedThing` sits on line 2 (1-based), cols 7–20 inclusive.
        XCTAssertEqual(diagnostic.range.start, TLAPosition(line: 1, column: 6))
        XCTAssertEqual(diagnostic.range.end, TLAPosition(line: 1, column: 20))
    }

    func testAnalyzeResolvesSiblingModuleViaSearchPath() async throws {
        try skipUnlessToolchainAvailable()

        let libDirectory = tempDirectory.appendingPathComponent("lib", isDirectory: true)
        try FileManager.default.createDirectory(at: libDirectory, withIntermediateDirectories: true)
        try """
        ---- MODULE Helper ----
        HelperOp == 42
        ====
        """.write(to: libDirectory.appendingPathComponent("Helper.tla"), atomically: true, encoding: .utf8)

        let specURL = tempDirectory.appendingPathComponent("UsesHelper.tla")
        try """
        ---- MODULE UsesHelper ----
        EXTENDS Helper
        X == HelperOp
        ====
        """.write(to: specURL, atomically: true, encoding: .utf8)

        // Without the library path the EXTENDS must fail…
        let withoutPath = await SANYRunner.shared.analyze(specFileURL: specURL)
        guard case .success(let stdout1, let stderr1, _) = withoutPath else {
            return XCTFail("Expected .success, got \(withoutPath)")
        }
        let failing = SANYOutputParser.parse(stdout: stdout1, stderr: stderr1, moduleName: "UsesHelper")
        XCTAssertTrue(
            failing.contains { $0.message.contains("Cannot find source file for module Helper") },
            "Expected a missing-module diagnostic, got: \(failing.map(\.message))"
        )

        // …and with it (via -DTLA-Library) the spec must be clean.
        let withPath = await SANYRunner.shared.analyze(
            specFileURL: specURL,
            searchPaths: [libDirectory]
        )
        guard case .success(let stdout2, let stderr2, let status) = withPath else {
            return XCTFail("Expected .success, got \(withPath)")
        }
        XCTAssertEqual(status, 0)
        XCTAssertTrue(
            SANYOutputParser.parse(stdout: stdout2, stderr: stderr2, moduleName: "UsesHelper").isEmpty
        )
    }
}
