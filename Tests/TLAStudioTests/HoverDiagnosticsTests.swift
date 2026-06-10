import XCTest
@testable import TLAStudioApp

final class HoverDiagnosticsTests: XCTestCase {

    private func diagnostic(
        _ startLine: Int, _ startCol: Int, _ endLine: Int, _ endCol: Int,
        severity: TLADiagnosticSeverity = .error,
        message: String = "msg",
        code: String? = nil
    ) -> TLADiagnostic {
        TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: UInt32(startLine), column: UInt32(startCol)),
                end: TLAPosition(line: UInt32(endLine), column: UInt32(endCol))
            ),
            severity: severity,
            message: message,
            code: code
        )
    }

    func testBatchLookupFindsContainingDiagnostic() {
        let text = "Op == UndefinedThing\nNext == TRUE"
        let diagnostics = [diagnostic(0, 6, 0, 20, message: "Unknown operator")]

        // Offset 10 is inside "UndefinedThing".
        let hits = DiagnosticHighlighter.diagnostics(at: 10, in: diagnostics, text: text)
        XCTAssertEqual(hits.map(\.message), ["Unknown operator"])

        // Offset 2 ("Op") is outside.
        XCTAssertTrue(DiagnosticHighlighter.diagnostics(at: 2, in: diagnostics, text: text).isEmpty)
    }

    func testOverlappingDiagnosticsAllReturned() {
        let text = "abcdef"
        let diagnostics = [
            diagnostic(0, 0, 0, 6, message: "outer"),
            diagnostic(0, 2, 0, 4, message: "inner")
        ]
        let hits = DiagnosticHighlighter.diagnostics(at: 3, in: diagnostics, text: text)
        XCTAssertEqual(Set(hits.map(\.message)), ["outer", "inner"])
    }

    func testMultiLineDiagnosticContainsMiddleLine() {
        let text = "aaa\nbbb\nccc"
        let diagnostics = [diagnostic(0, 0, 2, 3, message: "spans")]
        // Offset 5 is on line 1.
        XCTAssertEqual(
            DiagnosticHighlighter.diagnostics(at: 5, in: diagnostics, text: text).count, 1
        )
    }

    func testEmptyDiagnosticsFastPath() {
        XCTAssertTrue(DiagnosticHighlighter.diagnostics(at: 0, in: [], text: "abc").isEmpty)
    }

    func testDiagnosticsOnlyHoverInfo() {
        let diagnostics = [diagnostic(0, 0, 0, 3, message: "boom", code: "SANY")]
        let info = HoverInfo.diagnosticsOnly(diagnostics)
        XCTAssertTrue(info.title.isEmpty)
        XCTAssertEqual(info.diagnostics.count, 1)
        XCTAssertTrue(info.diagnostics[0].isSemantic)
    }
}
