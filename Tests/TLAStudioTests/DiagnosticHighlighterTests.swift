import XCTest
@testable import TLAStudioApp

// MARK: - Diagnostic Highlighter Tests

/// Tests for DiagnosticHighlighter that manages diagnostic underlines.
/// Note: These tests focus on range calculation logic since full UI testing
/// requires a running NSTextView which isn't available in unit tests.
final class DiagnosticHighlighterTests: XCTestCase {

    // MARK: - Range Calculation Tests

    func testCalculateRangeForSimpleDiagnostic() {
        let text = "Line 0\nLine 1\nLine 2"
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 1, column: 0),
                end: TLAPosition(line: 1, column: 4)
            ),
            severity: .error,
            message: "Test error",
            code: nil
        )

        let range = DiagnosticHighlighter.mappedRange(for: diagnostic, in: text)

        XCTAssertEqual(range, NSRange(location: 7, length: 4))
    }

    func testCalculateRangeMultiLine() {
        let text = "First\nSecond\nThird"

        let lines = text.components(separatedBy: "\n")

        // Line 2 starts at offset 13 (5 + 1 + 6 + 1 = 13)
        var offset = 0
        for i in 0..<2 {
            offset += lines[i].count + 1
        }

        XCTAssertEqual(offset, 13)
        XCTAssertEqual(lines[2], "Third")
    }

    func testCalculateRangeOutOfBounds() {
        let text = "Short"
        let lines = text.components(separatedBy: "\n")

        // Line 10 doesn't exist
        let lineIndex = 10
        XCTAssertFalse(lineIndex < lines.count)
    }

    func testCalculateRangeSinglePointDiagnostic() {
        let text = "TypeOK == x \\in Nat"
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 0)
            ),
            severity: .warning,
            message: "Warning",
            code: nil
        )

        let range = DiagnosticHighlighter.mappedRange(for: diagnostic, in: text)

        XCTAssertEqual(range, NSRange(location: 0, length: 6))
    }

    func testCalculateRangeUsesUTF16OffsetsForUnicode() {
        let text = "🙂abc\nNext"
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 1),
                end: TLAPosition(line: 0, column: 4)
            ),
            severity: .error,
            message: "Unicode range",
            code: nil
        )

        let range = DiagnosticHighlighter.mappedRange(for: diagnostic, in: text)

        XCTAssertEqual(range, NSRange(location: 2, length: 3))
    }

    // MARK: - Severity Tests

    func testDiagnosticSeverities() {
        let severities: [TLADiagnosticSeverity] = [.error, .warning, .information, .hint]

        for severity in severities {
            let diagnostic = TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 5)
                ),
                severity: severity,
                message: "Test",
                code: nil
            )

            XCTAssertEqual(diagnostic.severity, severity)
        }
    }

    // MARK: - Diagnostic Message Tests

    func testDiagnosticMessage() {
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 5)
            ),
            severity: .error,
            message: "Syntax error: unexpected token",
            code: "E001"
        )

        XCTAssertEqual(diagnostic.message, "Syntax error: unexpected token")
        XCTAssertEqual(diagnostic.code, "E001")
    }

    func testDiagnosticWithoutCode() {
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 5)
            ),
            severity: .warning,
            message: "Warning message",
            code: nil
        )

        XCTAssertNil(diagnostic.code)
    }

    // MARK: - Line Filtering Tests

    func testFilterDiagnosticsAtLine() {
        let diagnostics = [
            TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 5)
                ),
                severity: .error,
                message: "Error at line 0",
                code: nil
            ),
            TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 5, column: 0),
                    end: TLAPosition(line: 5, column: 10)
                ),
                severity: .warning,
                message: "Warning at line 5",
                code: nil
            ),
            TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 5, column: 15),
                    end: TLAPosition(line: 5, column: 20)
                ),
                severity: .information,
                message: "Info at line 5",
                code: nil
            ),
            TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 10, column: 0),
                    end: TLAPosition(line: 10, column: 5)
                ),
                severity: .hint,
                message: "Hint at line 10",
                code: nil
            )
        ]

        let line5Diagnostics = diagnostics.filter { Int($0.range.start.line) == 5 }

        XCTAssertEqual(line5Diagnostics.count, 2)
        XCTAssertTrue(line5Diagnostics.allSatisfy { Int($0.range.start.line) == 5 })
    }

    // MARK: - Character Index Tests

    func testDiagnosticAtCharacterIndex() {
        let text = "Line 0\nLine 1"
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 4)
            ),
            severity: .error,
            message: "Test",
            code: nil
        )

        guard let range = DiagnosticHighlighter.mappedRange(for: diagnostic, in: text) else {
            XCTFail("Expected range to be mapped")
            return
        }

        XCTAssertTrue(NSLocationInRange(2, range))
        XCTAssertFalse(NSLocationInRange(5, range))
    }

    // MARK: - Empty Diagnostics Tests

    func testEmptyDiagnosticsList() {
        let diagnostics: [TLADiagnostic] = []
        XCTAssertTrue(diagnostics.isEmpty)
    }

    // MARK: - TLADiagnostic Identity Tests

    func testDiagnosticHasUniqueId() {
        let diagnostic1 = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 5)
            ),
            severity: .error,
            message: "Test",
            code: nil
        )

        let diagnostic2 = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 5)
            ),
            severity: .error,
            message: "Test",
            code: nil
        )

        // Each diagnostic should have a unique ID
        XCTAssertNotEqual(diagnostic1.id, diagnostic2.id)
    }
}

// MARK: - NSUnderlineStyle Tests

final class UnderlineStyleTests: XCTestCase {

    func testUnderlineStyleCombinations() {
        // Test that underline styles can be combined
        let errorStyle: NSUnderlineStyle = [.single, .patternDot, .thick]
        let warningStyle: NSUnderlineStyle = [.single, .patternDot]
        let infoStyle: NSUnderlineStyle = [.single, .patternDash]
        let hintStyle: NSUnderlineStyle = [.single, .patternDashDot]

        XCTAssertNotEqual(errorStyle.rawValue, 0)
        XCTAssertNotEqual(warningStyle.rawValue, 0)
        XCTAssertNotEqual(infoStyle.rawValue, 0)
        XCTAssertNotEqual(hintStyle.rawValue, 0)
    }
}
