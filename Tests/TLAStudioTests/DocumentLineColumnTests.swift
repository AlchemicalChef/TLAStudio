import XCTest
@testable import TLAStudioApp

// MARK: - TLADocument Line/Column Calculation Tests

/// Tests for the line and column calculation functions in TLADocument.
/// These tests verify proper bounds checking and edge case handling.
@MainActor
final class DocumentLineColumnTests: XCTestCase {

    // MARK: - lineAndColumn(for:) Tests

    func testLineAndColumnForZeroOffset() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        let (line, column) = doc.lineAndColumn(for: 0)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 0)
    }

    func testLineAndColumnForMiddleOfFirstLine() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        let (line, column) = doc.lineAndColumn(for: 3)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 3)
    }

    func testLineAndColumnForNewlineCharacter() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Offset 5 is the newline character
        let (line, column) = doc.lineAndColumn(for: 5)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 5)
    }

    func testLineAndColumnForSecondLine() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Offset 6 is 'W' in "World"
        let (line, column) = doc.lineAndColumn(for: 6)

        XCTAssertEqual(line, 1)
        XCTAssertEqual(column, 0)
    }

    func testLineAndColumnForMiddleOfSecondLine() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Offset 8 is 'r' in "World"
        let (line, column) = doc.lineAndColumn(for: 8)

        XCTAssertEqual(line, 1)
        XCTAssertEqual(column, 2)
    }

    func testLineAndColumnForEndOfContent() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Offset 11 is end of content
        let (line, column) = doc.lineAndColumn(for: 11)

        XCTAssertEqual(line, 1)
        XCTAssertEqual(column, 5)
    }

    func testLineAndColumnForNegativeOffset() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Negative offset should be clamped to 0
        let (line, column) = doc.lineAndColumn(for: -5)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 0)
    }

    func testLineAndColumnForOffsetBeyondContent() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Offset 100 is way beyond content (length is 11)
        let (line, column) = doc.lineAndColumn(for: 100)

        XCTAssertEqual(line, 1)
        XCTAssertEqual(column, 5) // Clamped to end of content
    }

    func testLineAndColumnForEmptyContent() {
        let doc = TLADocument()
        doc.content = ""

        let (line, column) = doc.lineAndColumn(for: 0)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 0)
    }

    func testLineAndColumnForEmptyContentWithOffset() {
        let doc = TLADocument()
        doc.content = ""

        // Any offset on empty content should return (0, 0)
        let (line, column) = doc.lineAndColumn(for: 10)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 0)
    }

    func testLineAndColumnForMultipleLines() {
        let doc = TLADocument()
        doc.content = "Line1\nLine2\nLine3\nLine4"

        // Test various positions
        let tests: [(offset: Int, expectedLine: Int, expectedColumn: Int)] = [
            (0, 0, 0),   // Start of Line1
            (5, 0, 5),   // Newline after Line1
            (6, 1, 0),   // Start of Line2
            (11, 1, 5),  // Newline after Line2
            (12, 2, 0),  // Start of Line3
            (18, 3, 0),  // Start of Line4
            (23, 3, 5),  // End of Line4
        ]

        for test in tests {
            let (line, column) = doc.lineAndColumn(for: test.offset)
            XCTAssertEqual(line, test.expectedLine, "Offset \(test.offset): expected line \(test.expectedLine), got \(line)")
            XCTAssertEqual(column, test.expectedColumn, "Offset \(test.offset): expected column \(test.expectedColumn), got \(column)")
        }
    }

    // MARK: - offset(forLine:column:) Tests

    func testOffsetForLineZeroColumnZero() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        let offset = doc.offset(forLine: 0, column: 0)

        XCTAssertEqual(offset, 0)
    }

    func testOffsetForLineZeroWithColumn() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        let offset = doc.offset(forLine: 0, column: 3)

        XCTAssertEqual(offset, 3)
    }

    func testOffsetForSecondLine() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        let offset = doc.offset(forLine: 1, column: 0)

        XCTAssertEqual(offset, 6)
    }

    func testOffsetForSecondLineWithColumn() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        let offset = doc.offset(forLine: 1, column: 3)

        XCTAssertEqual(offset, 9)
    }

    func testOffsetForNegativeLine() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Negative line should be clamped to 0
        let offset = doc.offset(forLine: -1, column: 0)

        XCTAssertEqual(offset, 0)
    }

    func testOffsetForNegativeColumn() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Negative column should be clamped to 0
        let offset = doc.offset(forLine: 0, column: -5)

        XCTAssertEqual(offset, 0)
    }

    func testOffsetForLineBeyondContent() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Line 100 is way beyond content
        let offset = doc.offset(forLine: 100, column: 0)

        XCTAssertEqual(offset, 11) // End of content
    }

    func testOffsetForColumnBeyondLineLength() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld"

        // Column 100 is beyond "Hello" (length 5)
        let offset = doc.offset(forLine: 0, column: 100)

        XCTAssertEqual(offset, 5) // End of first line (before newline)
    }

    func testOffsetForEmptyContent() {
        let doc = TLADocument()
        doc.content = ""

        let offset = doc.offset(forLine: 0, column: 0)

        XCTAssertEqual(offset, 0)
    }

    func testOffsetForEmptyContentWithInvalidValues() {
        let doc = TLADocument()
        doc.content = ""

        let offset = doc.offset(forLine: 5, column: 10)

        XCTAssertEqual(offset, 0) // Clamped to content length
    }

    // MARK: - Round-trip Tests

    func testRoundTripLineAndColumnToOffset() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld\nTest"

        // Test multiple offsets
        for originalOffset in [0, 3, 5, 6, 10, 12, 15] {
            let (line, column) = doc.lineAndColumn(for: originalOffset)
            let recoveredOffset = doc.offset(forLine: line, column: column)
            XCTAssertEqual(recoveredOffset, originalOffset, "Round-trip failed for offset \(originalOffset)")
        }
    }

    func testRoundTripOffsetToLineAndColumn() {
        let doc = TLADocument()
        doc.content = "Hello\nWorld\nTest"

        // Test multiple line/column pairs
        let tests: [(line: Int, column: Int)] = [
            (0, 0), (0, 3), (0, 5),
            (1, 0), (1, 3), (1, 5),
            (2, 0), (2, 4),
        ]

        for test in tests {
            let offset = doc.offset(forLine: test.line, column: test.column)
            let (recoveredLine, recoveredColumn) = doc.lineAndColumn(for: offset)
            XCTAssertEqual(recoveredLine, test.line, "Round-trip failed for line \(test.line)")
            XCTAssertEqual(recoveredColumn, test.column, "Round-trip failed for column \(test.column)")
        }
    }

    // MARK: - Unicode Content Tests

    func testLineAndColumnWithUnicode() {
        let doc = TLADocument()
        // TLA+ often uses Unicode operators like ∧ (conjunction)
        doc.content = "A ∧ B\nC ∨ D"

        // After "A " (2 chars), we have ∧ which is 1 Swift Character but 3 UTF-8 bytes
        // Swift String counts characters, not bytes
        let (line, column) = doc.lineAndColumn(for: 2)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 2)
    }

    func testOffsetWithUnicodeContent() {
        let doc = TLADocument()
        doc.content = "A ∧ B\nC ∨ D"

        let offset = doc.offset(forLine: 1, column: 2)

        XCTAssertEqual(offset, 8) // "A ∧ B\n" = 6 chars, then "C " = 2 more
    }

    func testLineAndColumnWithEmojiUsesLogicalCharacterColumns() {
        let doc = TLADocument()
        doc.content = "🙂A\nB"

        // The editor selection offset after 🙂 is 2 UTF-16 code units.
        let (line, column) = doc.lineAndColumn(for: 2)

        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 1)
    }

    func testOffsetWithEmojiReturnsUTF16EditorOffset() {
        let doc = TLADocument()
        doc.content = "🙂A\nB"

        let offsetAfterEmoji = doc.offset(forLine: 0, column: 1)
        let offsetAfterEmojiAndA = doc.offset(forLine: 0, column: 2)

        XCTAssertEqual(offsetAfterEmoji, 2)
        XCTAssertEqual(offsetAfterEmojiAndA, 3)
    }

    // MARK: - Edge Case Tests

    func testLineWithOnlyNewline() {
        let doc = TLADocument()
        doc.content = "A\n\nB"

        // Line 1 is empty (just between newlines)
        let (line, column) = doc.lineAndColumn(for: 2)

        XCTAssertEqual(line, 1)
        XCTAssertEqual(column, 0)
    }

    func testTrailingNewline() {
        let doc = TLADocument()
        doc.content = "Hello\n"

        // Offset 6 is after the newline (empty line 1)
        let (line, column) = doc.lineAndColumn(for: 6)

        XCTAssertEqual(line, 1)
        XCTAssertEqual(column, 0)
    }

    func testLargeDocument() {
        let doc = TLADocument()
        // Create a document with 1000 lines
        doc.content = (0..<1000).map { "Line \($0)" }.joined(separator: "\n")

        // Test finding line 500
        let offsetForLine500 = doc.offset(forLine: 500, column: 0)
        let (line, _) = doc.lineAndColumn(for: offsetForLine500)

        XCTAssertEqual(line, 500)
    }

    // MARK: - Stress Tests

    func testVeryLargeDocument() {
        let doc = TLADocument()
        // Create a document with 10000 lines
        doc.content = (0..<10000).map { "This is line number \($0) with some content" }.joined(separator: "\n")

        // Test first line
        let (firstLine, firstCol) = doc.lineAndColumn(for: 0)
        XCTAssertEqual(firstLine, 0)
        XCTAssertEqual(firstCol, 0)

        // Test last line
        let lastOffset = doc.content.count - 1
        let (lastLine, _) = doc.lineAndColumn(for: lastOffset)
        XCTAssertEqual(lastLine, 9999)

        // Test middle line
        let midOffset = doc.offset(forLine: 5000, column: 10)
        let (midLine, midCol) = doc.lineAndColumn(for: midOffset)
        XCTAssertEqual(midLine, 5000)
        XCTAssertEqual(midCol, 10)
    }

    func testRepeatedLineIndexRebuilds() {
        let doc = TLADocument()
        doc.content = "Line1\nLine2\nLine3"

        // First access builds the index
        let (line1, _) = doc.lineAndColumn(for: 0)
        XCTAssertEqual(line1, 0)

        // Change content - should invalidate index
        doc.content = "NewLine1\nNewLine2"

        // Access should rebuild index
        let (line2, _) = doc.lineAndColumn(for: 9)
        XCTAssertEqual(line2, 1)
    }

    func testRapidContentChanges() {
        let doc = TLADocument()

        // Rapidly change content and query
        for i in 0..<100 {
            doc.content = (0..<i+1).map { "Line \($0)" }.joined(separator: "\n")
            let (line, _) = doc.lineAndColumn(for: min(i * 5, doc.content.count))
            XCTAssertGreaterThanOrEqual(line, 0)
        }
    }

    // MARK: - Boundary Tests

    func testExactlyAtNewline() {
        let doc = TLADocument()
        doc.content = "AB\nCD\nEF"

        // Position exactly at first newline (offset 2)
        let (line1, col1) = doc.lineAndColumn(for: 2)
        XCTAssertEqual(line1, 0)
        XCTAssertEqual(col1, 2)

        // Position exactly at second newline (offset 5)
        let (line2, col2) = doc.lineAndColumn(for: 5)
        XCTAssertEqual(line2, 1)
        XCTAssertEqual(col2, 2)
    }

    func testImmediatelyAfterNewline() {
        let doc = TLADocument()
        doc.content = "AB\nCD\nEF"

        // Position immediately after first newline (offset 3)
        let (line1, col1) = doc.lineAndColumn(for: 3)
        XCTAssertEqual(line1, 1)
        XCTAssertEqual(col1, 0)

        // Position immediately after second newline (offset 6)
        let (line2, col2) = doc.lineAndColumn(for: 6)
        XCTAssertEqual(line2, 2)
        XCTAssertEqual(col2, 0)
    }

    func testConsecutiveNewlines() {
        let doc = TLADocument()
        doc.content = "A\n\n\nB"

        // Line 0: "A" (offset 0)
        // Line 1: "" (offset 2)
        // Line 2: "" (offset 3)
        // Line 3: "B" (offset 4)

        let tests: [(offset: Int, line: Int, column: Int)] = [
            (0, 0, 0),  // 'A'
            (1, 0, 1),  // first newline
            (2, 1, 0),  // second newline (empty line 1)
            (3, 2, 0),  // third newline (empty line 2)
            (4, 3, 0),  // 'B'
        ]

        for test in tests {
            let (line, column) = doc.lineAndColumn(for: test.offset)
            XCTAssertEqual(line, test.line, "Offset \(test.offset)")
            XCTAssertEqual(column, test.column, "Offset \(test.offset)")
        }
    }

    func testOnlyNewlines() {
        let doc = TLADocument()
        doc.content = "\n\n\n"

        // 4 lines (3 newlines = 4 lines)
        let (line0, _) = doc.lineAndColumn(for: 0)
        let (line1, _) = doc.lineAndColumn(for: 1)
        let (line2, _) = doc.lineAndColumn(for: 2)
        let (line3, _) = doc.lineAndColumn(for: 3)

        XCTAssertEqual(line0, 0)
        XCTAssertEqual(line1, 1)
        XCTAssertEqual(line2, 2)
        XCTAssertEqual(line3, 3)
    }

    func testSingleCharacter() {
        let doc = TLADocument()
        doc.content = "X"

        let (line, column) = doc.lineAndColumn(for: 0)
        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 0)

        // Beyond the single character
        let (line2, column2) = doc.lineAndColumn(for: 1)
        XCTAssertEqual(line2, 0)
        XCTAssertEqual(column2, 1)
    }

    func testSingleNewline() {
        let doc = TLADocument()
        doc.content = "\n"

        let (line0, col0) = doc.lineAndColumn(for: 0)
        XCTAssertEqual(line0, 0)
        XCTAssertEqual(col0, 0)

        let (line1, col1) = doc.lineAndColumn(for: 1)
        XCTAssertEqual(line1, 1)
        XCTAssertEqual(col1, 0)
    }

    // MARK: - TLA+ Specific Tests

    func testTLAModuleHeader() {
        let doc = TLADocument()
        doc.content = "---- MODULE Test ----\nEXTENDS Naturals\n\nVARIABLES x, y"

        // Find "EXTENDS" (line 1, column 0)
        let extendsOffset = doc.offset(forLine: 1, column: 0)
        XCTAssertTrue(doc.content.dropFirst(extendsOffset).hasPrefix("EXTENDS"))

        // Find "VARIABLES" (line 3, column 0)
        let variablesOffset = doc.offset(forLine: 3, column: 0)
        XCTAssertTrue(doc.content.dropFirst(variablesOffset).hasPrefix("VARIABLES"))
    }

    func testTLAProofStructure() {
        let doc = TLADocument()
        doc.content = """
        THEOREM Thm == TRUE
        PROOF
          <1>1. TRUE
            OBVIOUS
          <1>2. QED
            BY <1>1
        """

        // Verify we can find specific proof steps
        let (theoremLine, _) = doc.lineAndColumn(for: 0)
        XCTAssertEqual(theoremLine, 0)

        let proofOffset = doc.content.range(of: "PROOF")!.lowerBound
        let (proofLine, _) = doc.lineAndColumn(for: doc.content.distance(from: doc.content.startIndex, to: proofOffset))
        XCTAssertEqual(proofLine, 1)
    }

    func testTLAOperatorsWithUnicode() {
        let doc = TLADocument()
        // TLA+ uses various Unicode operators
        doc.content = "A ∧ B ∨ C\n∀x ∈ S: P(x)\n∃y ∈ T: Q(y)"

        // Each Unicode symbol is 1 character in Swift
        let (line1, col1) = doc.lineAndColumn(for: 2)  // Position of ∧
        XCTAssertEqual(line1, 0)
        XCTAssertEqual(col1, 2)

        // Find ∀ on line 1
        let forallOffset = doc.content.range(of: "∀")!.lowerBound
        let (forallLine, forallCol) = doc.lineAndColumn(for: doc.content.distance(from: doc.content.startIndex, to: forallOffset))
        XCTAssertEqual(forallLine, 1)
        XCTAssertEqual(forallCol, 0)
    }

    // MARK: - Integer Overflow Protection Tests

    func testMaxIntOffset() {
        let doc = TLADocument()
        doc.content = "Hello"

        // Very large offset should be clamped
        let (line, column) = doc.lineAndColumn(for: Int.max)
        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 5)  // Clamped to end of content
    }

    func testMinIntOffset() {
        let doc = TLADocument()
        doc.content = "Hello"

        // Very negative offset should be clamped to 0
        let (line, column) = doc.lineAndColumn(for: Int.min)
        XCTAssertEqual(line, 0)
        XCTAssertEqual(column, 0)
    }

    func testMaxIntLine() {
        let doc = TLADocument()
        doc.content = "Line1\nLine2"

        // Very large line number should return end of content
        let offset = doc.offset(forLine: Int.max, column: 0)
        XCTAssertEqual(offset, doc.content.count)
    }

    func testMinIntLine() {
        let doc = TLADocument()
        doc.content = "Line1\nLine2"

        // Very negative line should be clamped to 0
        let offset = doc.offset(forLine: Int.min, column: 0)
        XCTAssertEqual(offset, 0)
    }

    // MARK: - Performance Tests

    func testLineColumnPerformanceSmallDocument() {
        let doc = TLADocument()
        doc.content = (0..<100).map { "Line \($0)" }.joined(separator: "\n")
        let contentLength = doc.content.utf16.count
        let offsets = (0..<1000).map { ($0 * 37) % max(1, contentLength) }

        measure {
            for offset in offsets {
                _ = doc.lineAndColumn(for: offset)
            }
        }
    }

    func testLineColumnPerformanceLargeDocument() {
        let doc = TLADocument()
        doc.content = (0..<10000).map { "This is line \($0) with content" }.joined(separator: "\n")
        let contentLength = doc.content.utf16.count
        let offsets = (0..<1000).map { ($0 * 7919) % max(1, contentLength) }

        measure {
            for offset in offsets {
                _ = doc.lineAndColumn(for: offset)
            }
        }
    }

    func testOffsetForLinePerformance() {
        let doc = TLADocument()
        doc.content = (0..<10000).map { "Line \($0)" }.joined(separator: "\n")
        let queries = (0..<1000).map { iteration in
            (
                line: (iteration * 97) % 10_000,
                column: (iteration * 13) % 10
            )
        }

        measure {
            for query in queries {
                _ = doc.offset(forLine: query.line, column: query.column)
            }
        }
    }
}
