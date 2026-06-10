import XCTest
@testable import TLAStudioApp

final class TreeSitterRangeConverterTests: XCTestCase {

    private func range(_ startLine: Int, _ startCol: Int, _ endLine: Int, _ endCol: Int) -> TLARange {
        TLARange(
            start: TLAPosition(line: UInt32(startLine), column: UInt32(startCol)),
            end: TLAPosition(line: UInt32(endLine), column: UInt32(endCol))
        )
    }

    func testASCIIMultiLine() {
        let text = "abc\ndef\nghi"
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: text)
        XCTAssertEqual(converter.utf16Range(for: range(0, 0, 0, 3)), NSRange(location: 0, length: 3))
        XCTAssertEqual(converter.utf16Range(for: range(1, 0, 1, 3)), NSRange(location: 4, length: 3))
        XCTAssertEqual(converter.utf16Range(for: range(2, 1, 2, 2)), NSRange(location: 9, length: 1))
    }

    func testTwoByteUTF8CharacterIsOneUTF16Unit() {
        // "é" = 2 UTF-8 bytes, 1 UTF-16 unit.
        let text = "éab"
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: text)
        // 'a' starts at byte 2, UTF-16 offset 1.
        XCTAssertEqual(converter.utf16Range(for: range(0, 2, 0, 3)), NSRange(location: 1, length: 1))
    }

    func testEmojiIsSurrogatePair() {
        // "😀" = 4 UTF-8 bytes, 2 UTF-16 units.
        let text = "x😀y\nz"
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: text)
        // 'y' starts at byte 5 (1 + 4), UTF-16 offset 3 (1 + 2).
        XCTAssertEqual(converter.utf16Range(for: range(0, 5, 0, 6)), NSRange(location: 3, length: 1))
        // line 1 starts after "x😀y\n" = 5 UTF-16 units.
        XCTAssertEqual(converter.utf16Range(for: range(1, 0, 1, 1)), NSRange(location: 5, length: 1))
    }

    func testCRLFLineEndings() {
        // \r and \n are each one UTF-16 unit; line 1 starts after both.
        let text = "ab\r\ncd"
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: text)
        XCTAssertEqual(converter.utf16Range(for: range(1, 0, 1, 2)), NSRange(location: 4, length: 2))
    }

    func testOutOfBoundsLineReturnsNil() {
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: "ab")
        XCTAssertNil(converter.utf16Range(for: range(3, 0, 3, 1)))
    }

    func testInvertedRangeReturnsNil() {
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: "abcdef")
        XCTAssertNil(converter.utf16Range(for: range(0, 4, 0, 2)))
    }

    func testZeroLengthRangeIsValid() {
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: "abc")
        XCTAssertEqual(converter.utf16Range(for: range(0, 1, 0, 1)), NSRange(location: 1, length: 0))
    }

    func testByteColumnPastLineEndClampsToLineEnd() {
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: "ab\ncd")
        XCTAssertEqual(converter.utf16Offset(line: 0, byteColumn: 99), 2)
    }

    func testEmptyText() {
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: "")
        XCTAssertEqual(converter.utf16Range(for: range(0, 0, 0, 0)), NSRange(location: 0, length: 0))
        XCTAssertNil(converter.utf16Range(for: range(1, 0, 1, 0)))
    }

    func testOneShotConvenience() {
        XCTAssertEqual(
            TextCoordinateMapper.utf16Range(forTreeSitterRange: range(0, 0, 0, 2), in: "hello"),
            NSRange(location: 0, length: 2)
        )
    }
}
