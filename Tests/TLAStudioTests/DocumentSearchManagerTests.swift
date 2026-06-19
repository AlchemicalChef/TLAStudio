import XCTest
@testable import TLAStudioApp

@MainActor
final class DocumentSearchManagerTests: XCTestCase {

    func testSearchComputesLineAndColumnFromOffsetTable() async {
        let manager = DocumentSearchManager()
        manager.query = "x"
        // 'x' is the 3rd character of line index 1 (0-based column 2).
        let content = "AAA\nBBxBB\nCC"

        let results = await manager.search(in: content)

        XCTAssertEqual(results.count, 1)
        let match = try? XCTUnwrap(results.first)
        XCTAssertEqual(match?.offset, 6)
        XCTAssertEqual(match?.line, 1)
        XCTAssertEqual(match?.column, 2)
    }

    func testSearchColumnIsGraphemeCountAcrossAstralCharacter() async {
        let manager = DocumentSearchManager()
        manager.query = "ok"
        // 𝟙 (U+1D7D9) is one grapheme but two UTF-16 units. The match "ok" sits at
        // UTF-16 offset 7, yet its grapheme column is 6 ("x = 𝟙 " = 6 characters).
        // Confirms the offset-table path preserves the app's grapheme-column units.
        let content = "x = 𝟙 ok"

        let results = await manager.search(in: content)

        XCTAssertEqual(results.count, 1)
        XCTAssertEqual(results.first?.line, 0)
        XCTAssertEqual(results.first?.column, 6)
    }

    func testEmptyQueryReturnsNoResults() async {
        let manager = DocumentSearchManager()
        manager.query = ""
        let results = await manager.search(in: "anything")
        XCTAssertTrue(results.isEmpty)
    }
}
