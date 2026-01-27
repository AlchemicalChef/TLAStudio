import XCTest
@testable import TLAStudioApp

final class TLAStudioTests: XCTestCase {

    func testDocumentCreation() throws {
        // Test that a new document can be created
        let document = TLADocument()
        XCTAssertFalse(document.content.isEmpty, "New document should have template content")
        XCTAssertTrue(document.content.contains("MODULE"), "Template should contain MODULE keyword")
    }

    func testLineEndingDetection() throws {
        let document = TLADocument()

        // Test LF detection (default)
        XCTAssertEqual(document.lineEnding, .lf, "Default line ending should be LF")
    }

    func testEncodingDefault() throws {
        let document = TLADocument()
        XCTAssertEqual(document.encoding, .utf8, "Default encoding should be UTF-8")
    }
}
