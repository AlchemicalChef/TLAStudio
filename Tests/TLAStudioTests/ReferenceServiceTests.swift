import XCTest
@testable import TLAStudioApp

@MainActor
final class ReferenceServiceTests: XCTestCase {

    func testCurrentDocumentReferencesExcludeCommentsAndStrings() async throws {
        let document = TLADocument()
        document.content = """
        ---- MODULE RefM ----
        Foo == 1
        Use == Foo \\* Foo in a comment
        Str == "Foo in a string"
        ====
        """

        let results = await ReferenceService.findReferences(to: "Foo", in: document)

        XCTAssertEqual(results.symbolName, "Foo")
        XCTAssertEqual(results.hits.count, 2, "definition + one reference; comment/string excluded")
        XCTAssertEqual(results.hits[0].role, .definition)
        XCTAssertEqual(results.hits[1].role, .reference)
        XCTAssertFalse(results.searchedExtendedModules)
        XCTAssertFalse(results.truncated)

        // Current-document hits carry a usable selection range.
        let nsRange = try XCTUnwrap(results.hits[1].nsRange)
        XCTAssertEqual((document.content as NSString).substring(with: nsRange), "Foo")
        XCTAssertEqual(results.hits[1].lineText, "Use == Foo \\* Foo in a comment")
    }

    func testCrossModuleReferencesViaIndexedClosure() async throws {
        let directory = FileManager.default.temporaryDirectory
            .appendingPathComponent("refsvc-test-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: directory) }

        try """
        ---- MODULE RefHelperZx ----
        SharedOp == 1
        UseInHelper == SharedOp
        ====
        """.write(to: directory.appendingPathComponent("RefHelperZx.tla"), atomically: true, encoding: .utf8)

        let document = TLADocument()
        document.content = """
        ---- MODULE RefMainZx ----
        EXTENDS RefHelperZx
        UseInMain == SharedOp
        ====
        """

        // Warm the document's cross-module snapshot directly.
        document.crossModuleProvider.scheduleRefresh(
            extendedModules: ["RefHelperZx"],
            specDirectory: directory,
            ownFileURL: nil
        )
        let deadline = Date().addingTimeInterval(5)
        while document.crossModuleProvider.symbols.isEmpty && Date() < deadline {
            try await Task.sleep(nanoseconds: 20_000_000)
        }
        XCTAssertFalse(document.crossModuleProvider.symbols.isEmpty, "index should have warmed")

        let results = await ReferenceService.findReferences(to: "SharedOp", in: document)

        XCTAssertTrue(results.searchedExtendedModules)
        let mainHits = results.hits.filter { $0.fileURL == nil }
        let helperHits = results.hits.filter { $0.fileURL != nil }
        XCTAssertEqual(mainHits.count, 1, "one reference in the main document")
        XCTAssertEqual(helperHits.count, 2, "definition + reference in the helper file")
        XCTAssertTrue(helperHits.contains { $0.role == .definition })
        XCTAssertEqual(helperHits.first?.moduleName, "RefHelperZx")
        XCTAssertNil(helperHits.first?.nsRange, "cross-file hits navigate via tlaRange")
    }

    func testFindAllReferencesPublishesAndEditClears() async throws {
        let document = TLADocument()
        document.content = "---- MODULE PubM ----\nFoo == 1\n===="

        await document.findAllReferences(to: "Foo")
        XCTAssertNotNil(document.referenceResults)
        XCTAssertEqual(document.referenceResults?.hits.count, 1)

        document.content += "\n"
        XCTAssertNil(document.referenceResults, "edits invalidate point-in-time results")
    }
}
