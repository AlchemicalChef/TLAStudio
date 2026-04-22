import XCTest
@testable import TLAStudioApp

final class PlusCalSourceMappingTests: XCTestCase {

    private let originalContent = """
    ---- MODULE Example ----
    EXTENDS Naturals

    (*--algorithm Example
    variables x = 0;
    begin
      x := x + 1;
    end algorithm; *)

    \\* BEGIN TRANSLATION
    \\* old
    \\* END TRANSLATION

    ====
    """

    private let translatedContent = """
    ---- MODULE Example ----
    EXTENDS Naturals

    (*--algorithm Example
    variables x = 0;
    begin
      x := x + 1;
    end algorithm; *)

    \\* BEGIN TRANSLATION
    x = 0
    /\\ x' = x + 1
    /\\ UNCHANGED <<>>
    \\* END TRANSLATION

    ====
    """

    private let fairAlgorithmContent = """
    ---- MODULE FairExample ----
    EXTENDS Naturals

    (*--fair algorithm FairExample
    variables x = 0;
    begin
      x := x + 1;
    end algorithm; *)

    ====
    """

    private let expandedAlgorithmContent = """
    ---- MODULE Example ----
    EXTENDS Naturals

    (*--algorithm Example
    variables x = 0;
    begin
      x := x + 1;
      x := x + 2;
    end algorithm; *)

    \\* BEGIN TRANSLATION
    x = 0
    /\\ x' = x + 2
    \\* END TRANSLATION

    ====
    """

    func testDetectsAlgorithmAndTranslationRanges() {
        let ranges = PlusCalSourceMapping.ranges(in: originalContent)

        XCTAssertNotNil(ranges)
        XCTAssertEqual((originalContent as NSString).substring(with: ranges!.algorithm).prefix(13), "(*--algorithm")
        XCTAssertNotNil(ranges!.translation)
        XCTAssertTrue((originalContent as NSString).substring(with: ranges!.translation!).contains("BEGIN TRANSLATION"))
    }

    func testDetectsFairAlgorithmWithoutTranslation() throws {
        let ranges = try XCTUnwrap(PlusCalSourceMapping.ranges(in: fairAlgorithmContent))

        XCTAssertEqual((fairAlgorithmContent as NSString).substring(with: ranges.algorithm).prefix(18), "(*--fair algorithm")
        XCTAssertNil(ranges.translation)
    }

    func testRemapsSelectionInsideTranslationBlock() throws {
        let oldTranslation = try XCTUnwrap(PlusCalSourceMapping.range(for: .translation, in: originalContent))
        let newTranslation = try XCTUnwrap(PlusCalSourceMapping.range(for: .translation, in: translatedContent))
        let selection = NSRange(location: oldTranslation.location + 8, length: 0)

        let remapped = try XCTUnwrap(
            PlusCalSourceMapping.remapSelection(selection, from: originalContent, to: translatedContent)
        )

        XCTAssertGreaterThanOrEqual(remapped.location, newTranslation.location)
        XCTAssertLessThanOrEqual(remapped.location, newTranslation.location + newTranslation.length)
    }

    func testSelectionAtAlgorithmEndIsNotRemappedAsInsideAlgorithm() throws {
        let oldAlgorithm = try XCTUnwrap(PlusCalSourceMapping.range(for: .algorithm, in: originalContent))
        let selection = NSRange(location: NSMaxRange(oldAlgorithm), length: 0)

        let remapped = try XCTUnwrap(
            PlusCalSourceMapping.remapSelection(selection, from: originalContent, to: expandedAlgorithmContent)
        )

        XCTAssertEqual(remapped.location, selection.location)
    }

    @MainActor
    func testDocumentNavigatesToAlgorithmAndTranslation() throws {
        let document = TLADocument()
        document.content = originalContent

        XCTAssertTrue(document.goToPlusCalAlgorithm())
        let algorithmRange = try XCTUnwrap(PlusCalSourceMapping.range(for: .algorithm, in: originalContent))
        XCTAssertEqual(document.selectedRange.location, algorithmRange.location)

        XCTAssertTrue(document.goToPlusCalTranslation())
        let translationRange = try XCTUnwrap(PlusCalSourceMapping.range(for: .translation, in: originalContent))
        XCTAssertEqual(document.selectedRange.location, translationRange.location)
    }

    @MainActor
    func testDocumentNavigatesFairAlgorithmWithoutTranslation() {
        let document = TLADocument()
        document.content = fairAlgorithmContent

        XCTAssertTrue(document.goToPlusCalAlgorithm())
        XCTAssertFalse(document.goToPlusCalTranslation())
    }
}
