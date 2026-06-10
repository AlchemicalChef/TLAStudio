import AppKit
import XCTest
@testable import TLAStudioApp

// MARK: - Validator

final class TLAIdentifierValidatorTests: XCTestCase {

    private func validate(_ name: String, original: String = "Old") -> TLAIdentifierValidator.ValidationError? {
        TLAIdentifierValidator.validate(name, original: original)
    }

    func testValidation() {
        XCTAssertEqual(validate(""), .empty)
        XCTAssertEqual(validate("Old"), .unchanged)
        XCTAssertEqual(validate("foo-bar"), .invalidCharacters)
        XCTAssertEqual(validate("foo bar"), .invalidCharacters)
        XCTAssertEqual(validate("123"), .noLetter)
        XCTAssertEqual(validate("_1"), .noLetter)
        XCTAssertEqual(validate("WF_clock"), .fairnessPrefix)
        XCTAssertEqual(validate("SF_x"), .fairnessPrefix)
        XCTAssertEqual(validate("CHOOSE"), .reservedWord)
        XCTAssertEqual(validate("PICK"), .reservedWord, "proof keywords are reserved too")
        XCTAssertEqual(validate("SUFFICES"), .reservedWord)
        XCTAssertNil(validate("goodName_2"))
        XCTAssertNil(validate("x"))
    }
}

// MARK: - Rename Service

@MainActor
final class RenameServiceTests: XCTestCase {

    private func makeDocument(_ content: String) -> TLADocument {
        let document = TLADocument()
        document.content = content
        return document
    }

    func testPrepareCollectsOccurrencesExcludingCommentsAndStrings() async throws {
        let document = makeDocument("""
        ---- MODULE RnM ----
        Foo == 1
        Use == Foo \\* Foo in comment
        Str == "Foo"
        ====
        """)

        let preparedPlan = await RenameService.prepare(name: "Foo", document: document)
        let plan = try XCTUnwrap(preparedPlan)
        XCTAssertEqual(plan.occurrences.count, 2)
        XCTAssertNil(plan.externalDefinition)
    }

    func testHeadlessApplyReplacesAllOccurrences() async throws {
        let document = makeDocument("""
        ---- MODULE RnM ----
        Foo == 1
        Use == Foo \\* Foo in comment
        Str == "Foo"
        ====
        """)

        let preparedPlan = await RenameService.prepare(name: "Foo", document: document)
        let plan = try XCTUnwrap(preparedPlan)
        let applied = RenameService.apply(plan, newName: "Bar", document: document, textView: nil)

        XCTAssertEqual(applied, 2)
        XCTAssertTrue(document.content.contains("Bar == 1"))
        XCTAssertTrue(document.content.contains("Use == Bar"))
        XCTAssertTrue(document.content.contains("\\* Foo in comment"), "comments untouched")
        XCTAssertTrue(document.content.contains("\"Foo\""), "strings untouched")
    }

    func testApplyAbortsOnStaleBuffer() async throws {
        let document = makeDocument("---- MODULE RnM ----\nFoo == 1\n====")
        let preparedPlan = await RenameService.prepare(name: "Foo", document: document)
        let plan = try XCTUnwrap(preparedPlan)

        document.content += "\n\\* edited"
        let applied = RenameService.apply(plan, newName: "Bar", document: document, textView: nil)

        XCTAssertEqual(applied, 0)
        XCTAssertTrue(document.content.contains("Foo == 1"))
    }

    func testApplyRejectsInvalidNewName() async throws {
        let document = makeDocument("---- MODULE RnM ----\nFoo == 1\n====")
        let preparedPlan = await RenameService.prepare(name: "Foo", document: document)
        let plan = try XCTUnwrap(preparedPlan)

        XCTAssertEqual(RenameService.apply(plan, newName: "CHOOSE", document: document, textView: nil), 0)
        XCTAssertEqual(RenameService.apply(plan, newName: "WF_x", document: document, textView: nil), 0)
    }

    func testCollisionAndBuiltinDetection() {
        let symbol = TLASymbol(
            name: "Existing", kind: .operator,
            range: TLARange(start: TLAPosition(line: 0, column: 0), end: TLAPosition(line: 0, column: 8)),
            selectionRange: nil, children: [], parameters: []
        )
        XCTAssertNotNil(RenameService.collision(newName: "Existing", in: [symbol]))
        XCTAssertNil(RenameService.collision(newName: "Fresh", in: [symbol]))
        XCTAssertTrue(RenameService.shadowsBuiltin("Len"))
        XCTAssertFalse(RenameService.shadowsBuiltin("MyVeryOwnOp"))
    }

    func testTextViewApplyIsSingleUndoGroup() async throws {
        final class UndoHost: NSObject, NSTextViewDelegate {
            let manager = UndoManager()
            func undoManager(for view: NSTextView) -> UndoManager? { manager }
        }

        let content = "---- MODULE RnM ----\nFoo == 1\nUse == Foo + Foo\n===="
        let document = makeDocument(content)
        let preparedPlan = await RenameService.prepare(name: "Foo", document: document)
        let plan = try XCTUnwrap(preparedPlan)

        let textView = NSTextView()
        let host = UndoHost()
        textView.allowsUndo = true
        textView.delegate = host
        textView.string = content

        let applied = RenameService.apply(plan, newName: "Bar", document: document, textView: textView)
        XCTAssertEqual(applied, 3)
        XCTAssertTrue(textView.string.contains("Bar == 1"))
        XCTAssertTrue(textView.string.contains("Use == Bar + Bar"))

        // ONE undo restores everything.
        host.manager.undo()
        XCTAssertEqual(textView.string, content)
    }
}
