import XCTest
@testable import TLAStudioApp

/// Fixtures below are verbatim captures from `java -cp tla2tools.jar tla2sany.SANY`
/// (SANY2 Version 2.2) — see SANYOutputParser's doc comment for the grammar.
final class SANYOutputParserTests: XCTestCase {

    // MARK: - Semantic errors

    func testUnknownOperatorAndArityErrors() {
        let output = """

        ****** SANY2 Version 2.2 created 08 July 2020

        Parsing file /private/tmp/sany-probe/Bad.tla
        Parsing file /private/var/folders/T/tlc-123/Naturals.tla (jar:file:/x/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
        Semantic processing of module Naturals
        Semantic processing of module Bad
        Semantic errors:

        *** Errors: 2

        line 3, col 7 to line 3, col 20 of module Bad

        Unknown operator: `UndefinedThing'.


        line 5, col 11 to line 5, col 13 of module Bad

        The operator Two requires 2 arguments.



        Linting of module Bad
        """

        let diagnostics = SANYOutputParser.parse(stdout: output, moduleName: "Bad")

        XCTAssertEqual(diagnostics.count, 2)

        XCTAssertEqual(diagnostics[0].severity, .error)
        XCTAssertEqual(diagnostics[0].message, "Unknown operator: `UndefinedThing'.")
        XCTAssertEqual(diagnostics[0].code, "SANY")
        XCTAssertTrue(diagnostics[0].isSemantic)
        // SANY is 1-based with inclusive end columns; TLARange is 0-based exclusive.
        XCTAssertEqual(diagnostics[0].range.start, TLAPosition(line: 2, column: 6))
        XCTAssertEqual(diagnostics[0].range.end, TLAPosition(line: 2, column: 20))

        XCTAssertEqual(diagnostics[1].severity, .error)
        XCTAssertEqual(diagnostics[1].message, "The operator Two requires 2 arguments.")
        XCTAssertEqual(diagnostics[1].range.start, TLAPosition(line: 4, column: 10))
        XCTAssertEqual(diagnostics[1].range.end, TLAPosition(line: 4, column: 13))
    }

    // MARK: - Warnings

    func testWarningsSectionAndMultiLineMessage() {
        let output = """
        ****** SANY2 Version 2.2 created 08 July 2020

        Parsing file /private/tmp/sany-probe/Warn.tla
        Semantic processing of module Warn
        Semantic errors:

        *** Errors: 1

        line 4, col 1 to line 4, col 6 of module Warn

        Operator x already defined or declared.


        *** Warnings: 1

        line 4, col 1 to line 4, col 6 of module Warn

        Multiple declarations or definitions for symbol x.
        This duplicates the one at line 3, col 1 to line 3, col 6 of module Warn.



        Linting of module Warn
        """

        let diagnostics = SANYOutputParser.parse(stdout: output, moduleName: "Warn")

        XCTAssertEqual(diagnostics.count, 2)

        XCTAssertEqual(diagnostics[0].severity, .error)
        XCTAssertEqual(diagnostics[0].message, "Operator x already defined or declared.")

        XCTAssertEqual(diagnostics[1].severity, .warning)
        // Message lines are joined; the embedded "at line 3, col 1 …" phrase must
        // NOT be mistaken for a new entry's location line.
        XCTAssertEqual(
            diagnostics[1].message,
            "Multiple declarations or definitions for symbol x. "
                + "This duplicates the one at line 3, col 1 to line 3, col 6 of module Warn."
        )
        XCTAssertEqual(diagnostics[1].range.start, TLAPosition(line: 3, column: 0))
        XCTAssertEqual(diagnostics[1].range.end, TLAPosition(line: 3, column: 6))
    }

    // MARK: - Aborts / missing modules

    func testMissingModuleAbortIsDocumentLevelAndNotDuplicated() {
        // The "Fatal errors…" preamble repeats the same entry that appears inside
        // the *** Errors: section; only one diagnostic must come out.
        let output = """
        ****** SANY2 Version 2.2 created 08 July 2020

        Parsing file /private/tmp/sany-probe/UsesHelper.tla

        Fatal errors while parsing TLA+ spec in file UsesHelper.tla

        Unknown location

        Cannot find source file for module Helper imported in module UsesHelper.
        *** Errors: 1

        Unknown location

        Cannot find source file for module Helper imported in module UsesHelper.


        """

        let diagnostics = SANYOutputParser.parse(stdout: output, moduleName: "UsesHelper")

        XCTAssertEqual(diagnostics.count, 1)
        XCTAssertEqual(diagnostics[0].severity, .error)
        XCTAssertEqual(
            diagnostics[0].message,
            "Cannot find source file for module Helper imported in module UsesHelper."
        )
        XCTAssertEqual(diagnostics[0].range.start, TLAPosition(line: 0, column: 0))
        XCTAssertEqual(diagnostics[0].range.end, TLAPosition(line: 0, column: 0))
    }

    // MARK: - Parse errors

    func testParseErrorBlockYieldsPositionedErrorAndSuppressesDuplicate() {
        let output = """
        ****** SANY2 Version 2.2 created 08 July 2020

        Parsing file /private/tmp/sany-probe/ParseErr.tla
        ***Parse Error***
        Was expecting "Expression or Instance"
        Encountered "==" at line 2, column 7 and token "=="

        Residual stack trace follows:
        Definition starting at line 2, column 1.
        Module body starting at line 2, column 1.
        Module definition starting at line 1, column 1.


        Fatal errors while parsing TLA+ spec in file ParseErr.tla

        In module ParseErr

        Could not parse module ParseErr from file ParseErr.tla
        *** Errors: 1

        In module ParseErr

        Could not parse module ParseErr from file ParseErr.tla


        """

        let diagnostics = SANYOutputParser.parse(stdout: output, moduleName: "ParseErr")

        // The ***Parse Error*** block carries the only precise position; the
        // section's "Could not parse module" entry is a duplicate and is dropped.
        XCTAssertEqual(diagnostics.count, 1)
        XCTAssertEqual(diagnostics[0].severity, .error)
        XCTAssertTrue(diagnostics[0].message.contains("Was expecting \"Expression or Instance\""))
        XCTAssertTrue(diagnostics[0].message.contains("Encountered \"==\" at line 2, column 7"))
        XCTAssertEqual(diagnostics[0].range.start, TLAPosition(line: 1, column: 6))
        XCTAssertEqual(diagnostics[0].range.end, TLAPosition(line: 1, column: 8))
    }

    func testParseErrorInSiblingModuleIsSummarized() {
        // SANY parses EXTENDS'd files too: a parse error whose owning file (from
        // the preceding "Parsing file" line) is NOT the current document must not
        // produce a range in the current document.
        let output = """
        ****** SANY2 Version 2.2 created 08 July 2020

        Parsing file /private/tmp/sany-probe/Main.tla
        Parsing file /private/tmp/sany-probe/Broken.tla
        ***Parse Error***
        Was expecting "Expression or Instance"
        Encountered "==" at line 2, column 7 and token "=="

        Residual stack trace follows:
        Definition starting at line 2, column 1.


        Fatal errors while parsing TLA+ spec in file Main.tla

        In module Broken

        Could not parse module Broken from file Broken.tla
        *** Errors: 1

        In module Broken

        Could not parse module Broken from file Broken.tla


        """

        let diagnostics = SANYOutputParser.parse(stdout: output, moduleName: "Main")

        XCTAssertEqual(diagnostics.count, 1)
        XCTAssertEqual(diagnostics[0].severity, .error)
        XCTAssertTrue(diagnostics[0].message.hasPrefix("In module Broken:"))
        XCTAssertEqual(diagnostics[0].range.start, TLAPosition(line: 0, column: 0))
        XCTAssertEqual(diagnostics[0].range.end, TLAPosition(line: 0, column: 0))
    }

    // MARK: - Cross-module attribution

    func testSemanticErrorInExtendedModuleIsSummarized() {
        let output = """
        *** Errors: 1

        line 2, col 1 to line 2, col 5 of module Helper

        Some semantic error in the sibling.
        """

        let diagnostics = SANYOutputParser.parse(stdout: output, moduleName: "UsesHelper")

        XCTAssertEqual(diagnostics.count, 1)
        XCTAssertEqual(diagnostics[0].message, "In module Helper: Some semantic error in the sibling.")
        XCTAssertEqual(diagnostics[0].range.start, TLAPosition(line: 0, column: 0))
    }

    // MARK: - Clean / degenerate output

    func testCleanRunProducesNoDiagnostics() {
        let output = """
        ****** SANY2 Version 2.2 created 08 July 2020

        Parsing file /private/tmp/sany-probe/UsesHelper.tla
        Parsing file /private/tmp/sany-probe/lib/Helper.tla (file:/tmp/sany-probe/lib/Helper.tla)
        Semantic processing of module Helper
        Semantic processing of module UsesHelper
        Linting of module Helper
        Linting of module UsesHelper
        """

        XCTAssertTrue(SANYOutputParser.parse(stdout: output, moduleName: "UsesHelper").isEmpty)
    }

    func testEmptyOutputProducesNoDiagnostics() {
        XCTAssertTrue(SANYOutputParser.parse(stdout: "", moduleName: "Empty").isEmpty)
    }

    func testStderrIsParsedAsFallback() {
        let stderr = """
        *** Errors: 1

        line 1, col 1 to line 1, col 4 of module M

        Some error on stderr.
        """

        let diagnostics = SANYOutputParser.parse(stdout: "", stderr: stderr, moduleName: "M")
        XCTAssertEqual(diagnostics.count, 1)
        XCTAssertEqual(diagnostics[0].message, "Some error on stderr.")
    }

    func testRepeatedEntriesAcrossSectionsAreDeduplicated() {
        let output = """
        *** Abort messages: 1

        Unknown location

        Same abort message.

        *** Errors: 1

        Unknown location

        Same abort message.
        """

        let diagnostics = SANYOutputParser.parse(stdout: output, moduleName: "M")
        XCTAssertEqual(diagnostics.count, 1)
        XCTAssertEqual(diagnostics[0].severity, .error)
    }

    // MARK: - Discriminator

    func testIsSemanticDiscriminator() {
        let range = TLARange(
            start: TLAPosition(line: 0, column: 0),
            end: TLAPosition(line: 0, column: 0)
        )
        XCTAssertTrue(
            TLADiagnostic(range: range, severity: .error, message: "m", code: "SANY").isSemantic
        )
        XCTAssertFalse(
            TLADiagnostic(range: range, severity: .error, message: "m", code: nil).isSemantic
        )
        XCTAssertFalse(
            TLADiagnostic(range: range, severity: .error, message: "m", code: "TS").isSemantic
        )
    }
}
