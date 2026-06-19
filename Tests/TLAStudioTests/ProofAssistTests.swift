import XCTest
@testable import TLAStudioApp

final class ProofAssistTests: XCTestCase {

    // MARK: - Helpers

    private func obligation(
        startLine: Int,
        endLine: Int? = nil,
        goal: String,
        status: ProofStatus = .failed
    ) -> ProofObligation {
        ProofObligation(
            fingerprint: "fp-test",
            location: ProofSourceLocation(
                fileURL: URL(fileURLWithPath: "/tmp/Spec.tla"),
                startLine: startLine,
                startColumn: 1,
                endLine: endLine ?? startLine,
                endColumn: 10
            ),
            kind: .step,
            status: status,
            obligationText: goal
        )
    }

    private func symbol(_ name: String, kind: TLASymbolKind = .operator, parameters: [String] = []) -> TLASymbol {
        TLASymbol(
            name: name, kind: kind,
            range: TLARange(start: TLAPosition(line: 0, column: 0), end: TLAPosition(line: 0, column: 1)),
            selectionRange: nil, children: [], parameters: parameters
        )
    }

    // MARK: - BY DEF suggestions

    func testSuggestsReferencedDefinitionsInGoalOrder() {
        let failing = obligation(startLine: 5, goal: "TypeOK /\\ Inv => Safety")
        let symbols = [symbol("Safety"), symbol("Inv"), symbol("TypeOK"), symbol("Unrelated")]

        let suggestions = ProofAssist.byDefSuggestions(
            for: failing,
            content: "line1\nline2\nline3\nline4\nstep line\n",
            symbols: symbols
        )
        XCTAssertEqual(suggestions, ["TypeOK", "Inv", "Safety"])
    }

    func testExcludesAlreadyExpandedAndNonDefinitions() {
        let content = """
        ---- MODULE M ----
        VARIABLE x
        Inv == x = 0
        THEOREM Inv => TypeOK
        <1>1. QED
          BY DEF Inv
        ====
        """
        let failing = obligation(startLine: 5, endLine: 6, goal: "Inv => TypeOK /\\ x = 0")
        let symbols = [symbol("Inv"), symbol("TypeOK"), symbol("x", kind: .variable)]

        let suggestions = ProofAssist.byDefSuggestions(for: failing, content: content, symbols: symbols)
        XCTAssertEqual(suggestions, ["TypeOK"], "Inv already expanded; x is a variable, not a definition")
    }

    func testIncludesCrossModuleDefinitions() {
        let failing = obligation(startLine: 1, goal: "HelperOp(1) = 2")
        let crossModule = [ModuleSymbol(
            symbol: symbol("HelperOp", parameters: ["a"]),
            moduleName: "Helper",
            fileURL: URL(fileURLWithPath: "/tmp/Helper.tla"),
            depth: 1
        )]
        let suggestions = ProofAssist.byDefSuggestions(
            for: failing, content: "x\n", symbols: [], crossModuleSymbols: crossModule
        )
        XCTAssertEqual(suggestions, ["HelperOp"])
    }

    // MARK: - BY DEF insertion planning

    func testInsertionReplacesObvious() throws {
        let content = """
        THEOREM Inv => TypeOK
        <1>1. Inv => TypeOK
          OBVIOUS
        """
        let failing = obligation(startLine: 2, goal: "Inv => TypeOK")
        let plan = try XCTUnwrap(ProofAssist.planByDefInsertion(names: ["Inv", "TypeOK"], for: failing, content: content))
        XCTAssertEqual(plan.lineIndex, 2)
        XCTAssertEqual(plan.updatedLine, "  BY DEF Inv, TypeOK")
    }

    func testInsertionAppendsDefToBareBy() throws {
        let content = "<1>1. Inv\n  BY Z3\n"
        let failing = obligation(startLine: 1, goal: "Inv")
        let plan = try XCTUnwrap(ProofAssist.planByDefInsertion(names: ["Inv"], for: failing, content: content))
        XCTAssertEqual(plan.updatedLine, "  BY Z3 DEF Inv")
    }

    func testInsertionExtendsExistingDefList() throws {
        let content = "<1>1. Inv /\\ TypeOK\n  BY Z3 DEF Inv\n"
        let failing = obligation(startLine: 1, goal: "Inv /\\ TypeOK")
        let plan = try XCTUnwrap(ProofAssist.planByDefInsertion(names: ["TypeOK"], for: failing, content: content))
        XCTAssertEqual(plan.updatedLine, "  BY Z3 DEF Inv, TypeOK")
    }

    func testInsertionPreservesTrailingComment() throws {
        let content = "<1>1. Inv\n  BY Z3 \\* tuned\n"
        let failing = obligation(startLine: 1, goal: "Inv")
        let plan = try XCTUnwrap(ProofAssist.planByDefInsertion(names: ["Inv"], for: failing, content: content))
        XCTAssertEqual(plan.updatedLine, "  BY Z3 DEF Inv\\* tuned")
    }

    func testNoInsertionWithoutProofLeaf() {
        // Structured proof (no BY/OBVIOUS near the step) must not be modified.
        let content = "<1>1. Inv\n<1>2. TypeOK\n<1>3. QED\n"
        let failing = obligation(startLine: 1, goal: "Inv")
        XCTAssertNil(ProofAssist.planByDefInsertion(names: ["Inv"], for: failing, content: content))
    }

    func testInsertionTargetsContinuationDefLine() throws {
        // Multi-line BY: DEF lives on a continuation line — extending the BY
        // line would produce an invalid second DEF clause.
        let content = "<1>1. Inv /\\ TypeOK\n  BY Z3, Zenon\n     DEF Inv\n"
        let failing = obligation(startLine: 1, goal: "Inv /\\ TypeOK")
        let plan = try XCTUnwrap(ProofAssist.planByDefInsertion(names: ["TypeOK"], for: failing, content: content))
        XCTAssertEqual(plan.lineIndex, 2)
        XCTAssertEqual(plan.updatedLine, "     DEF Inv, TypeOK")
    }

    func testInsertionBailsOnContinuingByList() {
        // BY line ends with a comma (clause continues): appending DEF here
        // would split the list — refuse instead.
        let content = "<1>1. Inv\n  BY Z3,\n     Zenon\n"
        let failing = obligation(startLine: 1, goal: "Inv")
        XCTAssertNil(ProofAssist.planByDefInsertion(names: ["Inv"], for: failing, content: content))
    }

    func testInsertionRefusesWrappedDefList() {
        // The DEF list itself ends with a comma (it continues onto the next
        // physical line). We can only edit one line, so inserting here would
        // orphan the `Helper` continuation (`Inv, TypeOK` / `Helper` with no comma
        // between TypeOK and Helper) — refuse rather than emit invalid TLA+ (e2e M4).
        let content = "<1>1. Inv /\\ TypeOK\n  BY Z3 DEF Inv,\n     Helper\n"
        let failing = obligation(startLine: 1, goal: "Inv /\\ TypeOK")
        XCTAssertNil(ProofAssist.planByDefInsertion(names: ["TypeOK"], for: failing, content: content))
    }

    func testInsertionExtendsSelfContainedDefList() throws {
        // A DEF list fully on one line (no trailing comma) is safely extended.
        let content = "<1>1. Inv /\\ TypeOK\n  BY Z3 DEF Inv\n"
        let failing = obligation(startLine: 1, goal: "Inv /\\ TypeOK")
        let plan = try XCTUnwrap(ProofAssist.planByDefInsertion(names: ["TypeOK"], for: failing, content: content))
        XCTAssertEqual(plan.updatedLine, "  BY Z3 DEF Inv, TypeOK")
    }

    func testInsertionDoesNotBorrowSiblingStepLeaf() {
        // This step (<1>1.) has no proof leaf of its own; the next sibling
        // <1>2. has a BY within the +2 look-ahead. The window must clamp at the
        // sibling's step marker, so no insertion is offered (e2e Low #7).
        let content = "<1>1. Foo\n<1>2. Bar\n  BY Z3\n"
        let failing = obligation(startLine: 1, goal: "Foo")
        XCTAssertNil(ProofAssist.planByDefInsertion(names: ["Foo"], for: failing, content: content))
    }

    // MARK: - Invariant candidates

    func testInvariantCandidatesRankAndFilter() {
        let failing = obligation(startLine: 1, goal: "Helper /\\ TypeOK /\\ Init => Inv'")
        let symbols = [
            symbol("TypeOK"),
            symbol("Inv"),
            symbol("Helper"),
            symbol("Init"),                       // structural — excluded
            symbol("Param", parameters: ["x"])    // parameterized — excluded
        ]
        let candidates = ProofAssist.invariantCandidates(for: failing, symbols: symbols)
        XCTAssertEqual(candidates, ["TypeOK", "Inv", "Helper"], "invariant-looking names rank first; Init excluded")
    }

    func testInvariantCandidatesEmptyWhenNoStatePredicates() {
        let failing = obligation(startLine: 1, goal: "x + 1 = 2")
        XCTAssertTrue(ProofAssist.invariantCandidates(for: failing, symbols: [symbol("x", kind: .variable)]).isEmpty)
    }
}
