import XCTest
@testable import TLAStudioApp

final class ProofSkeletonGeneratorTests: XCTestCase {

    private func symbol(_ name: String, kind: TLASymbolKind = .operator) -> TLASymbol {
        TLASymbol(
            name: name, kind: kind,
            range: TLARange(start: TLAPosition(line: 0, column: 0), end: TLAPosition(line: 0, column: 1)),
            selectionRange: nil, children: [], parameters: []
        )
    }

    // MARK: - Invariance shape

    func testInvarianceSkeletonWithVarsSymbol() throws {
        let content = """
        ---- MODULE M ----
        vars == <<x>>
        THEOREM Spec => []TypeOK
        ====
        """
        let insertion = try XCTUnwrap(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 2,
            content: content,
            symbols: [symbol("vars")]
        ))

        XCTAssertEqual(insertion.insertAfterLine, 2)
        XCTAssertEqual(insertion.lines, [
            "PROOF",
            "<1>1. Init => TypeOK",
            "  BY DEF Init, TypeOK",
            "<1>2. TypeOK /\\ [Next]_vars => TypeOK'",
            "  BY DEF TypeOK, Next, vars",
            "<1>3. QED",
            "  BY <1>1, <1>2, PTL DEF Spec"
        ])
    }

    func testInvarianceSkeletonBuildsVarsTupleFromVariables() throws {
        let content = "THEOREM Spec => []Inv"
        let insertion = try XCTUnwrap(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 0,
            content: content,
            symbols: [symbol("x", kind: .variable), symbol("y", kind: .variable)]
        ))
        XCTAssertTrue(insertion.lines.contains("<1>2. Inv /\\ [Next]_<<x, y>> => Inv'"))
    }

    func testNamedTheoremGoalIsUnwrapped() throws {
        let content = "THEOREM Safety == Spec => []Inv"
        let insertion = try XCTUnwrap(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 0, content: content, symbols: [symbol("vars")]
        ))
        XCTAssertTrue(insertion.lines.contains("<1>1. Init => Inv"))
    }

    func testMultiLineTheoremStatement() throws {
        let content = """
        THEOREM Safety ==
            Spec => []Inv
        Next == TRUE
        """
        let insertion = try XCTUnwrap(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 1, content: content, symbols: [symbol("vars")]
        ))
        XCTAssertEqual(insertion.insertAfterLine, 1, "skeleton goes after the continuation line")
    }

    // MARK: - Conjunction shape

    func testConjunctionSkeleton() throws {
        let content = "THEOREM TypeOK /\\ Inv /\\ Fair"
        let insertion = try XCTUnwrap(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 0, content: content, symbols: []
        ))
        XCTAssertEqual(insertion.lines, [
            "PROOF",
            "<1>1. TypeOK",
            "<1>2. Inv",
            "<1>3. Fair",
            "<1>4. QED",
            "  BY <1>1, <1>2, <1>3"
        ])
    }

    func testConjunctionRespectsBrackets() throws {
        // The /\ inside the tuple must not split.
        let content = "THEOREM (A /\\ B) /\\ C"
        let insertion = try XCTUnwrap(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 0, content: content, symbols: []
        ))
        XCTAssertEqual(insertion.lines[1], "<1>1. (A /\\ B)")
        XCTAssertEqual(insertion.lines[2], "<1>2. C")
    }

    func testConjunctionIgnoresCommentedJunction() {
        // The /\ sits inside a block comment (with unbalanced brackets that
        // would confuse a comment-unaware depth counter) — it must not split,
        // so the goal has no top-level conjunction and no skeleton is offered.
        let content = "THEOREM (* ) /\\ ( *) X"
        XCTAssertNil(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 0, content: content, symbols: []
        ))
    }

    // MARK: - Universal shape

    func testUniversalSkeleton() throws {
        let content = "THEOREM \\A n \\in Nat : n >= 0"
        let insertion = try XCTUnwrap(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 0, content: content, symbols: []
        ))
        XCTAssertEqual(insertion.lines, [
            "PROOF",
            "<1> TAKE n \\in Nat",
            "<1> QED"
        ])
    }

    // MARK: - Refusals

    func testRefusesWhenProofExists() {
        let content = """
        THEOREM Spec => []Inv
        PROOF
        <1>1. QED
        """
        XCTAssertNil(ProofSkeletonGenerator.skeleton(forTheoremAtLine: 0, content: content, symbols: []))
    }

    func testRefusesWhenByLeafExists() {
        let content = "THEOREM Spec => []Inv\n  BY PTL DEF Spec\n"
        XCTAssertNil(ProofSkeletonGenerator.skeleton(forTheoremAtLine: 0, content: content, symbols: []))
    }

    func testRefusesUnrecognizedGoal() {
        XCTAssertNil(ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: 0,
            content: "THEOREM Spec => <>Done",
            symbols: []
        ))
    }

    func testRefusesWhenCursorNotOnTheorem() {
        let content = "Init == x = 0\nNext == x' = x"
        XCTAssertNil(ProofSkeletonGenerator.skeleton(forTheoremAtLine: 1, content: content, symbols: []))
    }
}
