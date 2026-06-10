import XCTest
@testable import TLAStudioApp

final class NextActionDecomposerTests: XCTestCase {

    // MARK: - body(ofDefinition:)

    func testBodyExtractionReturnsRemainderAndColumn() throws {
        let result = try XCTUnwrap(NextActionDecomposer.body(ofDefinition: "Next == A \\/ B"))
        XCTAssertEqual(result.body, " A \\/ B")
        XCTAssertEqual(result.startColumn, 7)
    }

    func testBodyExtractionSkipsParenthesizedHeader() throws {
        let result = try XCTUnwrap(NextActionDecomposer.body(ofDefinition: "Act(p, q) == p \\/ q"))
        XCTAssertEqual(result.body, " p \\/ q")
    }

    func testBodyExtractionReturnsNilWithoutDefinition() {
        XCTAssertNil(NextActionDecomposer.body(ofDefinition: "just an expression"))
    }

    // MARK: - Single-line splits

    func testSplitsSingleLineInfixDisjunction() throws {
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: " Inc \\/ Push"))
        XCTAssertEqual(actions.map(\.label), ["Inc", "Push"])
        XCTAssertEqual(actions.map(\.expression), ["Inc", "Push"])
    }

    func testSingleLineSplitRespectsConjunctionPrecedence() throws {
        // A \/ B /\ C \/ D  ≡  A \/ (B /\ C) \/ D
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: "A \\/ B /\\ C \\/ D"))
        XCTAssertEqual(actions.map(\.expression), ["A", "B /\\ C", "D"])
    }

    func testParenthesesShieldNestedDisjunction() throws {
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: "A \\/ (B \\/ C)"))
        XCTAssertEqual(actions.map(\.expression), ["A", "(B \\/ C)"])
    }

    func testTuplesShieldDisjunctionTokens() throws {
        let actions = try XCTUnwrap(
            NextActionDecomposer.decompose(nextBody: "x' = <<TRUE \\/ FALSE>> \\/ Reset")
        )
        XCTAssertEqual(actions.map(\.expression), ["x' = <<TRUE \\/ FALSE>>", "Reset"])
    }

    func testCommentsAndStringsAreIgnored() {
        // The only `\/` tokens are inside a comment and a string — no split.
        let body = #" Act(s) /\ s = "a \/ b"  \* alt: X \/ Y"#
        XCTAssertNil(NextActionDecomposer.decompose(nextBody: body))
    }

    // MARK: - Multi-line splits

    func testSplitsBulletedDisjunctList() throws {
        let body = """

            \\/ Inc
            \\/ Push
        """
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: body))
        XCTAssertEqual(actions.map(\.label), ["Inc", "Push"])
    }

    func testRefusesConjunctionTopLevel() {
        // /\-bulleted top level containing nested \/-bullets must not split.
        let body = """
         /\\ guard
         /\\ \\/ A
            \\/ B
        """
        XCTAssertNil(NextActionDecomposer.decompose(nextBody: body))
    }

    func testNoDisjunctionReturnsNil() {
        XCTAssertNil(NextActionDecomposer.decompose(nextBody: " \\E p \\in Procs: Step(p)"))
        XCTAssertNil(NextActionDecomposer.decompose(nextBody: " Inc"))
    }

    func testNestedBulletsStayWithTheirDisjunct() throws {
        let body = """
        \\/ /\\ g
           /\\ h
        \\/ B
        """
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: body, bodyStartColumn: 0))
        XCTAssertEqual(actions.count, 2)
        // The nested /\-bullets keep their mutual alignment after dedenting.
        XCTAssertEqual(actions[0].expression, "/\\ g\n/\\ h")
        XCTAssertEqual(actions[1].expression, "B")
    }

    func testNestedDeeperDisjunctionBulletsAreNotSplitPoints() throws {
        let body = """
        \\/ A
        \\/ \\/ B
           \\/ C
        """
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: body))
        XCTAssertEqual(actions.count, 2)
        XCTAssertEqual(actions[0].expression, "A")
        XCTAssertEqual(actions[1].expression, "\\/ B\n\\/ C")
    }

    func testQuantifiedDisjunctsSplitAndLabelCleanly() throws {
        let body = #" Timeout \/ \E p \in Procs: Send(p)"#
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: body))
        XCTAssertEqual(actions.map(\.label), ["Timeout", #"\E p \in Procs: Send(p)"#])
    }

    func testLongLabelsAreTruncated() throws {
        let longDisjunct = "ThisIsAnExtremelyLongActionExpressionName(aaaa, bbbb, cccc)"
        let actions = try XCTUnwrap(NextActionDecomposer.decompose(nextBody: "A \\/ \(longDisjunct)"))
        XCTAssertEqual(actions.count, 2)
        XCTAssertLessThanOrEqual(actions[1].label.count, 48)
        XCTAssertTrue(actions[1].label.hasSuffix("…"))
    }
}
