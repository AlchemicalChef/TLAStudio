import XCTest
@testable import TLAStudioApp

final class TraceExplorerExpressionTests: XCTestCase {

    func testEvaluatesIdentifierLookup() throws {
        let result = try TraceExplorerExpressionEngine.evaluate(
            "x",
            with: ["x": .int(3)]
        )

        XCTAssertEqual(result, .int(3))
    }

    func testEvaluatesArithmeticExpression() throws {
        let result = try TraceExplorerExpressionEngine.evaluate(
            "x + 2 * y",
            with: ["x": .int(3), "y": .int(4)]
        )

        XCTAssertEqual(result, .int(11))
    }

    func testEvaluatesRecordFieldAccess() throws {
        let result = try TraceExplorerExpressionEngine.evaluate(
            "pc.worker",
            with: [
                "pc": .record([
                    "worker": .string("running")
                ])
            ]
        )

        XCTAssertEqual(result, .string("running"))
    }

    func testEvaluatesSequenceIndexing() throws {
        let result = try TraceExplorerExpressionEngine.evaluate(
            "queue[2]",
            with: [
                "queue": .sequence([.int(10), .int(20), .int(30)])
            ]
        )

        XCTAssertEqual(result, .int(20))
    }

    func testEvaluatesBuiltInFunctions() throws {
        let domain = try TraceExplorerExpressionEngine.evaluate(
            "DOMAIN queue",
            with: [
                "queue": .sequence([.int(10), .int(20), .int(30)])
            ]
        )
        let cardinality = try TraceExplorerExpressionEngine.evaluate(
            "Cardinality(S)",
            with: [
                "S": .set(Set([StateValueWrapper(.int(1)), StateValueWrapper(.int(2))]))
            ]
        )
        let length = try TraceExplorerExpressionEngine.evaluate(
            "Len(queue)",
            with: [
                "queue": .sequence([.int(10), .int(20), .int(30)])
            ]
        )

        XCTAssertEqual(
            domain,
            .set(Set([StateValueWrapper(.int(1)), StateValueWrapper(.int(2)), StateValueWrapper(.int(3))]))
        )
        XCTAssertEqual(cardinality, .int(2))
        XCTAssertEqual(length, .int(3))
    }

    func testEvaluatesLogicalOperators() throws {
        let result = try TraceExplorerExpressionEngine.evaluate(
            "x = 2 /\\ y > 1",
            with: [
                "x": .int(2),
                "y": .int(5)
            ]
        )

        XCTAssertEqual(result, .bool(true))
    }

    func testUnknownIdentifierThrowsUsefulError() {
        XCTAssertThrowsError(
            try TraceExplorerExpressionEngine.evaluate("missing", with: [:])
        ) { error in
            XCTAssertEqual(error as? TraceExpressionError, .unknownIdentifier("missing"))
        }
    }

    func testOutOfBoundsIndexThrowsUsefulError() {
        XCTAssertThrowsError(
            try TraceExplorerExpressionEngine.evaluate(
                "queue[4]",
                with: ["queue": .sequence([.int(1), .int(2)])]
            )
        ) { error in
            XCTAssertEqual(
                error as? TraceExpressionError,
                .invalidIndex("Sequence index 4 is out of bounds")
            )
        }
    }
}
