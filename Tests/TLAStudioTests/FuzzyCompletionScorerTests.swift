import XCTest
@testable import TLAStudioApp

final class FuzzyCompletionScorerTests: XCTestCase {

    private func score(_ query: String, _ candidate: String) -> Int? {
        FuzzyCompletionScorer.match(query: query, candidate: candidate)?.score
    }

    // MARK: - Tiers

    func testExactBeatsPrefixBeatsBoundaryBeatsSubstringBeatsSubsequence() throws {
        let exact = try XCTUnwrap(score("Init", "Init"))
        let prefix = try XCTUnwrap(score("Init", "InitState"))
        let boundary = try XCTUnwrap(score("tinv", "TypeInvariant"))
        let substring = try XCTUnwrap(score("nit", "Monitor"))
        let subsequence = try XCTUnwrap(score("mtr", "Monitor"))

        XCTAssertGreaterThan(exact, prefix)
        XCTAssertGreaterThan(prefix, boundary)
        XCTAssertGreaterThan(boundary, substring)
        XCTAssertGreaterThan(substring, subsequence)
    }

    func testCamelCaseBoundaryMatch() throws {
        let match = try XCTUnwrap(FuzzyCompletionScorer.match(query: "tinv", candidate: "TypeInvariant"))
        // 't' at 0, 'inv' at the Invariant boundary (index 4).
        XCTAssertEqual(match.matchedRanges, [0..<1, 4..<7])
        XCTAssertGreaterThanOrEqual(match.score, 600)
    }

    func testBackslashOperatorPrefix() throws {
        let cup = try XCTUnwrap(score("\\cu", "\\cup"))
        let cap = score("\\cu", "\\cap")
        XCTAssertGreaterThanOrEqual(cup, 800, "\\cu should prefix-match \\cup")
        XCTAssertNil(cap, "\\cu is not a subsequence of \\cap in order")
    }

    func testUnderscoreBoundary() throws {
        let match = try XCTUnwrap(FuzzyCompletionScorer.match(query: "tok", candidate: "type_ok"))
        XCTAssertGreaterThanOrEqual(match.score, 600)
    }

    func testNonSubsequenceReturnsNil() {
        XCTAssertNil(FuzzyCompletionScorer.match(query: "xyz", candidate: "Init"))
        XCTAssertNil(FuzzyCompletionScorer.match(query: "Initial", candidate: "Init"), "query longer than candidate")
    }

    func testEmptyQueryReturnsNil() {
        XCTAssertNil(FuzzyCompletionScorer.match(query: "", candidate: "Init"))
    }

    func testCaseExactScoresAboveCaseInsensitive() throws {
        let exactCase = try XCTUnwrap(score("Init", "InitState"))
        let wrongCase = try XCTUnwrap(score("init", "InitState"))
        XCTAssertGreaterThan(exactCase, wrongCase)
    }

    func testShorterCandidatePreferredOnEqualTier() throws {
        let short = try XCTUnwrap(score("In", "Init"))
        let long = try XCTUnwrap(score("In", "InitialPredicateState"))
        XCTAssertGreaterThan(short, long)
    }

    func testMatchedRangesAreContiguousForSubstring() throws {
        let match = try XCTUnwrap(FuzzyCompletionScorer.match(query: "nit", candidate: "Monitor"))
        XCTAssertEqual(match.matchedRanges, [2..<5])
    }

    func testBoundaryFirstFallsBackWhenBoundaryPathFails() throws {
        // Boundary-first picks 'i' at a boundary too far right and would strand
        // the rest of the query; the plain greedy pass must still match.
        XCTAssertNotNil(FuzzyCompletionScorer.match(query: "ior", candidate: "priorIn"))
    }

    // MARK: - Performance

    func testScoringTwoThousandCandidatesIsFast() {
        let candidates = (0..<2000).map { "SomeOperatorName\($0)Variant" }
        measure {
            for candidate in candidates {
                _ = FuzzyCompletionScorer.match(query: "sonv", candidate: candidate)
            }
        }
    }
}
