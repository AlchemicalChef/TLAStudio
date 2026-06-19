import XCTest
import AppKit
@testable import SourceEditor

/// Correctness tests for the binary-search visible-token slice used by the
/// large-file scroll highlighting path. The invariant: the returned index range
/// must contain EVERY token that actually intersects the visible range (callers
/// then intersection-filter within the slice), for any viewport position.
final class TreeSitterTokenSliceTests: XCTestCase {

    private func tok(_ location: Int, _ length: Int, _ name: String = "keyword") -> (NSRange, String) {
        (NSRange(location: location, length: length), name)
    }

    private func maxLen(_ tokens: [(NSRange, String)]) -> Int {
        tokens.map { $0.0.length }.max() ?? 0
    }

    /// Brute-force: indices of all tokens intersecting `visible`.
    private func bruteForce(_ tokens: [(NSRange, String)], _ visible: NSRange) -> Set<Int> {
        var result = Set<Int>()
        for (index, token) in tokens.enumerated()
        where NSIntersectionRange(token.0, visible).length > 0 {
            result.insert(index)
        }
        return result
    }

    /// Indices the slice yields after the same intersection filter the highlighter applies.
    private func viaSlice(_ tokens: [(NSRange, String)], _ visible: NSRange) -> Set<Int> {
        let range = TLASyntaxHighlighter.visibleTokenIndexRange(
            in: tokens, visibleRange: visible, maxTokenLength: maxLen(tokens)
        )
        var result = Set<Int>()
        for index in range where NSIntersectionRange(tokens[index].0, visible).length > 0 {
            result.insert(index)
        }
        return result
    }

    func testSliceMatchesBruteForceAcrossViewports() {
        // Sorted-by-location tokens including one long span (a "block comment").
        let tokens = [
            tok(0, 3), tok(5, 2), tok(10, 4), tok(20, 100),
            tok(130, 3), tok(140, 5), tok(141, 1), tok(200, 2),
        ]
        for visibleLoc in stride(from: 0, through: 220, by: 3) {
            for visibleLen in [1, 8, 37, 90] {
                let visible = NSRange(location: visibleLoc, length: visibleLen)
                XCTAssertEqual(
                    viaSlice(tokens, visible), bruteForce(tokens, visible),
                    "slice ≠ brute force at \(visible)"
                )
            }
        }
    }

    func testEmptyTokensYieldsEmptyRange() {
        let range = TLASyntaxHighlighter.visibleTokenIndexRange(
            in: [], visibleRange: NSRange(location: 0, length: 10), maxTokenLength: 0
        )
        XCTAssertEqual(range, 0..<0)
    }

    func testLongTokenStartingBeforeWindowIsInSlice() {
        // [20,120) must be found when the viewport is [100,110), even though the
        // token STARTS far before the window — this is what maxTokenLength guards.
        let tokens = [tok(20, 100), tok(130, 3)]
        let range = TLASyntaxHighlighter.visibleTokenIndexRange(
            in: tokens, visibleRange: NSRange(location: 100, length: 10), maxTokenLength: maxLen(tokens)
        )
        XCTAssertTrue(range.contains(0))
    }

    func testViewportPastAllTokensIsEmpty() {
        let tokens = [tok(0, 3), tok(10, 4)]
        XCTAssertTrue(viaSlice(tokens, NSRange(location: 500, length: 10)).isEmpty)
    }
}
