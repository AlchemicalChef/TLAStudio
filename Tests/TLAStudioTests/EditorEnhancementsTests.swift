import AppKit
import XCTest
@testable import TLAStudioApp

@MainActor
final class EditorEnhancementsTests: XCTestCase {

    func testBracketMatcherHandlesUTF16CursorOffsets() {
        let textView = makeTextView(with: "🙂(x)")
        let matcher = BracketMatcher(textView: textView)
        let text = textView.string as NSString
        let openIndex = text.range(of: "(").location
        let closeIndex = text.range(of: ")").location

        textView.setSelectedRange(NSRange(location: closeIndex, length: 0))
        NotificationCenter.default.post(name: NSTextView.didChangeSelectionNotification, object: textView)

        withExtendedLifetime(matcher) {
            let openColor = textView.textStorage?.attribute(.backgroundColor, at: openIndex, effectiveRange: nil) as? NSColor
            let closeColor = textView.textStorage?.attribute(.backgroundColor, at: closeIndex, effectiveRange: nil) as? NSColor

            XCTAssertNotNil(openColor)
            XCTAssertNotNil(closeColor)
        }
    }

    func testBracketMatcherRestoresOriginalBackgroundColor() {
        let textView = makeTextView(with: "(x)")
        let text = textView.string as NSString
        let openIndex = text.range(of: "(").location
        let closeIndex = text.range(of: ")").location
        let originalColor = NSColor.systemYellow

        textView.textStorage?.addAttribute(.backgroundColor, value: originalColor, range: NSRange(location: openIndex, length: 1))
        let matcher = BracketMatcher(textView: textView)
        textView.setSelectedRange(NSRange(location: closeIndex, length: 0))
        NotificationCenter.default.post(name: NSTextView.didChangeSelectionNotification, object: textView)
        matcher.setEnabled(false)

        let restoredColor = textView.textStorage?.attribute(.backgroundColor, at: openIndex, effectiveRange: nil) as? NSColor
        XCTAssertTrue(restoredColor?.isEqual(originalColor) == true)
        XCTAssertNil(textView.textStorage?.attribute(.backgroundColor, at: closeIndex, effectiveRange: nil))
    }

    private func makeTextView(with text: String) -> NSTextView {
        let scrollView = NSScrollView(frame: NSRect(x: 0, y: 0, width: 400, height: 200))
        let textView = NSTextView(frame: scrollView.bounds)
        scrollView.documentView = textView
        textView.string = text
        return textView
    }
}
