import AppKit
import Foundation

// MARK: - Current Line Highlighter

/// Highlights the current line in the editor
final class CurrentLineHighlighter {

    // MARK: - Properties

    private weak var textView: NSTextView?
    private var lineHighlightView: NSView?
    private var enabled: Bool = true
    private var highlightColor: NSColor = NSColor(calibratedWhite: 0.5, alpha: 0.08)

    private var selectionObserver: NSObjectProtocol?

    // MARK: - Initialization

    init(textView: NSTextView, enabled: Bool = true) {
        self.textView = textView
        self.enabled = enabled

        if enabled {
            setupLineHighlight()
        }
    }

    deinit {
        if let observer = selectionObserver {
            NotificationCenter.default.removeObserver(observer)
        }
        lineHighlightView?.removeFromSuperview()
    }

    // MARK: - Configuration

    func setEnabled(_ enabled: Bool) {
        self.enabled = enabled
        if enabled {
            setupLineHighlight()
            updateHighlight()
        } else {
            lineHighlightView?.removeFromSuperview()
            lineHighlightView = nil
        }
    }

    func setHighlightColor(_ color: NSColor) {
        self.highlightColor = color
        lineHighlightView?.layer?.backgroundColor = color.cgColor
    }

    // MARK: - Setup

    private func setupLineHighlight() {
        guard let textView = textView else { return }

        // Create highlight view
        let highlightView = NSView(frame: .zero)
        highlightView.wantsLayer = true
        highlightView.layer?.backgroundColor = highlightColor.cgColor
        highlightView.alphaValue = 1.0

        // Insert behind text
        if let scrollView = textView.enclosingScrollView {
            // Add to clip view so it scrolls with content
            if let clipView = scrollView.contentView as? NSClipView {
                clipView.addSubview(highlightView, positioned: .below, relativeTo: textView)
            }
        }

        lineHighlightView = highlightView

        // Observe selection changes
        selectionObserver = NotificationCenter.default.addObserver(
            forName: NSTextView.didChangeSelectionNotification,
            object: textView,
            queue: .main
        ) { [weak self] _ in
            self?.updateHighlight()
        }

        // Initial update
        updateHighlight()
    }

    // MARK: - Update

    func updateHighlight() {
        guard enabled,
              let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer,
              let highlightView = lineHighlightView else {
            return
        }

        // Get current line rect
        let selectedRange = textView.selectedRange()
        if selectedRange.location == NSNotFound {
            highlightView.isHidden = true
            return
        }

        // Calculate line range
        let text = textView.string as NSString
        let lineRange = text.lineRange(for: NSRange(location: selectedRange.location, length: 0))

        // Get bounding rect for line
        let glyphRange = layoutManager.glyphRange(forCharacterRange: lineRange, actualCharacterRange: nil)
        var lineRect = layoutManager.boundingRect(forGlyphRange: glyphRange, in: textContainer)

        // Adjust for text container inset
        lineRect.origin.y += textView.textContainerInset.height
        lineRect.origin.x = 0
        lineRect.size.width = textView.bounds.width

        // Position highlight
        highlightView.frame = lineRect
        highlightView.isHidden = false
    }
}

// MARK: - Bracket Matcher

/// Highlights matching brackets in the editor
final class BracketMatcher {

    // MARK: - Types

    private struct BracketPair {
        let open: Character
        let close: Character
    }

    // MARK: - Properties

    private weak var textView: NSTextView?
    private var enabled: Bool = true
    private var highlightColor: NSColor = NSColor.systemBlue.withAlphaComponent(0.3)

    private var matchHighlightRanges: [NSRange] = []
    private var selectionObserver: NSObjectProtocol?

    private let bracketPairs: [BracketPair] = [
        BracketPair(open: "(", close: ")"),
        BracketPair(open: "[", close: "]"),
        BracketPair(open: "{", close: "}"),
        BracketPair(open: "<", close: ">"),
    ]

    // MARK: - Initialization

    init(textView: NSTextView, enabled: Bool = true) {
        self.textView = textView
        self.enabled = enabled

        if enabled {
            setupBracketMatching()
        }
    }

    deinit {
        if let observer = selectionObserver {
            NotificationCenter.default.removeObserver(observer)
        }
    }

    // MARK: - Configuration

    func setEnabled(_ enabled: Bool) {
        self.enabled = enabled
        if enabled {
            setupBracketMatching()
            updateBracketHighlight()
        } else {
            clearHighlights()
        }
    }

    func setHighlightColor(_ color: NSColor) {
        self.highlightColor = color
        updateBracketHighlight()
    }

    // MARK: - Setup

    private func setupBracketMatching() {
        guard let textView = textView else { return }

        // Observe selection changes
        selectionObserver = NotificationCenter.default.addObserver(
            forName: NSTextView.didChangeSelectionNotification,
            object: textView,
            queue: .main
        ) { [weak self] _ in
            self?.updateBracketHighlight()
        }

        // Initial update
        updateBracketHighlight()
    }

    // MARK: - Bracket Finding

    private func updateBracketHighlight() {
        guard enabled, let textView = textView else { return }

        // Clear previous highlights
        clearHighlights()

        let selectedRange = textView.selectedRange()
        guard selectedRange.location != NSNotFound else { return }

        let text = textView.string
        let nsText = text as NSString

        // Check character at cursor and before cursor
        let positions = [selectedRange.location, max(0, selectedRange.location - 1)]

        for pos in positions where pos < nsText.length {
            let char = Character(UnicodeScalar(nsText.character(at: pos))!)

            // Check if it's an opening bracket
            if let pair = bracketPairs.first(where: { $0.open == char }) {
                if let matchPos = findMatchingCloseBracket(from: pos, pair: pair, in: text) {
                    highlightBrackets(at: pos, and: matchPos)
                    return
                }
            }

            // Check if it's a closing bracket
            if let pair = bracketPairs.first(where: { $0.close == char }) {
                if let matchPos = findMatchingOpenBracket(from: pos, pair: pair, in: text) {
                    highlightBrackets(at: matchPos, and: pos)
                    return
                }
            }
        }
    }

    private func findMatchingCloseBracket(from start: Int, pair: BracketPair, in text: String) -> Int? {
        let chars = Array(text)
        var depth = 1
        var pos = start + 1

        while pos < chars.count && depth > 0 {
            if chars[pos] == pair.open {
                depth += 1
            } else if chars[pos] == pair.close {
                depth -= 1
            }
            if depth == 0 {
                return pos
            }
            pos += 1
        }

        return nil
    }

    private func findMatchingOpenBracket(from start: Int, pair: BracketPair, in text: String) -> Int? {
        let chars = Array(text)
        var depth = 1
        var pos = start - 1

        while pos >= 0 && depth > 0 {
            if chars[pos] == pair.close {
                depth += 1
            } else if chars[pos] == pair.open {
                depth -= 1
            }
            if depth == 0 {
                return pos
            }
            pos -= 1
        }

        return nil
    }

    // MARK: - Highlighting

    private func highlightBrackets(at pos1: Int, and pos2: Int) {
        guard let textView = textView,
              let textStorage = textView.textStorage else { return }

        let range1 = NSRange(location: pos1, length: 1)
        let range2 = NSRange(location: pos2, length: 1)

        // Store ranges for clearing later
        matchHighlightRanges = [range1, range2]

        // Apply highlight
        textStorage.beginEditing()
        textStorage.addAttribute(.backgroundColor, value: highlightColor, range: range1)
        textStorage.addAttribute(.backgroundColor, value: highlightColor, range: range2)
        textStorage.endEditing()
    }

    private func clearHighlights() {
        guard let textView = textView,
              let textStorage = textView.textStorage else { return }

        guard !matchHighlightRanges.isEmpty else { return }

        textStorage.beginEditing()
        for range in matchHighlightRanges {
            if range.location + range.length <= textStorage.length {
                textStorage.removeAttribute(.backgroundColor, range: range)
            }
        }
        textStorage.endEditing()

        matchHighlightRanges = []
    }
}

// MARK: - Combined Editor Enhancements

/// Manages all editor visual enhancements
final class EditorEnhancements {
    private let currentLineHighlighter: CurrentLineHighlighter?
    private let bracketMatcher: BracketMatcher?

    init(textView: NSTextView, enableCurrentLineHighlight: Bool, enableBracketMatching: Bool) {
        if enableCurrentLineHighlight {
            currentLineHighlighter = CurrentLineHighlighter(textView: textView)
        } else {
            currentLineHighlighter = nil
        }

        if enableBracketMatching {
            bracketMatcher = BracketMatcher(textView: textView)
        } else {
            bracketMatcher = nil
        }
    }

    func setCurrentLineHighlightEnabled(_ enabled: Bool) {
        currentLineHighlighter?.setEnabled(enabled)
    }

    func setBracketMatchingEnabled(_ enabled: Bool) {
        bracketMatcher?.setEnabled(enabled)
    }

    func setCurrentLineColor(_ color: NSColor) {
        currentLineHighlighter?.setHighlightColor(color)
    }

    func setBracketHighlightColor(_ color: NSColor) {
        bracketMatcher?.setHighlightColor(color)
    }

    func updateCurrentLineHighlight() {
        currentLineHighlighter?.updateHighlight()
    }
}
