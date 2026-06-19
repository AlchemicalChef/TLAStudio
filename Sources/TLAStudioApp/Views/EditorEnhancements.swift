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
        tearDownLineHighlight()
    }

    // MARK: - Configuration

    func setEnabled(_ enabled: Bool) {
        self.enabled = enabled
        if enabled {
            setupLineHighlight()
            updateHighlight()
        } else {
            tearDownLineHighlight()
        }
    }

    func setHighlightColor(_ color: NSColor) {
        self.highlightColor = color
        lineHighlightView?.layer?.backgroundColor = color.cgColor
    }

    // MARK: - Setup

    private func setupLineHighlight() {
        guard let textView = textView else { return }

        if lineHighlightView == nil,
           let scrollView = textView.enclosingScrollView {
            let highlightView = NSView(frame: .zero)
            highlightView.wantsLayer = true
            highlightView.layer?.backgroundColor = highlightColor.cgColor
            highlightView.alphaValue = 1.0

            // Add to the clip view so the highlight scrolls with the text content.
            scrollView.contentView.addSubview(highlightView, positioned: .below, relativeTo: textView)
            lineHighlightView = highlightView
        }

        installSelectionObserver(for: textView) { [weak self] in
            self?.updateHighlight()
        }
        updateHighlight()
    }

    private func tearDownLineHighlight() {
        removeSelectionObserver()
        lineHighlightView?.removeFromSuperview()
        lineHighlightView = nil
    }

    private func installSelectionObserver(for textView: NSTextView, handler: @escaping () -> Void) {
        removeSelectionObserver()
        selectionObserver = NotificationCenter.default.addObserver(
            forName: NSTextView.didChangeSelectionNotification,
            object: textView,
            queue: .main
        ) { _ in
            handler()
        }
    }

    private func removeSelectionObserver() {
        guard let selectionObserver else { return }
        NotificationCenter.default.removeObserver(selectionObserver)
        self.selectionObserver = nil
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
        let open: unichar
        let close: unichar

        init(open: Character, close: Character) {
            self.open = String(open).utf16.first ?? 0
            self.close = String(close).utf16.first ?? 0
        }
    }

    private struct HighlightedBracket {
        let range: NSRange
        let originalBackgroundColor: Any?
    }

    // MARK: - Properties

    private weak var textView: NSTextView?
    private var enabled: Bool = true
    private var highlightColor: NSColor = NSColor.systemBlue.withAlphaComponent(0.3)

    private var highlightedBrackets: [HighlightedBracket] = []
    private var selectionObserver: NSObjectProtocol?

    // No `<`/`>` pair: in TLA+ those are pervasive comparison operators (x < y,
    // =<, >=) and the tuple/sequence delimiters are the DOUBLE `<<`/`>>`, so a
    // single-angle pair flagged a "match" next to almost every operator. Matching
    // real `<<`/`>>` needs a two-char scanner (see SourceEditor/BracketMatcher).
    private let bracketPairs: [BracketPair] = [
        BracketPair(open: "(", close: ")"),
        BracketPair(open: "[", close: "]"),
        BracketPair(open: "{", close: "}"),
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
        removeSelectionObserver()
    }

    // MARK: - Configuration

    func setEnabled(_ enabled: Bool) {
        self.enabled = enabled
        if enabled {
            setupBracketMatching()
            updateBracketHighlight()
        } else {
            removeSelectionObserver()
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

        installSelectionObserver(for: textView) { [weak self] in
            self?.updateBracketHighlight()
        }
        updateBracketHighlight()
    }

    private func installSelectionObserver(for textView: NSTextView, handler: @escaping () -> Void) {
        removeSelectionObserver()
        selectionObserver = NotificationCenter.default.addObserver(
            forName: NSTextView.didChangeSelectionNotification,
            object: textView,
            queue: .main
        ) { _ in
            handler()
        }
    }

    private func removeSelectionObserver() {
        guard let selectionObserver else { return }
        NotificationCenter.default.removeObserver(selectionObserver)
        self.selectionObserver = nil
    }

    // MARK: - Bracket Finding

    private func updateBracketHighlight() {
        guard enabled, let textView = textView else { return }

        // Clear previous highlights
        clearHighlights()

        let selectedRange = textView.selectedRange()
        guard selectedRange.location != NSNotFound else { return }

        let text = textView.string as NSString

        // Check character at cursor and before cursor
        let positions = candidatePositions(for: selectedRange.location)

        for pos in positions where pos < text.length {
            let char = text.character(at: pos)

            if let pair = bracketPairs.first(where: { $0.open == char }) {
                if let matchPos = findMatchingCloseBracket(from: pos, pair: pair, in: text) {
                    highlightBrackets(at: pos, and: matchPos)
                    return
                }
            }

            if let pair = bracketPairs.first(where: { $0.close == char }) {
                if let matchPos = findMatchingOpenBracket(from: pos, pair: pair, in: text) {
                    highlightBrackets(at: matchPos, and: pos)
                    return
                }
            }
        }
    }

    private func candidatePositions(for location: Int) -> [Int] {
        guard location > 0 else { return [0] }
        return [location, location - 1]
    }

    private func findMatchingCloseBracket(from start: Int, pair: BracketPair, in text: NSString) -> Int? {
        var depth = 1
        var pos = start + 1

        while pos < text.length && depth > 0 {
            let character = text.character(at: pos)
            if character == pair.open {
                depth += 1
            } else if character == pair.close {
                depth -= 1
            }
            if depth == 0 {
                return pos
            }
            pos += 1
        }

        return nil
    }

    private func findMatchingOpenBracket(from start: Int, pair: BracketPair, in text: NSString) -> Int? {
        var depth = 1
        var pos = start - 1

        while pos >= 0 && depth > 0 {
            let character = text.character(at: pos)
            if character == pair.close {
                depth += 1
            } else if character == pair.open {
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

        highlightedBrackets = [range1, range2].map { range in
            let existingBackground = textStorage.attribute(.backgroundColor, at: range.location, effectiveRange: nil)
            return HighlightedBracket(range: range, originalBackgroundColor: existingBackground)
        }

        textStorage.beginEditing()
        textStorage.addAttribute(.backgroundColor, value: highlightColor, range: range1)
        textStorage.addAttribute(.backgroundColor, value: highlightColor, range: range2)
        textStorage.endEditing()
    }

    private func clearHighlights() {
        guard let textView = textView,
              let textStorage = textView.textStorage else { return }

        guard !highlightedBrackets.isEmpty else { return }

        textStorage.beginEditing()
        for bracket in highlightedBrackets where bracket.range.location + bracket.range.length <= textStorage.length {
            if let originalBackgroundColor = bracket.originalBackgroundColor {
                textStorage.addAttribute(.backgroundColor, value: originalBackgroundColor, range: bracket.range)
            } else {
                textStorage.removeAttribute(.backgroundColor, range: bracket.range)
            }
        }
        textStorage.endEditing()

        highlightedBrackets = []
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
