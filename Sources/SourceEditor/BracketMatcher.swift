import AppKit

// MARK: - Bracket Matcher

/// Handles bracket matching and highlighting for TLA+ source code
public final class BracketMatcher {

    // MARK: - Types

    /// A bracket pair definition
    public struct BracketPair {
        let open: String
        let close: String

        public init(open: String, close: String) {
            self.open = open
            self.close = close
        }
    }

    /// Result of finding a matching bracket
    public struct MatchResult {
        public let openRange: NSRange
        public let closeRange: NSRange
        public let isOpenBracket: Bool  // true if cursor is at open bracket

        public init(openRange: NSRange, closeRange: NSRange, isOpenBracket: Bool) {
            self.openRange = openRange
            self.closeRange = closeRange
            self.isOpenBracket = isOpenBracket
        }
    }

    // MARK: - Constants

    /// Standard bracket pairs for TLA+
    public static let standardPairs: [BracketPair] = [
        BracketPair(open: "(", close: ")"),
        BracketPair(open: "[", close: "]"),
        BracketPair(open: "{", close: "}"),
        BracketPair(open: "<<", close: ">>"),
        BracketPair(open: "\\langle", close: "\\rangle"),
    ]

    /// Highlight color for matching brackets
    public static let matchHighlightColor = NSColor.systemYellow.withAlphaComponent(0.3)

    // MARK: - Properties

    private let pairs: [BracketPair]

    // MARK: - Character Array Cache
    // Caches the character array to avoid O(n) Array(text) conversion on every cursor movement.
    // This is a critical performance optimization for large files (10K+ lines).
    private var cachedTextLength: Int = 0
    private var cachedTextHash: Int = 0
    private var cachedChars: [Character] = []

    /// Get or create cached character array for text.
    /// Only recreates the array if the text has changed.
    /// Uses length + hash for cache validation to detect mutations safely.
    private func getChars(for text: String) -> [Character] {
        let textLength = text.count
        let textHash = text.hashValue

        // Use both length and hash to detect changes
        // This is safer than string equality for detecting NSMutableString mutations
        if textLength == cachedTextLength && textHash == cachedTextHash && cachedChars.count == textLength {
            return cachedChars
        }

        cachedTextLength = textLength
        cachedTextHash = textHash
        cachedChars = Array(text)
        return cachedChars
    }

    /// Invalidate the cache (call when text is known to have changed)
    public func invalidateCache() {
        cachedTextLength = 0
        cachedTextHash = 0
        cachedChars = []
    }

    // MARK: - Initialization

    public init(pairs: [BracketPair] = standardPairs) {
        self.pairs = pairs
    }

    // MARK: - Public Methods

    /// Find the matching bracket for the bracket at or adjacent to the given position
    /// - Parameters:
    ///   - text: The source text
    ///   - position: The cursor position
    /// - Returns: The match result if a matching bracket is found
    public func findMatchingBracket(in text: String, at position: Int) -> MatchResult? {
        // Use cached character array to avoid O(n) conversion on every call
        let chars = getChars(for: text)
        let maxIndex = chars.count

        // Look at character at position (cursor is before this char)
        if position < maxIndex {
            if let result = findMatch(chars: chars, at: position) {
                return result
            }
        }

        // Look at character before position (cursor is after this char)
        if position > 0 {
            if let result = findMatch(chars: chars, at: position - 1) {
                return result
            }
        }

        return nil
    }

    /// Check if a position is at a bracket character
    public func isAtBracket(in text: String, at position: Int) -> Bool {
        let chars = getChars(for: text)
        let maxIndex = chars.count

        if position < maxIndex {
            if getBracketInfo(chars: chars, at: position) != nil {
                return true
            }
        }

        if position > 0 {
            if getBracketInfo(chars: chars, at: position - 1) != nil {
                return true
            }
        }

        return false
    }

    // MARK: - Private Methods

    private struct BracketInfo {
        let pair: BracketPair
        let isOpen: Bool
        let range: NSRange
    }

    private func findMatch(chars: [Character], at position: Int) -> MatchResult? {
        guard let info = getBracketInfo(chars: chars, at: position) else {
            return nil
        }

        if info.isOpen {
            // Find matching close bracket
            if let closeRange = findCloseBracket(chars: chars, pair: info.pair, startAfter: position + info.pair.open.count) {
                return MatchResult(openRange: info.range, closeRange: closeRange, isOpenBracket: true)
            }
        } else {
            // Find matching open bracket
            if let openRange = findOpenBracket(chars: chars, pair: info.pair, startBefore: position) {
                return MatchResult(openRange: openRange, closeRange: info.range, isOpenBracket: false)
            }
        }

        return nil
    }

    private func getBracketInfo(chars: [Character], at position: Int) -> BracketInfo? {
        for pair in pairs {
            // Check if open bracket starts at this position
            let openEnd = position + pair.open.count
            if openEnd <= chars.count {
                let substring = String(chars[position..<openEnd])
                if substring == pair.open {
                    return BracketInfo(
                        pair: pair,
                        isOpen: true,
                        range: NSRange(location: position, length: pair.open.count)
                    )
                }
            }

            // Check if close bracket starts at this position
            let closeEnd = position + pair.close.count
            if closeEnd <= chars.count {
                let substring = String(chars[position..<closeEnd])
                if substring == pair.close {
                    return BracketInfo(
                        pair: pair,
                        isOpen: false,
                        range: NSRange(location: position, length: pair.close.count)
                    )
                }
            }
        }

        return nil
    }

    private func findCloseBracket(chars: [Character], pair: BracketPair, startAfter: Int) -> NSRange? {
        var depth = 1
        var i = startAfter

        while i < chars.count {
            // Check for open bracket (increase depth)
            let openEnd = i + pair.open.count
            if openEnd <= chars.count {
                let substring = String(chars[i..<openEnd])
                if substring == pair.open {
                    depth += 1
                    i = openEnd
                    continue
                }
            }

            // Check for close bracket (decrease depth)
            let closeEnd = i + pair.close.count
            if closeEnd <= chars.count {
                let substring = String(chars[i..<closeEnd])
                if substring == pair.close {
                    depth -= 1
                    if depth == 0 {
                        return NSRange(location: i, length: pair.close.count)
                    }
                    i = closeEnd
                    continue
                }
            }

            i += 1
        }

        return nil
    }

    private func findOpenBracket(chars: [Character], pair: BracketPair, startBefore: Int) -> NSRange? {
        var depth = 1
        var i = startBefore - 1

        while i >= 0 {
            // Check for close bracket (increase depth) - search backwards
            let closeStart = i - pair.close.count + 1
            if closeStart >= 0 {
                let substring = String(chars[closeStart...(i)])
                if substring == pair.close {
                    depth += 1
                    i = closeStart - 1
                    continue
                }
            }

            // Check for open bracket (decrease depth) - search backwards
            let openStart = i - pair.open.count + 1
            if openStart >= 0 {
                let substring = String(chars[openStart...(i)])
                if substring == pair.open {
                    depth -= 1
                    if depth == 0 {
                        return NSRange(location: openStart, length: pair.open.count)
                    }
                    i = openStart - 1
                    continue
                }
            }

            i -= 1
        }

        return nil
    }
}

// MARK: - NSTextView Extension for Bracket Highlighting

public extension NSTextView {

    /// Attribute key for bracket highlight
    static let bracketHighlightKey = NSAttributedString.Key("TLABracketHighlight")

    /// Associated object key for cached BracketMatcher
    private static var bracketMatcherKey: UInt8 = 0

    /// Get or create a cached BracketMatcher for this text view.
    /// Reusing the same instance allows the character array cache to be effective.
    private var cachedBracketMatcher: BracketMatcher {
        if let matcher = objc_getAssociatedObject(self, &NSTextView.bracketMatcherKey) as? BracketMatcher {
            return matcher
        }
        let matcher = BracketMatcher()
        objc_setAssociatedObject(self, &NSTextView.bracketMatcherKey, matcher, .OBJC_ASSOCIATION_RETAIN_NONATOMIC)
        return matcher
    }

    /// Highlight matching brackets at the current cursor position
    func highlightMatchingBrackets() {
        guard let textStorage = textStorage else { return }

        // Clear previous bracket highlights
        clearBracketHighlights()

        let cursorPosition = selectedRange().location
        // Use cached matcher to benefit from character array caching
        let matcher = cachedBracketMatcher

        guard let match = matcher.findMatchingBracket(in: string, at: cursorPosition) else {
            return
        }

        // Highlight both brackets
        textStorage.beginEditing()

        let highlightColor = BracketMatcher.matchHighlightColor

        // Validate ranges before applying
        if match.openRange.location + match.openRange.length <= textStorage.length {
            textStorage.addAttribute(.backgroundColor, value: highlightColor, range: match.openRange)
            textStorage.addAttribute(NSTextView.bracketHighlightKey, value: true, range: match.openRange)
        }

        if match.closeRange.location + match.closeRange.length <= textStorage.length {
            textStorage.addAttribute(.backgroundColor, value: highlightColor, range: match.closeRange)
            textStorage.addAttribute(NSTextView.bracketHighlightKey, value: true, range: match.closeRange)
        }

        textStorage.endEditing()
    }

    /// Clear any bracket highlight attributes
    func clearBracketHighlights() {
        guard let textStorage = textStorage else { return }

        let fullRange = NSRange(location: 0, length: textStorage.length)

        // Collect ranges first to avoid mutating during enumeration
        var rangesToClear: [NSRange] = []
        textStorage.enumerateAttribute(NSTextView.bracketHighlightKey, in: fullRange, options: []) { value, range, _ in
            if value != nil {
                rangesToClear.append(range)
            }
        }

        // Now remove attributes after enumeration completes
        guard !rangesToClear.isEmpty else { return }

        textStorage.beginEditing()
        for range in rangesToClear {
            textStorage.removeAttribute(.backgroundColor, range: range)
            textStorage.removeAttribute(NSTextView.bracketHighlightKey, range: range)
        }
        textStorage.endEditing()
    }
}
