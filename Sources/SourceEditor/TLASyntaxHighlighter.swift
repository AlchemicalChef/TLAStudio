import AppKit
import Combine

// MARK: - Pre-compiled Syntax Patterns

/// Pre-compiled regex patterns for TLA+ syntax highlighting.
/// Compiled once at load time to avoid per-keystroke compilation overhead.
private enum SyntaxPatterns {

    // MARK: - Keywords (combined into single alternation for efficiency)

    /// All TLA+ keywords combined into a single alternation pattern
    static let keywords: NSRegularExpression = {
        let keywordList = [
            "EXTENDS", "LOCAL", "INSTANCE", "WITH", "RECURSIVE",
            "VARIABLE", "VARIABLES", "CONSTANT", "CONSTANTS",
            "ASSUME", "ASSUMPTION", "AXIOM", "THEOREM", "LEMMA", "COROLLARY", "PROPOSITION",
            "PROOF", "BY", "DEF", "DEFS", "OBVIOUS", "OMITTED", "QED",
            "PICK", "HAVE", "TAKE", "WITNESS", "SUFFICES", "USE", "HIDE", "DEFINE",
            "NEW", "STATE", "ACTION", "TEMPORAL",
            "IF", "THEN", "ELSE", "CASE", "OTHER", "LET", "IN",
            "CHOOSE", "EXCEPT", "DOMAIN", "SUBSET", "UNION",
            "ENABLED", "UNCHANGED", "WF_", "SF_",
            "TRUE", "FALSE", "BOOLEAN"
        ]
        let pattern = "\\b(" + keywordList.joined(separator: "|") + ")(_)?\\b"
        return try! NSRegularExpression(pattern: pattern)
    }()

    /// Standard module names
    static let standardModules: NSRegularExpression = {
        let modules = ["Naturals", "Integers", "Reals", "Sequences", "FiniteSets",
                       "Bags", "TLC", "TLAPS", "ProofRules"]
        let pattern = "\\b(" + modules.joined(separator: "|") + ")\\b"
        return try! NSRegularExpression(pattern: pattern)
    }()

    // MARK: - Comments

    /// Line comments: \* ... end of line
    static let lineComment = try! NSRegularExpression(
        pattern: "\\\\\\*.*$",
        options: .anchorsMatchLines
    )

    /// Block comments: (* ... *)
    static let blockComment = try! NSRegularExpression(
        pattern: "\\(\\*[\\s\\S]*?\\*\\)"
    )

    // MARK: - Literals

    /// String literals: "..."
    static let stringLiteral = try! NSRegularExpression(
        pattern: "\"[^\"]*\""
    )

    /// Number literals
    static let numberLiteral = try! NSRegularExpression(
        pattern: "\\b\\d+\\b"
    )

    // MARK: - Operators (combined into single alternation)

    /// TLA+ backslash operators
    static let tlaOperators: NSRegularExpression = {
        let ops = [
            "\\\\in", "\\\\notin", "\\\\subseteq", "\\\\subset",
            "\\\\cup", "\\\\cap", "\\\\union", "\\\\intersect",
            "\\\\E", "\\\\A", "\\\\EE", "\\\\AA",
            "\\\\lnot", "\\\\lor", "\\\\land", "\\\\neg",
            "\\\\implies", "\\\\equiv", "\\\\leadsto",
            "\\\\X", "\\\\o", "\\\\circ", "\\\\div",
            "\\\\times", "\\\\oplus", "\\\\ominus", "\\\\otimes",
            "\\\\prec", "\\\\succ", "\\\\preceq", "\\\\succeq",
            "\\\\ll", "\\\\gg", "\\\\sim", "\\\\simeq",
            "\\\\asymp", "\\\\approx", "\\\\cong", "\\\\doteq"
        ]
        let pattern = "(" + ops.joined(separator: "|") + ")"
        return try! NSRegularExpression(pattern: pattern)
    }()

    /// ASCII operators
    static let asciiOperators: NSRegularExpression = {
        let ops = [
            "/\\\\", "\\\\/", "~", "=>", "<=>", "->", "<-", ":=",
            "(?<!=)==(?!=)", "#", "/=", "<=", ">=", "<<", ">>", "\\|->",
            "\\[\\]", "<>", "-\\+->", "\\|\\|", "@@"
        ]
        let pattern = "(" + ops.joined(separator: "|") + ")"
        return try! NSRegularExpression(pattern: pattern)
    }()

    // MARK: - Structure

    /// Module header: ---- MODULE Name ----
    static let moduleHeader = try! NSRegularExpression(
        pattern: "^-{4,}\\s+MODULE\\s+\\w+\\s+-{4,}$",
        options: .anchorsMatchLines
    )

    /// Module footer: ====
    static let moduleFooter = try! NSRegularExpression(
        pattern: "^={4,}\\s*$",
        options: .anchorsMatchLines
    )

    /// Prime operator for state variables: var'
    static let primeOperator = try! NSRegularExpression(
        pattern: "\\w+'"
    )
}

// MARK: - TLASyntaxHighlighter

/// Manages syntax highlighting for TLASourceEditor
/// Bridges the TLACore parser with the editor's highlighting system
public final class TLASyntaxHighlighter {

    // MARK: - Configuration

    public var theme: SyntaxTheme = .default {
        didSet {
            scheduleHighlighting()
        }
    }

    public var debounceInterval: TimeInterval = 0.016  // ~1 frame at 60fps for responsive highlighting

    // MARK: - State

    private weak var editor: TLASourceEditor?
    private weak var textView: NSTextView?
    private var debounceWorkItem: DispatchWorkItem?
    private var isHighlighting = false
    private var pendingHighlight = false
    private var lastHighlightedText: String = ""
    private var needsFullReset = true

    /// Threshold for switching to visible-range-only highlighting.
    /// For documents larger than this (in characters), only the visible range is highlighted.
    /// This provides 10-100x speedup for large files.
    private static let visibleRangeHighlightingThreshold = 50_000  // ~1000 lines

    /// Track last highlighted visible range to avoid redundant work
    private var lastHighlightedVisibleRange: NSRange = NSRange(location: 0, length: 0)
    /// Track content hash of the last highlighted range to detect text changes
    private var lastHighlightedContentHash: Int = 0

    /// Pre-sorted tree-sitter tokens plus the longest token length, supplied by
    /// the provider so the highlighter can binary-search the visible slice on
    /// scroll instead of scanning the whole document's token array each frame.
    public struct TreeSitterTokens {
        /// Tokens (range, captureName) sorted ascending by `range.location`.
        public let tokens: [(NSRange, String)]
        /// Longest `range.length` among `tokens` (0 when empty). Bounds the lower
        /// edge of the binary search so a long token (e.g. a block comment) that
        /// starts before the visible window is still found.
        public let maxTokenLength: Int

        public init(tokens: [(NSRange, String)], maxTokenLength: Int) {
            self.tokens = tokens
            self.maxTokenLength = maxTokenLength
        }
    }

    /// Optional closure that provides tree-sitter highlight tokens (sorted by
    /// location). Called with the source text; returns nil when no tokens are
    /// available for that text. When set, tree-sitter highlighting is preferred
    /// over regex.
    public var treeSitterHighlightProvider: ((String) -> TreeSitterTokens?)?

    // Highlight token to color mapping (covers both regex and tree-sitter capture names)
    private let tokenColorMap: [String: KeyPath<SyntaxTheme, NSColor>] = [
        "keyword": \.keyword,
        "keyword.control": \.keyword,
        "keyword.operator": \.operator_,
        "operator": \.operator_,
        "string": \.string,
        "string.special": \.string,
        "comment": \.comment,
        "comment.line": \.comment,
        "comment.block": \.comment,
        "number": \.number,
        "constant.numeric": \.number,
        "constant": \.number,
        "type": \.type,
        "type.builtin": \.type,
        "module": \.type,
        "variable": \.identifier,
        "variable.parameter": \.identifier,
        "variable.builtin": \.keyword,
        "variable.reference": \.identifier,
        "attribute": \.identifier,
        "tag": \.string,
        "function": \.identifier,
        "function.method": \.identifier,
        "function.builtin": \.operator_,
        "punctuation": \.identifier,
        "punctuation.bracket": \.identifier,
        "punctuation.delimiter": \.identifier,
    ]

    // MARK: - Initialization

    public init(editor: TLASourceEditor) {
        self.editor = editor
        self.textView = editor
    }

    /// Initialize with any NSTextView
    public init(textView: NSTextView, theme: SyntaxTheme = .default) {
        self.textView = textView
        self.theme = theme
    }

    // MARK: - Highlighting

    /// Schedule highlighting with debouncing
    public func scheduleHighlighting() {
        debounceWorkItem?.cancel()

        let workItem = DispatchWorkItem { [weak self] in
            self?.performHighlighting()
        }

        debounceWorkItem = workItem
        DispatchQueue.main.asyncAfter(deadline: .now() + debounceInterval, execute: workItem)
    }

    /// Perform immediate highlighting without debouncing
    public func highlightImmediately() {
        debounceWorkItem?.cancel()
        needsFullReset = true
        // The large-file visible-range path gates on its own range/hash cache and
        // does NOT consult needsFullReset, so a forced re-highlight whose text and
        // viewport are unchanged (theme switch, fold/unfold-all) would early-return
        // and leave the viewport in the old colors. Reset that cache too, mirroring
        // scrollPositionChanged().
        lastHighlightedVisibleRange = NSRange(location: 0, length: 0)
        lastHighlightedContentHash = 0
        performHighlighting()
    }

    private func performHighlighting() {
        guard let textView = textView else { return }

        // Skip if text hasn't changed
        let currentText = textView.string
        if currentText == lastHighlightedText && !needsFullReset {
            return
        }

        // Prevent re-entrant highlighting
        if isHighlighting {
            pendingHighlight = true
            return
        }

        isHighlighting = true
        lastHighlightedText = currentText
        needsFullReset = false

        // Apply highlights directly to text storage
        guard let textStorage = textView.textStorage else {
            isHighlighting = false
            return
        }
        guard textStorage.length > 0 else {
            isHighlighting = false
            return
        }

        // Preserve selection
        let selectedRanges = textView.selectedRanges

        // PERFORMANCE OPTIMIZATION: For large files, only highlight visible range + buffer
        // This provides 10-100x speedup for files with 1000+ lines
        if textStorage.length > Self.visibleRangeHighlightingThreshold {
            performVisibleRangeHighlighting(textView: textView, textStorage: textStorage, currentText: currentText)
        } else {
            // Small file: highlight everything
            performFullHighlighting(textView: textView, textStorage: textStorage, currentText: currentText)
        }

        // Restore selection
        textView.selectedRanges = selectedRanges

        isHighlighting = false

        // Handle pending highlight request
        if pendingHighlight {
            pendingHighlight = false
            DispatchQueue.main.async { [weak self] in
                self?.performHighlighting()
            }
        }
    }

    /// Highlight only the visible range plus a buffer (for large files)
    private func performVisibleRangeHighlighting(textView: NSTextView, textStorage: NSTextStorage, currentText: String) {
        let nsText = currentText as NSString

        // Get visible range from scroll view
        guard let scrollView = textView.enclosingScrollView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else {
            // Fallback to full highlighting if we can't get visible range
            performFullHighlighting(textView: textView, textStorage: textStorage, currentText: currentText)
            return
        }

        let visibleRect = scrollView.documentVisibleRect
        let glyphRange = layoutManager.glyphRange(forBoundingRect: visibleRect, in: textContainer)
        let visibleCharRange = layoutManager.characterRange(forGlyphRange: glyphRange, actualGlyphRange: nil)

        // Add buffer of ~500 characters before and after visible range
        let bufferSize = 500
        let expandedStart = max(0, visibleCharRange.location - bufferSize)
        let expandedEnd = min(nsText.length, NSMaxRange(visibleCharRange) + bufferSize)

        // Expand to complete lines for proper syntax highlighting
        var lineStart = expandedStart
        while lineStart > 0 && nsText.character(at: lineStart - 1) != 0x0A {
            lineStart -= 1
        }
        var lineEnd = expandedEnd
        while lineEnd < nsText.length && nsText.character(at: lineEnd) != 0x0A {
            lineEnd += 1
        }

        let highlightRange = NSRange(location: lineStart, length: lineEnd - lineStart)

        // Extract text for the range to highlight
        let rangeText = nsText.substring(with: highlightRange)

        // Compute content hash to detect text changes within the same range
        let contentHash = rangeText.hashValue

        // Skip if we already highlighted this exact range with the same content
        if highlightRange == lastHighlightedVisibleRange && contentHash == lastHighlightedContentHash {
            return
        }
        lastHighlightedVisibleRange = highlightRange
        lastHighlightedContentHash = contentHash

        // Get highlights for this range. Tree-sitter providers operate on the full
        // source so cached absolute ranges can be reused for visible highlighting.
        let highlights = highlightWithTreeSitter(currentText, restrictingTo: highlightRange) ?? {
            let regexHighlights = highlightWithRegex(rangeText)
            return regexHighlights.map { highlight in
                HighlightRange(
                    range: NSRange(
                        location: highlight.range.location + highlightRange.location,
                        length: highlight.range.length
                    ),
                    color: highlight.color,
                    style: highlight.style
                )
            }
        }()

        // Apply highlights
        textStorage.beginEditing()

        // Only reset colors in the range we're highlighting
        textStorage.addAttribute(.foregroundColor, value: NSColor.textColor, range: highlightRange)

        for highlight in highlights {
            guard highlight.range.location >= 0,
                  highlight.range.location + highlight.range.length <= textStorage.length else {
                continue
            }
            textStorage.addAttribute(.foregroundColor, value: highlight.color, range: highlight.range)
        }

        textStorage.endEditing()
    }

    /// Highlight the entire document (for small files)
    private func performFullHighlighting(textView: NSTextView, textStorage: NSTextStorage, currentText: String) {
        let highlights = highlightWithTreeSitter(currentText) ?? highlightWithRegex(currentText)
        let fullRange = NSRange(location: 0, length: textStorage.length)

        textStorage.beginEditing()

        // Reset foreground color only - DO NOT touch fonts at all
        textStorage.addAttribute(.foregroundColor, value: NSColor.textColor, range: fullRange)

        // Apply highlight colors only - no font changes
        for highlight in highlights {
            guard highlight.range.location >= 0,
                  highlight.range.location + highlight.range.length <= textStorage.length else {
                continue
            }
            textStorage.addAttribute(.foregroundColor, value: highlight.color, range: highlight.range)
        }

        textStorage.endEditing()
    }

    // MARK: - Tree-Sitter Highlighting

    /// Attempt to highlight using tree-sitter tokens from the provider.
    /// Returns nil if no provider is set or it returns empty results.
    private func highlightWithTreeSitter(_ text: String, restrictingTo visibleRange: NSRange? = nil) -> [HighlightRange]? {
        guard let provider = treeSitterHighlightProvider else { return nil }
        guard let bundle = provider(text), !bundle.tokens.isEmpty else { return nil }
        let tokens = bundle.tokens

        var highlights: [HighlightRange] = []

        if let visibleRange {
            // Large-file scroll/keystroke path: the token array is whole-document
            // and sorted by location, so only a small window can intersect the
            // viewport. Binary-search that slice instead of scanning every token.
            let slice = Self.visibleTokenIndexRange(
                in: tokens,
                visibleRange: visibleRange,
                maxTokenLength: bundle.maxTokenLength
            )
            for index in slice {
                let (range, captureName) = tokens[index]
                guard let colorKeyPath = tokenColorMap[captureName] else { continue }
                let intersection = NSIntersectionRange(range, visibleRange)
                guard intersection.length > 0 else { continue }
                let color = theme[keyPath: colorKeyPath]
                let style: HighlightRange.Style = captureName.hasPrefix("keyword") ? .bold : .plain
                highlights.append(HighlightRange(range: intersection, color: color, style: style))
            }
        } else {
            // Small-file full-highlight path: apply every token.
            for (range, captureName) in tokens {
                guard let colorKeyPath = tokenColorMap[captureName] else { continue }
                let color = theme[keyPath: colorKeyPath]
                let style: HighlightRange.Style = captureName.hasPrefix("keyword") ? .bold : .plain
                highlights.append(HighlightRange(range: range, color: color, style: style))
            }
        }

        return highlights.isEmpty ? nil : highlights
    }

    /// The half-open index range `[lo, hi)` into `tokens` (which MUST be sorted
    /// ascending by `range.location`) whose entries can possibly intersect
    /// `visibleRange`, given `maxTokenLength` = the longest token length in the
    /// array. A token starting before `visibleRange.location - maxTokenLength`
    /// provably ends before the window; one starting at/after the window's end
    /// provably starts after it — so only this slice need be examined. Callers
    /// still intersection-test each entry in the slice. Exposed for unit testing.
    static func visibleTokenIndexRange(
        in tokens: [(NSRange, String)],
        visibleRange: NSRange,
        maxTokenLength: Int
    ) -> Range<Int> {
        guard !tokens.isEmpty else { return 0..<0 }
        let lowerLocation = max(0, visibleRange.location - max(0, maxTokenLength))
        let visibleEnd = NSMaxRange(visibleRange)
        let lo = firstTokenIndex(in: tokens, withLocationAtLeast: lowerLocation)
        let hi = firstTokenIndex(in: tokens, withLocationAtLeast: visibleEnd)
        return lo..<max(lo, hi)
    }

    /// First index whose token `range.location` is >= `target` (lower_bound),
    /// or `tokens.count` if none. `tokens` MUST be sorted by `range.location`.
    private static func firstTokenIndex(
        in tokens: [(NSRange, String)],
        withLocationAtLeast target: Int
    ) -> Int {
        var low = 0
        var high = tokens.count
        while low < high {
            let mid = (low + high) / 2
            if tokens[mid].0.location < target {
                low = mid + 1
            } else {
                high = mid
            }
        }
        return low
    }

    // MARK: - Regex-Based Highlighting

    private func highlightWithRegex(_ text: String) -> [HighlightRange] {
        var highlights: [HighlightRange] = []
        let nsText = text as NSString
        let fullRange = NSRange(location: 0, length: nsText.length)

        // Use pre-compiled patterns for all highlighting

        // Keywords (single combined pattern instead of 40+ individual patterns)
        for match in SyntaxPatterns.keywords.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.keyword, style: .bold))
        }

        // Standard modules (single combined pattern)
        for match in SyntaxPatterns.standardModules.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.type, style: .plain))
        }

        // Line comments (\* ... end of line)
        for match in SyntaxPatterns.lineComment.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.comment, style: .plain))
        }

        // Block comments (* ... *)
        for match in SyntaxPatterns.blockComment.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.comment, style: .plain))
        }

        // Strings
        for match in SyntaxPatterns.stringLiteral.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.string, style: .plain))
        }

        // Numbers
        for match in SyntaxPatterns.numberLiteral.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.number, style: .plain))
        }

        // TLA+ operators (single combined pattern instead of 30+ individual patterns)
        for match in SyntaxPatterns.tlaOperators.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.operator_, style: .plain))
        }

        // ASCII operators (single combined pattern)
        for match in SyntaxPatterns.asciiOperators.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.operator_, style: .plain))
        }

        // Module header
        for match in SyntaxPatterns.moduleHeader.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.keyword, style: .bold))
        }

        // Module footer
        for match in SyntaxPatterns.moduleFooter.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.keyword, style: .bold))
        }

        // Prime operator (state variable updates)
        for match in SyntaxPatterns.primeOperator.matches(in: text, range: fullRange) {
            highlights.append(HighlightRange(range: match.range, color: theme.identifier, style: .plain))
        }

        return sortAndDeduplicateHighlights(highlights)
    }

    /// Sort highlights and handle overlaps (later items override earlier ones)
    private func sortAndDeduplicateHighlights(_ highlights: [HighlightRange]) -> [HighlightRange] {
        // Sort by location
        let sorted = highlights.sorted { $0.range.location < $1.range.location }

        // For simplicity, just return sorted list
        // The editor will apply them in order, with later ones overriding
        return sorted
    }

    // MARK: - Theme Updates

    /// Update highlighting when theme changes
    public func applyTheme(_ theme: SyntaxTheme) {
        self.theme = theme
        highlightImmediately()
    }
}

// MARK: - Async Highlighting Support

extension TLASyntaxHighlighter {

    /// Highlight using async TLACore (when available)
    @available(macOS 10.15, *)
    @MainActor
    public func highlightAsync(using core: Any) async {
        guard let editor = editor else { return }

        // Capture text on main actor
        let text = editor.text

        // This method will be implemented when TLACore bindings are available
        // For now, fall back to regex-based highlighting
        let highlights = highlightWithRegex(text)
        editor.setHighlights(highlights)
    }
}

// MARK: - Incremental Highlighting

extension TLASyntaxHighlighter {

    /// Called when the scroll position changes - triggers visible-range highlighting for large files
    public func scrollPositionChanged() {
        // Use NSString.length (O(1) UTF-16 units) rather than String.count (O(N) graphemes).
        // The threshold semantics are NSRange-compatible. See audit F-S6-editor-perf-002.
        guard let textView = textView else { return }
        let length = textView.textStorage?.length ?? (textView.string as NSString).length
        guard length > Self.visibleRangeHighlightingThreshold else {
            return
        }
        // Reset the cached visible range and content hash to force re-highlighting
        lastHighlightedVisibleRange = NSRange(location: 0, length: 0)
        lastHighlightedContentHash = 0
        needsFullReset = true
        scheduleHighlighting()
    }

    /// Perform incremental highlighting for the visible range only
    /// More efficient for large files
    public func highlightVisibleRange(in visibleRange: NSRange) {
        guard let editor = editor else { return }

        let text = editor.text
        let nsText = text as NSString

        // Expand range to include complete lines
        var expandedRange = visibleRange

        // Find line start
        var lineStart = expandedRange.location
        while lineStart > 0 && nsText.character(at: lineStart - 1) != 0x0A {
            lineStart -= 1
        }

        // Find line end
        var lineEnd = NSMaxRange(expandedRange)
        while lineEnd < nsText.length && nsText.character(at: lineEnd) != 0x0A {
            lineEnd += 1
        }

        expandedRange = NSRange(location: lineStart, length: lineEnd - lineStart)

        // Only highlight the expanded range
        let rangeText = nsText.substring(with: expandedRange)
        var highlights = highlightWithRegex(rangeText)

        // Adjust ranges to absolute positions
        highlights = highlights.map { highlight in
            HighlightRange(
                range: NSRange(
                    location: highlight.range.location + expandedRange.location,
                    length: highlight.range.length
                ),
                color: highlight.color,
                style: highlight.style
            )
        }

        editor.setHighlights(highlights)
    }
}
