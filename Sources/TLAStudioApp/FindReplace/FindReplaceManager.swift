import AppKit
import Combine

// MARK: - FindReplaceManager

/// Manages find and replace operations for the TLA+ editor.
///
/// This class handles all find/replace logic including:
/// - Text searching with case sensitivity, whole word, and regex options
/// - Match highlighting in the text view
/// - Navigation between matches
/// - Single and bulk replacement operations
/// - Search/replace history management
///
/// Usage:
/// ```swift
/// let manager = FindReplaceManager()
/// manager.textView = myTextView
/// manager.searchQuery = "example"
/// manager.findAll()
/// ```
@MainActor
public final class FindReplaceManager: ObservableObject {

    // MARK: - Published Properties

    /// Current search text.
    /// Updates trigger automatic match recalculation after a debounce period.
    @Published public var searchQuery: String = "" {
        didSet {
            if searchQuery != oldValue {
                scheduleSearch()
            }
        }
    }

    /// Replacement text for replace operations.
    @Published public var replaceQuery: String = ""

    /// Panel visibility state.
    @Published public var isVisible: Bool = false

    /// Whether the replace row is visible in the panel.
    @Published public var showReplace: Bool = false {
        didSet {
            if showReplace != oldValue {
                NotificationCenter.default.post(
                    name: .findReplacePanelHeightChanged,
                    object: self
                )
            }
        }
    }

    /// Whether to perform case-sensitive matching.
    /// When `true`, "Example" will not match "example".
    @Published public var isCaseSensitive: Bool = false {
        didSet {
            if isCaseSensitive != oldValue {
                performSearch()
            }
        }
    }

    /// Alias for isCaseSensitive to maintain compatibility with FindReplacePanel.
    public var matchCase: Bool {
        get { isCaseSensitive }
        set { isCaseSensitive = newValue }
    }

    /// Whether to match whole words only.
    /// When `true`, searching for "word" will not match "keyword".
    @Published public var isWholeWord: Bool = false {
        didSet {
            if isWholeWord != oldValue {
                performSearch()
            }
        }
    }

    /// Alias for isWholeWord to maintain compatibility with FindReplacePanel.
    public var wholeWord: Bool {
        get { isWholeWord }
        set { isWholeWord = newValue }
    }

    /// Whether to interpret the search query as a regular expression.
    @Published public var isRegex: Bool = false {
        didSet {
            if isRegex != oldValue {
                // Clear regex error when disabling regex mode
                if !isRegex {
                    regexError = nil
                }
                performSearch()
            }
        }
    }

    /// Alias for isRegex to maintain compatibility with FindReplacePanel.
    public var useRegex: Bool {
        get { isRegex }
        set { isRegex = newValue }
    }

    /// Current match index (0-based), nil if no matches.
    @Published public private(set) var currentMatchIndex: Int? = nil

    /// Total number of matches found.
    @Published public private(set) var totalMatches: Int = 0

    /// Alias for totalMatches to maintain compatibility with FindReplacePanel.
    public var matchCount: Int { totalMatches }

    /// Array of match ranges in the document.
    @Published public private(set) var matches: [NSRange] = []

    /// Status message describing the current state.
    /// Examples: "3 of 15 matches", "No matches", ""
    @Published public private(set) var statusMessage: String = ""

    /// Error message when regex pattern is invalid.
    /// Nil when pattern is valid or regex mode is disabled.
    @Published public private(set) var regexError: String? = nil

    /// Whether the current search has an error (invalid regex).
    public var hasError: Bool { regexError != nil }

    // MARK: - Properties

    /// Reference to the editor text view for highlighting and text operations.
    public weak var textView: NSTextView?

    /// Recent search queries (most recent first, max 10).
    public private(set) var recentSearches: [String] = []

    /// Recent replacement queries (most recent first, max 10).
    public private(set) var recentReplacements: [String] = []

    // MARK: - Callbacks

    /// Called when the panel should be closed.
    public var onClose: (() -> Void)?

    /// Called to get the current document text.
    /// If not set, uses textView.string.
    public var textProvider: (() -> String)?

    /// Called to replace text in a range.
    /// If not set, uses textView.textStorage.
    public var textReplacer: ((NSRange, String) -> Void)?

    /// Called to select and scroll to a range.
    /// If not set, uses textView.setSelectedRange and scrollRangeToVisible.
    public var selectionHandler: ((NSRange) -> Void)?

    // MARK: - Private Properties

    private let maxHistoryCount = 10
    private var searchDebounceTask: Task<Void, Never>?
    private let debounceInterval: Duration = .milliseconds(150)

    /// Attribute key for find highlight.
    private static let findHighlightKey = NSAttributedString.Key("TLAFindHighlight")

    /// Attribute key for current match highlight.
    private static let currentMatchHighlightKey = NSAttributedString.Key("TLACurrentMatchHighlight")

    // MARK: - Initialization

    public init() {}

    // MARK: - Panel Visibility

    /// Shows the find/replace panel and focuses the search field.
    public func show() {
        isVisible = true
    }

    /// Alias for show() to maintain compatibility.
    public func open() {
        show()
    }

    /// Hides the find/replace panel and clears highlights.
    public func hide() {
        isVisible = false
        clearHighlights()
    }

    /// Closes the find/replace panel and notifies observers.
    public func close() {
        hide()
        onClose?()
    }

    /// Toggles panel visibility.
    public func toggle() {
        if isVisible {
            hide()
        } else {
            show()
        }
    }

    // MARK: - Navigation

    /// Navigates to the next match, wrapping to the first if at the end.
    public func findNext() {
        guard totalMatches > 0 else { return }

        if let current = currentMatchIndex {
            currentMatchIndex = (current + 1) % totalMatches
        } else {
            currentMatchIndex = 0
        }

        highlightCurrentMatch()
        selectCurrentMatch()
        updateStatusMessage()
    }

    /// Navigates to the previous match, wrapping to the last if at the beginning.
    public func findPrevious() {
        guard totalMatches > 0 else { return }

        if let current = currentMatchIndex {
            currentMatchIndex = (current - 1 + totalMatches) % totalMatches
        } else {
            currentMatchIndex = totalMatches - 1
        }

        highlightCurrentMatch()
        selectCurrentMatch()
        updateStatusMessage()
    }

    /// Finds all matches and highlights them.
    /// Also adds the search query to history.
    public func findAll() {
        performSearch()
        addToSearchHistory(searchQuery)
    }

    // MARK: - Replace Operations

    /// Replaces the current match with the replacement text.
    public func replaceCurrent() {
        guard let index = currentMatchIndex,
              index < matches.count else {
            return
        }

        let range = matches[index]

        // Use custom replacer if provided
        if let replacer = textReplacer {
            replacer(range, replaceQuery)
        } else if let textView = textView,
                  let textStorage = textView.textStorage {
            // Verify the range is still valid
            guard range.location + range.length <= textStorage.length else {
                performSearch()
                return
            }

            textStorage.beginEditing()
            textStorage.replaceCharacters(in: range, with: replaceQuery)
            textStorage.endEditing()
        }

        // Add to replacement history
        addToReplacementHistory(replaceQuery)

        // Re-search after replacement
        performSearch()

        // Adjust current match index
        if totalMatches > 0 {
            currentMatchIndex = min(index, totalMatches - 1)
            selectCurrentMatch()
        } else {
            currentMatchIndex = nil
        }
    }

    /// Replaces the current match and advances to the next one.
    public func replaceAndFindNext() {
        replaceCurrent()
        if totalMatches > 0 {
            selectCurrentMatch()
        }
    }

    /// Replaces all matches with the replacement text.
    /// - Returns: The number of replacements made.
    @discardableResult
    public func replaceAll() -> Int {
        guard totalMatches > 0 else { return 0 }

        let replacementCount = matches.count

        // Replace from end to start to preserve range validity
        let sortedMatches = matches.sorted { $0.location > $1.location }

        if let replacer = textReplacer {
            for range in sortedMatches {
                replacer(range, replaceQuery)
            }
        } else if let textView = textView,
                  let textStorage = textView.textStorage {
            textStorage.beginEditing()
            for range in sortedMatches {
                guard range.location + range.length <= textStorage.length else {
                    continue
                }
                textStorage.replaceCharacters(in: range, with: replaceQuery)
            }
            textStorage.endEditing()
        }

        // Add to replacement history
        addToReplacementHistory(replaceQuery)

        // Re-search after replacement (will clear matches since text changed)
        performSearch()

        return replacementCount
    }

    // MARK: - Match Calculation

    /// Recalculates matches when the query or options change.
    /// Called automatically on property changes; can also be called manually.
    public func updateMatches() {
        performSearch()
    }

    /// Updates the current match index based on cursor position.
    /// - Parameter position: The cursor position in the document.
    public func updateCurrentMatch(forCursorPosition position: Int) {
        guard totalMatches > 0 else {
            currentMatchIndex = nil
            return
        }

        // Find the match that contains or is closest after the cursor
        for (index, range) in matches.enumerated() {
            if position <= range.location + range.length {
                currentMatchIndex = index
                return
            }
        }

        // If cursor is after all matches, wrap to first
        currentMatchIndex = 0
    }

    // MARK: - Private Methods - Search

    private func scheduleSearch() {
        searchDebounceTask?.cancel()

        searchDebounceTask = Task {
            try? await Task.sleep(for: debounceInterval)

            if !Task.isCancelled {
                performSearch()
            }
        }
    }

    private func performSearch() {
        let text: String
        if let provider = textProvider {
            text = provider()
        } else if let textView = textView {
            text = textView.string
        } else {
            matches = []
            totalMatches = 0
            currentMatchIndex = nil
            updateStatusMessage()
            return
        }

        guard !searchQuery.isEmpty else {
            matches = []
            totalMatches = 0
            currentMatchIndex = nil
            updateStatusMessage()
            clearHighlights()
            return
        }

        // Calculate new matches using regex for consistency
        do {
            let pattern = buildSearchPattern()
            var options: NSRegularExpression.Options = []

            if !isCaseSensitive {
                options.insert(.caseInsensitive)
            }

            let regex = try NSRegularExpression(pattern: pattern, options: options)
            let nsText = text as NSString
            let searchRange = NSRange(location: 0, length: nsText.length)

            let results = regex.matches(in: text, options: [], range: searchRange)
            matches = results.map { $0.range }
            totalMatches = matches.count

            // Clear any previous regex error
            regexError = nil

            // Adjust current match index
            if totalMatches == 0 {
                currentMatchIndex = nil
            } else if let current = currentMatchIndex {
                currentMatchIndex = min(current, totalMatches - 1)
            } else {
                currentMatchIndex = 0
            }
        } catch let error as NSError {
            // Invalid regex pattern - clear results and set error
            matches = []
            totalMatches = 0
            currentMatchIndex = nil

            // Only show regex error if regex mode is enabled
            if isRegex {
                // Extract a user-friendly error message
                let description = error.localizedDescription
                regexError = "Invalid regex: \(description)"
            } else {
                regexError = nil
            }
        }

        // Update highlights
        applyHighlights()
        updateStatusMessage()

        // Scroll to current match if there are matches
        if !matches.isEmpty {
            scrollToCurrentMatch()
        }
    }

    private func buildSearchPattern() -> String {
        var pattern: String

        if isRegex {
            pattern = searchQuery
        } else {
            // Escape special regex characters for literal search
            pattern = NSRegularExpression.escapedPattern(for: searchQuery)
        }

        if isWholeWord {
            pattern = "\\b\(pattern)\\b"
        }

        return pattern
    }

    // MARK: - Private Methods - Highlighting

    private func applyHighlights() {
        guard let textView = textView,
              let textStorage = textView.textStorage,
              let layoutManager = textView.layoutManager else {
            return
        }

        // Clear existing highlights first
        clearHighlights()

        guard !matches.isEmpty else { return }

        // Highlight color for all matches - subtle yellow background
        let allMatchColor = NSColor.findHighlightColor.withAlphaComponent(0.3)

        // Highlight color for current match - more prominent
        let currentMatchColor = NSColor.selectedTextBackgroundColor.withAlphaComponent(0.5)

        textStorage.beginEditing()

        // Apply highlight to all matches
        for (index, range) in matches.enumerated() {
            guard range.location + range.length <= textStorage.length else {
                continue
            }

            let highlightColor = (index == currentMatchIndex) ? currentMatchColor : allMatchColor
            textStorage.addAttribute(.backgroundColor, value: highlightColor, range: range)
            textStorage.addAttribute(Self.findHighlightKey, value: true, range: range)

            if index == currentMatchIndex {
                textStorage.addAttribute(Self.currentMatchHighlightKey, value: true, range: range)
            }
        }

        textStorage.endEditing()

        // Invalidate layout for highlighted ranges
        for range in matches {
            if range.location + range.length <= textStorage.length {
                layoutManager.invalidateDisplay(forCharacterRange: range)
            }
        }
    }

    private func highlightCurrentMatch() {
        // Reapply all highlights with updated current match
        applyHighlights()
    }

    private func clearHighlights() {
        guard let textView = textView,
              let textStorage = textView.textStorage else {
            return
        }

        guard textStorage.length > 0 else { return }

        let fullRange = NSRange(location: 0, length: textStorage.length)

        textStorage.beginEditing()

        // Remove our custom highlight attributes
        textStorage.enumerateAttribute(Self.findHighlightKey, in: fullRange, options: []) { value, range, _ in
            if value != nil {
                textStorage.removeAttribute(.backgroundColor, range: range)
                textStorage.removeAttribute(Self.findHighlightKey, range: range)
                textStorage.removeAttribute(Self.currentMatchHighlightKey, range: range)
            }
        }

        textStorage.endEditing()
    }

    private func scrollToCurrentMatch() {
        guard let index = currentMatchIndex,
              index < matches.count,
              let textView = textView else {
            return
        }

        let currentRange = matches[index]
        textView.scrollRangeToVisible(currentRange)
        textView.showFindIndicator(for: currentRange)
    }

    private func selectCurrentMatch() {
        guard let index = currentMatchIndex,
              index < matches.count else {
            return
        }

        let range = matches[index]

        if let handler = selectionHandler {
            handler(range)
        } else if let textView = textView {
            textView.setSelectedRange(range)
            textView.scrollRangeToVisible(range)
        }
    }

    // MARK: - Private Methods - Status

    private func updateStatusMessage() {
        if searchQuery.isEmpty {
            statusMessage = ""
        } else if let error = regexError {
            statusMessage = error
        } else if matches.isEmpty {
            statusMessage = "No matches"
        } else if matches.count == 1 {
            statusMessage = "1 match"
        } else if let index = currentMatchIndex {
            statusMessage = "\(index + 1) of \(matches.count) matches"
        } else {
            statusMessage = "\(matches.count) matches"
        }
    }

    // MARK: - Private Methods - History

    private func addToSearchHistory(_ query: String) {
        guard !query.isEmpty else { return }

        // Remove if already exists to move to front
        recentSearches.removeAll { $0 == query }

        // Insert at front
        recentSearches.insert(query, at: 0)

        // Trim to max count
        if recentSearches.count > maxHistoryCount {
            recentSearches = Array(recentSearches.prefix(maxHistoryCount))
        }
    }

    private func addToReplacementHistory(_ replacement: String) {
        guard !replacement.isEmpty else { return }

        // Remove if already exists to move to front
        recentReplacements.removeAll { $0 == replacement }

        // Insert at front
        recentReplacements.insert(replacement, at: 0)

        // Trim to max count
        if recentReplacements.count > maxHistoryCount {
            recentReplacements = Array(recentReplacements.prefix(maxHistoryCount))
        }
    }
}
