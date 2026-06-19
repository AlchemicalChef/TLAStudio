import XCTest
@testable import TLAStudioApp

// MARK: - FindReplaceManager Tests

/// Tests for FindReplaceManager search logic, pattern building, history management,
/// and status message generation.
@MainActor
final class FindReplaceManagerTests: XCTestCase {

    var manager: FindReplaceManager!
    var testContent: String!

    override func setUp() async throws {
        try await super.setUp()
        testContent = """
        ---- MODULE Test ----
        VARIABLE x, y
        Init == x = 0 /\\ y = TRUE
        Next == x' = x + 1 /\\ y' = ~y
        Spec == Init /\\ [][Next]_<<x, y>>
        ====
        """
        manager = makeManager()
    }

    override func tearDown() async throws {
        manager = nil
        testContent = nil
        try await super.tearDown()
    }

    private func makeManager(
        debounceInterval: Duration = .zero,
        contentProvider: (() -> String)? = nil
    ) -> FindReplaceManager {
        let manager = FindReplaceManager(debounceInterval: debounceInterval)
        manager.textProvider = contentProvider ?? { [weak self] in
            self?.testContent ?? ""
        }
        return manager
    }

    // MARK: - Basic Search Tests

    func testSearchQueryUpdatesMatches() async throws {
        manager.searchQuery = "x"

        XCTAssertGreaterThan(manager.totalMatches, 0)
        XCTAssertFalse(manager.matches.isEmpty)
    }

    func testEmptySearchQuery() async throws {
        manager.searchQuery = ""

        XCTAssertEqual(manager.totalMatches, 0)
        XCTAssertTrue(manager.matches.isEmpty)
        XCTAssertNil(manager.currentMatchIndex)
    }

    func testNoMatchesFound() async throws {
        manager.searchQuery = "NonExistentTerm12345"

        XCTAssertEqual(manager.totalMatches, 0)
        XCTAssertTrue(manager.matches.isEmpty)
        XCTAssertEqual(manager.statusMessage, "No matches")
    }

    func testSearchFindsAllOccurrences() async throws {
        manager.searchQuery = "x"

        // "x" appears multiple times in our test content
        // VARIABLE x, Init == x = 0, Next == x' = x + 1, <<x, y>>
        XCTAssertGreaterThan(manager.totalMatches, 3)
    }

    // MARK: - Case Sensitivity Tests

    func testCaseInsensitiveSearch() async throws {
        testContent = "Hello hello HELLO"
        manager.isCaseSensitive = false
        manager.searchQuery = "hello"

        XCTAssertEqual(manager.totalMatches, 3)
    }

    func testCaseSensitiveSearch() async throws {
        testContent = "Hello hello HELLO"
        manager.isCaseSensitive = true
        manager.searchQuery = "hello"

        XCTAssertEqual(manager.totalMatches, 1)
    }

    func testMatchCaseAlias() {
        manager.matchCase = true
        XCTAssertTrue(manager.isCaseSensitive)

        manager.matchCase = false
        XCTAssertFalse(manager.isCaseSensitive)
    }

    // MARK: - Whole Word Tests

    func testWholeWordSearch() async throws {
        testContent = "test testing tested contest"
        manager.isWholeWord = true
        manager.searchQuery = "test"

        // Should only match standalone "test", not "testing", "tested", or "contest"
        XCTAssertEqual(manager.totalMatches, 1)
    }

    func testWholeWordSearchDisabled() async throws {
        testContent = "test testing tested contest"
        manager.isWholeWord = false
        manager.searchQuery = "test"

        // Should match all occurrences containing "test"
        XCTAssertEqual(manager.totalMatches, 4)
    }

    func testWholeWordAlias() {
        manager.wholeWord = true
        XCTAssertTrue(manager.isWholeWord)

        manager.wholeWord = false
        XCTAssertFalse(manager.isWholeWord)
    }

    // MARK: - Regex Search Tests

    func testRegexSearch() async throws {
        testContent = "foo1 foo2 foo3 bar1 bar2"
        manager.isRegex = true
        manager.searchQuery = "foo\\d"

        XCTAssertEqual(manager.totalMatches, 3)
    }

    func testRegexSearchWithGroups() async throws {
        testContent = "cat bat rat mat"
        manager.isRegex = true
        manager.searchQuery = "[cbr]at"

        XCTAssertEqual(manager.totalMatches, 3)
    }

    func testInvalidRegexShowsError() async throws {
        manager.isRegex = true
        manager.searchQuery = "[invalid("

        XCTAssertNotNil(manager.regexError)
        XCTAssertTrue(manager.hasError)
        XCTAssertEqual(manager.totalMatches, 0)
    }

    func testValidRegexClearsError() async throws {
        // First set invalid regex
        manager.isRegex = true
        manager.searchQuery = "[invalid("
        XCTAssertNotNil(manager.regexError)

        // Then set valid regex
        manager.searchQuery = "valid"

        XCTAssertNil(manager.regexError)
        XCTAssertFalse(manager.hasError)
    }

    func testDisablingRegexClearsError() async throws {
        manager.isRegex = true
        manager.searchQuery = "[invalid("
        XCTAssertNotNil(manager.regexError)

        manager.isRegex = false
        XCTAssertNil(manager.regexError)
    }

    func testUseRegexAlias() {
        manager.useRegex = true
        XCTAssertTrue(manager.isRegex)

        manager.useRegex = false
        XCTAssertFalse(manager.isRegex)
    }

    // MARK: - Navigation Tests

    func testFindNext() async throws {
        manager.searchQuery = "x"

        let initialIndex = manager.currentMatchIndex ?? 0
        manager.findNext()

        XCTAssertEqual(manager.currentMatchIndex, initialIndex + 1)
    }

    func testFindNextWraps() async throws {
        testContent = "a a"
        manager.searchQuery = "a"

        XCTAssertEqual(manager.totalMatches, 2)

        // Verify starting at index 0
        XCTAssertEqual(manager.currentMatchIndex, 0)
        manager.findNext()
        XCTAssertEqual(manager.currentMatchIndex, 1)

        manager.findNext()
        XCTAssertEqual(manager.currentMatchIndex, 0) // Wraps to first
    }

    func testFindPrevious() async throws {
        testContent = "a a a"
        manager.searchQuery = "a"

        manager.findNext() // Go to index 1
        manager.findPrevious()

        XCTAssertEqual(manager.currentMatchIndex, 0)
    }

    func testFindPreviousWraps() async throws {
        testContent = "a a"
        manager.searchQuery = "a"

        // Start at index 0
        XCTAssertEqual(manager.currentMatchIndex, 0)

        manager.findPrevious()
        XCTAssertEqual(manager.currentMatchIndex, 1) // Wraps to last
    }

    func testFindNextWithNoMatches() async throws {
        manager.searchQuery = "NonExistent"

        let indexBefore = manager.currentMatchIndex
        manager.findNext()
        XCTAssertEqual(manager.currentMatchIndex, indexBefore)
    }

    func testFindPreviousWithNoMatches() async throws {
        manager.searchQuery = "NonExistent"

        let indexBefore = manager.currentMatchIndex
        manager.findPrevious()
        XCTAssertEqual(manager.currentMatchIndex, indexBefore)
    }

    // MARK: - Status Message Tests

    func testStatusMessageEmpty() async throws {
        manager.searchQuery = ""

        XCTAssertEqual(manager.statusMessage, "")
    }

    func testStatusMessageNoMatches() async throws {
        manager.searchQuery = "NonExistent"

        XCTAssertEqual(manager.statusMessage, "No matches")
    }

    func testStatusMessageSingleMatch() async throws {
        testContent = "unique"
        manager.searchQuery = "unique"

        XCTAssertEqual(manager.statusMessage, "1 match")
    }

    func testStatusMessageMultipleMatches() async throws {
        testContent = "a a a"
        manager.searchQuery = "a"

        // Should show "1 of 3 matches" since currentMatchIndex is set
        XCTAssertTrue(manager.statusMessage.contains("of 3 matches"))
    }

    func testStatusMessageWithRegexError() async throws {
        manager.isRegex = true
        manager.searchQuery = "[invalid("

        XCTAssertTrue(manager.statusMessage.contains("Invalid regex"))
    }

    // MARK: - History Tests

    func testSearchHistoryEmpty() {
        XCTAssertTrue(manager.recentSearches.isEmpty)
    }

    func testSearchHistoryAdded() async throws {
        manager.searchQuery = "test"
        manager.findAll()

        XCTAssertTrue(manager.recentSearches.contains("test"))
    }

    func testSearchHistoryMostRecentFirst() async throws {
        manager.searchQuery = "first"
        manager.findAll()

        manager.searchQuery = "second"
        manager.findAll()

        XCTAssertEqual(manager.recentSearches.first, "second")
        XCTAssertTrue(manager.recentSearches.contains("first"))
    }

    func testSearchHistoryNoDuplicates() async throws {
        manager.searchQuery = "test"
        manager.findAll()

        manager.searchQuery = "other"
        manager.findAll()

        manager.searchQuery = "test"
        manager.findAll()

        let testOccurrences = manager.recentSearches.filter { $0 == "test" }.count
        XCTAssertEqual(testOccurrences, 1)
        XCTAssertEqual(manager.recentSearches.first, "test") // Moved to front
    }

    func testSearchHistoryEmptyQueryNotAdded() async throws {
        manager.searchQuery = ""
        manager.findAll()

        XCTAssertTrue(manager.recentSearches.isEmpty)
    }

    func testReplacementHistoryEmpty() {
        XCTAssertTrue(manager.recentReplacements.isEmpty)
    }

    // MARK: - Panel Visibility Tests

    func testShowPanel() {
        XCTAssertFalse(manager.isVisible)

        manager.show()
        XCTAssertTrue(manager.isVisible)
    }

    func testOpenAlias() {
        XCTAssertFalse(manager.isVisible)

        manager.open()
        XCTAssertTrue(manager.isVisible)
    }

    func testHidePanel() {
        manager.show()
        XCTAssertTrue(manager.isVisible)

        manager.hide()
        XCTAssertFalse(manager.isVisible)
    }

    func testTogglePanel() {
        XCTAssertFalse(manager.isVisible)

        manager.toggle()
        XCTAssertTrue(manager.isVisible)

        manager.toggle()
        XCTAssertFalse(manager.isVisible)
    }

    func testClosePanel() {
        var closeCalled = false
        manager.onClose = { closeCalled = true }

        manager.show()
        manager.close()

        XCTAssertFalse(manager.isVisible)
        XCTAssertTrue(closeCalled)
    }

    // MARK: - Replace Row Visibility Tests

    func testShowReplaceDefault() {
        XCTAssertFalse(manager.showReplace)
    }

    func testShowReplaceToggle() {
        manager.showReplace = true
        XCTAssertTrue(manager.showReplace)

        manager.showReplace = false
        XCTAssertFalse(manager.showReplace)
    }

    // MARK: - Match Count Alias Tests

    func testMatchCountAlias() async throws {
        testContent = "a a a"
        manager.searchQuery = "a"

        XCTAssertEqual(manager.matchCount, manager.totalMatches)
        XCTAssertEqual(manager.matchCount, 3)
    }

    // MARK: - Update Current Match Tests

    func testUpdateCurrentMatchForCursorPosition() async throws {
        testContent = "a b a b a"
        manager.searchQuery = "a"

        // Find positions of 'a' in the string
        // Position 0: 'a', Position 4: 'a', Position 8: 'a'
        XCTAssertEqual(manager.totalMatches, 3)

        // Place cursor at position 5 (after second 'a')
        manager.updateCurrentMatch(forCursorPosition: 5)
        // Should select the match at or after position 5
        XCTAssertNotNil(manager.currentMatchIndex)
    }

    func testUpdateCurrentMatchNoMatches() async throws {
        manager.searchQuery = "NonExistent"

        manager.updateCurrentMatch(forCursorPosition: 0)
        XCTAssertNil(manager.currentMatchIndex)
    }

    // MARK: - Replace Query Tests

    func testReplaceQueryDefault() {
        XCTAssertEqual(manager.replaceQuery, "")
    }

    func testReplaceQuerySet() {
        manager.replaceQuery = "replacement"
        XCTAssertEqual(manager.replaceQuery, "replacement")
    }

    // MARK: - Combined Options Tests

    func testCombinedCaseSensitiveAndWholeWord() async throws {
        testContent = "Test test TEST testing Testing TESTING"
        manager.isCaseSensitive = true
        manager.isWholeWord = true
        manager.searchQuery = "Test"

        // Should only match exact "Test" (not "test", "TEST", or "Testing")
        XCTAssertEqual(manager.totalMatches, 1)
    }

    func testCombinedCaseInsensitiveAndWholeWord() async throws {
        testContent = "Test test TEST testing Testing TESTING"
        manager.isCaseSensitive = false
        manager.isWholeWord = true
        manager.searchQuery = "test"

        // Should match "Test", "test", "TEST" (not "testing", "Testing", "TESTING")
        XCTAssertEqual(manager.totalMatches, 3)
    }

    // MARK: - Special Characters Tests

    func testSearchWithSpecialRegexChars() async throws {
        testContent = "a.b a*b a+b a?b"
        manager.isRegex = false
        manager.searchQuery = "a.b"

        // With regex disabled, should only match literal "a.b"
        XCTAssertEqual(manager.totalMatches, 1)
    }

    func testSearchWithBackslash() async throws {
        testContent = "path\\to\\file"
        manager.isRegex = false
        manager.searchQuery = "\\"

        XCTAssertEqual(manager.totalMatches, 2)
    }

    func testRegexWithSpecialChars() async throws {
        testContent = "a.b aXb a9b"
        manager.isRegex = true
        manager.searchQuery = "a.b"

        // With regex enabled, "." matches any character
        XCTAssertEqual(manager.totalMatches, 3)
    }

    // MARK: - Text Provider Tests

    func testCustomTextProvider() async throws {
        let customContent = "custom content here"
        manager.textProvider = { customContent }

        manager.searchQuery = "custom"

        XCTAssertEqual(manager.totalMatches, 1)
    }

    func testNilTextProviderNoTextView() async throws {
        manager.textProvider = nil
        manager.textView = nil

        manager.searchQuery = "test"

        XCTAssertEqual(manager.totalMatches, 0)
        XCTAssertTrue(manager.matches.isEmpty)
    }

    // MARK: - Regex Replacement Template Tests

    /// Wires the manager to an in-memory buffer so replace operations mutate
    /// real text. Returns a closure reading the current buffer.
    private func makeReplaceHarness(_ initial: String) -> () -> String {
        var content = initial
        manager = makeManager(contentProvider: { content })
        manager.textReplacer = { range, replacement in
            let text = NSMutableString(string: content)
            text.replaceCharacters(in: range, with: replacement)
            content = text as String
        }
        return { content }
    }

    func testRegexReplaceAllExpandsBackreferences() {
        let buffer = makeReplaceHarness("foo_bar baz_qux")
        manager.isRegex = true
        manager.searchQuery = #"(\w+)_(\w+)"#
        manager.replaceQuery = "$2_$1"

        let count = manager.replaceAll()

        XCTAssertEqual(count, 2)
        XCTAssertEqual(buffer(), "bar_foo qux_baz")
    }

    func testRegexReplaceCurrentExpandsBackreferences() {
        let buffer = makeReplaceHarness("abc")
        manager.isRegex = true
        manager.searchQuery = "(a)(b)"
        manager.replaceQuery = "$2$1"

        manager.replaceCurrent()

        XCTAssertEqual(buffer(), "bac")
    }

    func testRegexReplaceSupportsWholeMatchReference() {
        let buffer = makeReplaceHarness("x = 1")
        manager.isRegex = true
        manager.searchQuery = #"\d+"#
        manager.replaceQuery = "($0)"

        manager.replaceAll()

        XCTAssertEqual(buffer(), "x = (1)")
    }

    func testLiteralModeKeepsDollarSignsLiteral() {
        let buffer = makeReplaceHarness("price: X")
        manager.isRegex = false
        manager.searchQuery = "X"
        manager.replaceQuery = "$1"

        manager.replaceAll()

        XCTAssertEqual(buffer(), "price: $1")
    }

    func testLiteralReplaceAllSkipsStaleRanges() {
        // The find panel computes `matches` once, then the user edits the buffer
        // directly (the panel does NOT re-search on in-editor edits). Replace All's
        // literal path must validate each stored range against the live buffer and
        // skip stale ones rather than splice at the wrong offset (or pass an
        // out-of-bounds range to the replacer).
        var content = "alpha beta alpha"
        manager = makeManager(contentProvider: { content })
        manager.textReplacer = { range, replacement in
            let text = NSMutableString(string: content)
            text.replaceCharacters(in: range, with: replacement)
            content = text as String
        }
        manager.isRegex = false
        manager.searchQuery = "alpha"
        manager.replaceQuery = "X"
        XCTAssertEqual(manager.totalMatches, 2)   // [0,5) and [11,16)

        // In-editor edit shrinks the buffer to 10 chars; manager.matches still
        // holds the old offsets: [0,5) now spans "beta " (substring mismatch) and
        // [11,16) is out of bounds. Both must be dropped.
        content = "beta alpha"

        let count = manager.replaceAll()

        XCTAssertEqual(count, 0)               // no stale splice applied
        XCTAssertEqual(content, "beta alpha")  // buffer untouched (no corruption/crash)
    }

    func testRegexReplaceOutOfRangeGroupStaysLiteral() {
        let buffer = makeReplaceHarness("aa")
        manager.isRegex = true
        manager.searchQuery = "(a)"
        manager.replaceQuery = "$5"

        manager.replaceAll()

        XCTAssertEqual(buffer(), "$5$5")
    }

    func testRegexReplaceEscapedDollarStaysLiteral() {
        let buffer = makeReplaceHarness("a")
        manager.isRegex = true
        manager.searchQuery = "(a)"
        manager.replaceQuery = #"\$1"#

        manager.replaceAll()

        XCTAssertEqual(buffer(), "$1")
    }

    func testRegexReplaceAllWithLookaheadUsesOriginalText() {
        // Lookahead must be evaluated against the pre-replacement buffer even
        // though replacements are applied end-to-start.
        let buffer = makeReplaceHarness("a1 a2 a9")
        manager.isRegex = true
        manager.searchQuery = #"a(?=\d)"#
        manager.replaceQuery = "b"

        let count = manager.replaceAll()

        XCTAssertEqual(count, 3)
        XCTAssertEqual(buffer(), "b1 b2 b9")
    }

    func testSanitizedTemplateEdgeCases() {
        // Bare dollar → literal.
        XCTAssertEqual(FindReplaceManager.sanitizedTemplate("cost $", captureGroupCount: 1), #"cost \$"#)
        // Valid group preserved.
        XCTAssertEqual(FindReplaceManager.sanitizedTemplate("$1", captureGroupCount: 1), "$1")
        // Out-of-range group escaped.
        XCTAssertEqual(FindReplaceManager.sanitizedTemplate("$3", captureGroupCount: 1), #"\$3"#)
        // With < 10 groups only one digit is consumed (ICU behavior): "$12" is
        // group 1 followed by literal "2".
        XCTAssertEqual(FindReplaceManager.sanitizedTemplate("$12", captureGroupCount: 3), "$12")
        // Existing escapes pass through untouched.
        XCTAssertEqual(FindReplaceManager.sanitizedTemplate(#"\$1"#, captureGroupCount: 1), #"\$1"#)
        // Lone trailing backslash escaped.
        XCTAssertEqual(FindReplaceManager.sanitizedTemplate(#"x\"#, captureGroupCount: 0), #"x\\"#)
    }

    // MARK: - Debounce Tests

    func testSearchDebounce() async throws {
        manager = makeManager(debounceInterval: .milliseconds(150))

        // Rapidly change search query
        manager.searchQuery = "a"
        manager.searchQuery = "ab"
        manager.searchQuery = "abc"

        // Should not have processed yet (debounce)
        XCTAssertEqual(manager.totalMatches, 0)

        try await Task.sleep(for: .milliseconds(200))

        // Now search should have been performed with final query
        XCTAssertTrue(manager.searchQuery == "abc")
    }
}
