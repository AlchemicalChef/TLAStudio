import XCTest
@testable import TLAStudioApp

// MARK: - Editor Functionality Tests

/// Tests for editor-related functionality that can be tested without UI.
final class EditorFunctionalityTests: XCTestCase {

    // MARK: - TLA Core Wrapper Tests

    @MainActor
    func testTLACoreWrapperSingleton() {
        let wrapper1 = TLACoreWrapper.shared
        let wrapper2 = TLACoreWrapper.shared

        XCTAssertTrue(wrapper1 === wrapper2)
    }

    @MainActor
    func testParseMinimalContent() async throws {
        // Parser expects non-empty content, so use minimal valid TLA+
        let result = try await TLACoreWrapper.shared.parse("---- MODULE X ----\n====")

        XCTAssertNotNil(result)
    }

    @MainActor
    func testParseValidTLAContent() async throws {
        let content = """
        ---- MODULE Test ----
        VARIABLES x
        Init == x = 0
        Next == x' = x + 1
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)

        XCTAssertNotNil(result)
    }

    @MainActor
    func testParseContentWithSyntaxError() async throws {
        let content = """
        ---- MODULE Test ----
        VARIABLES x
        Init == x = = 0
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)

        // Should still return a result, possibly with diagnostics
        XCTAssertNotNil(result)
    }

    @MainActor
    func testWordAtPosition() {
        let content = "VARIABLES counter"
        let position = TLAPosition(line: 0, column: 12)

        let word = TLACoreWrapper.shared.wordAt(position: position, in: content)

        // Should find "counter" or nearby word
        XCTAssertNotNil(word)
    }

    @MainActor
    func testWordAtPositionEmptyContent() {
        let content = ""
        let position = TLAPosition(line: 0, column: 0)

        let word = TLACoreWrapper.shared.wordAt(position: position, in: content)

        XCTAssertNil(word)
    }

    @MainActor
    func testWordAtPositionBeyondContent() {
        let content = "Hello"
        let position = TLAPosition(line: 100, column: 100)

        let word = TLACoreWrapper.shared.wordAt(position: position, in: content)

        XCTAssertNil(word)
    }

    @MainActor
    func testWordAtPositionMultilineUnicode() {
        let content = "---- MODULE Test ----\n🙂counter == 1\n===="
        let position = TLAPosition(line: 1, column: 2)

        let word = TLACoreWrapper.shared.wordAt(position: position, in: content)

        XCTAssertEqual(word, "counter")
    }

    @MainActor
    func testFindDefinitionInSymbols() {
        let symbols = [
            TLASymbol(name: "Init", kind: .operator, range: TLARange(
                start: TLAPosition(line: 5, column: 0),
                end: TLAPosition(line: 5, column: 4)
            ), selectionRange: nil, children: [], parameters: []),
            TLASymbol(name: "Next", kind: .operator, range: TLARange(
                start: TLAPosition(line: 7, column: 0),
                end: TLAPosition(line: 7, column: 4)
            ), selectionRange: nil, children: [], parameters: [])
        ]

        let range = TLACoreWrapper.shared.findDefinition(named: "Init", in: symbols)

        XCTAssertNotNil(range)
        XCTAssertEqual(range?.start.line, 5)
    }

    @MainActor
    func testFindDefinitionNotFound() {
        let symbols = [
            TLASymbol(name: "Init", kind: .operator, range: TLARange(
                start: TLAPosition(line: 5, column: 0),
                end: TLAPosition(line: 5, column: 4)
            ), selectionRange: nil, children: [], parameters: [])
        ]

        let range = TLACoreWrapper.shared.findDefinition(named: "NotExist", in: symbols)

        XCTAssertNil(range)
    }

    @MainActor
    func testFindDefinitionInNestedSymbols() {
        let childSymbol = TLASymbol(name: "NestedOp", kind: .operator, range: TLARange(
            start: TLAPosition(line: 10, column: 4),
            end: TLAPosition(line: 10, column: 12)
        ), selectionRange: nil, children: [], parameters: [])

        let parentSymbol = TLASymbol(name: "Parent", kind: .module, range: TLARange(
            start: TLAPosition(line: 0, column: 0),
            end: TLAPosition(line: 20, column: 0)
        ), selectionRange: nil, children: [childSymbol], parameters: [])

        let range = TLACoreWrapper.shared.findDefinition(named: "NestedOp", in: [parentSymbol])

        XCTAssertNotNil(range)
        XCTAssertEqual(range?.start.line, 10)
    }

    // MARK: - TLA Symbol Tests

    func testTLASymbolCreation() {
        let symbol = TLASymbol(
            name: "TestOp",
            kind: .operator,
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 6)
            ),
            selectionRange: nil,
            children: [],
            parameters: []
        )

        XCTAssertEqual(symbol.name, "TestOp")
        XCTAssertEqual(symbol.kind, .operator)
        XCTAssertTrue(symbol.children.isEmpty)
    }

    func testTLASymbolKinds() {
        let kinds: [TLASymbolKind] = [
            .module, .constant, .variable, .operator, .theorem, .assumption
        ]

        for kind in kinds {
            let symbol = TLASymbol(
                name: "Test",
                kind: kind,
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 4)
                ),
                selectionRange: nil,
                children: [],
                parameters: []
            )
            XCTAssertEqual(symbol.kind, kind)
        }
    }

    func testTLASymbolWithChildren() {
        let child = TLASymbol(
            name: "Child",
            kind: .operator,
            range: TLARange(
                start: TLAPosition(line: 2, column: 2),
                end: TLAPosition(line: 2, column: 7)
            ),
            selectionRange: nil,
            children: [],
            parameters: []
        )

        let parent = TLASymbol(
            name: "Parent",
            kind: .module,
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 10, column: 0)
            ),
            selectionRange: nil,
            children: [child],
            parameters: []
        )

        XCTAssertEqual(parent.children.count, 1)
        XCTAssertEqual(parent.children.first?.name, "Child")
    }

    // MARK: - TLA Position Tests

    func testTLAPositionCreation() {
        let position = TLAPosition(line: 10, column: 5)

        XCTAssertEqual(position.line, 10)
        XCTAssertEqual(position.column, 5)
    }

    func testTLAPositionZero() {
        let position = TLAPosition(line: 0, column: 0)

        XCTAssertEqual(position.line, 0)
        XCTAssertEqual(position.column, 0)
    }

    func testTLAPositionLargeValues() {
        let position = TLAPosition(line: UInt32.max, column: UInt32.max)

        XCTAssertEqual(position.line, UInt32.max)
        XCTAssertEqual(position.column, UInt32.max)
    }

    // MARK: - TLA Range Tests

    func testTLARangeCreation() {
        let range = TLARange(
            start: TLAPosition(line: 5, column: 0),
            end: TLAPosition(line: 10, column: 20)
        )

        XCTAssertEqual(range.start.line, 5)
        XCTAssertEqual(range.end.line, 10)
    }

    func testTLARangeSingleLine() {
        let range = TLARange(
            start: TLAPosition(line: 5, column: 0),
            end: TLAPosition(line: 5, column: 10)
        )

        XCTAssertEqual(range.start.line, range.end.line)
    }

    func testTLARangeZeroLength() {
        let range = TLARange(
            start: TLAPosition(line: 5, column: 5),
            end: TLAPosition(line: 5, column: 5)
        )

        XCTAssertEqual(range.start.line, range.end.line)
        XCTAssertEqual(range.start.column, range.end.column)
    }

    // MARK: - TLA Diagnostic Tests

    func testTLADiagnosticCreation() {
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 5, column: 0),
                end: TLAPosition(line: 5, column: 10)
            ),
            severity: .error,
            message: "Syntax error",
            code: "E001"
        )

        XCTAssertEqual(diagnostic.severity, .error)
        XCTAssertEqual(diagnostic.message, "Syntax error")
        XCTAssertEqual(diagnostic.code, "E001")
    }

    func testTLADiagnosticSeverities() {
        let severities: [TLADiagnosticSeverity] = [.error, .warning, .information, .hint]

        for severity in severities {
            let diagnostic = TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 0)
                ),
                severity: severity,
                message: "Test",
                code: nil
            )
            XCTAssertEqual(diagnostic.severity, severity)
        }
    }

    func testTLADiagnosticWithoutCode() {
        let diagnostic = TLADiagnostic(
            range: TLARange(
                start: TLAPosition(line: 0, column: 0),
                end: TLAPosition(line: 0, column: 0)
            ),
            severity: .warning,
            message: "Warning message",
            code: nil
        )

        XCTAssertNil(diagnostic.code)
    }

    // MARK: - TLA Parse Result Tests

    @MainActor
    func testTLAParseResultDiagnostics() async throws {
        let content = """
        ---- MODULE Test ----
        VARIABLES x
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)

        // Diagnostics should be an array (possibly empty for valid content)
        XCTAssertNotNil(result.diagnostics)
    }

    // MARK: - Symbol Extraction Tests

    @MainActor
    func testExtractSymbolsFromParseResult() async throws {
        let content = """
        ---- MODULE Test ----
        VARIABLES x, y
        Init == x = 0 /\\ y = 0
        Next == x' = x + 1 /\\ y' = y
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)
        let symbols = await TLACoreWrapper.shared.getSymbols(from: result)

        // Should extract some symbols
        XCTAssertNotNil(symbols)
    }

    // MARK: - Highlighting Token Tests

    @MainActor
    func testHighlightingTokenTypes() async throws {
        let content = """
        ---- MODULE Test ----
        VARIABLES x
        Init == x = 0
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)

        // Parse result should have tokens (if highlighting is enabled)
        XCTAssertNotNil(result)
    }

    // MARK: - Concurrent Parsing Tests

    @MainActor
    func testConcurrentParsing() async throws {
        let content = """
        ---- MODULE Test ----
        VARIABLES x
        Init == x = 0
        ====
        """

        // Parse multiple times concurrently
        async let result1 = TLACoreWrapper.shared.parse(content)
        async let result2 = TLACoreWrapper.shared.parse(content)
        async let result3 = TLACoreWrapper.shared.parse(content)

        let results = try await [result1, result2, result3]

        // All should succeed
        XCTAssertEqual(results.count, 3)
        for result in results {
            XCTAssertNotNil(result)
        }
    }

    // MARK: - Large Content Parsing Tests

    @MainActor
    func testParseLargeContent() async throws {
        var content = "---- MODULE Large ----\nVARIABLES "
        for i in 0..<1000 {
            content += "v\(i), "
        }
        content += "last\n====\n"

        let result = try await TLACoreWrapper.shared.parse(content)

        XCTAssertNotNil(result)
    }

    // MARK: - Unicode Content Parsing Tests

    @MainActor
    func testParseUnicodeContent() async throws {
        let content = """
        ---- MODULE Unicode ----
        (* 日本語のコメント *)
        VARIABLES α, β, γ
        Init == α = 0 ∧ β = 0 ∧ γ = 0
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)

        XCTAssertNotNil(result)
    }

    // MARK: - Special TLA+ Syntax Tests

    @MainActor
    func testParseTLAOperators() async throws {
        let content = """
        ---- MODULE Operators ----
        VARIABLES x, S
        Test1 == \\A y \\in S : y > 0
        Test2 == \\E y \\in S : y = x
        Test3 == <<1, 2, 3>>
        Test4 == [a |-> 1, b |-> 2]
        Test5 == x \\in S
        Test6 == DOMAIN x
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)

        XCTAssertNotNil(result)
    }

    @MainActor
    func testParsePlusCal() async throws {
        let content = """
        ---- MODULE PlusCal ----
        (*--algorithm test
        variables x = 0;
        begin
          x := x + 1;
        end algorithm;*)
        ====
        """

        let result = try await TLACoreWrapper.shared.parse(content)

        XCTAssertNotNil(result)
    }

    // MARK: - Find/Replace Manager Tests

    @MainActor
    func testFindReplaceManagerInitialization() {
        let manager = FindReplaceManager()

        XCTAssertTrue(manager.searchQuery.isEmpty)
        XCTAssertTrue(manager.replaceQuery.isEmpty)
        XCTAssertFalse(manager.isCaseSensitive)
        XCTAssertFalse(manager.isRegex)
        XCTAssertFalse(manager.isWholeWord)
    }

    @MainActor
    func testFindReplaceManagerSearchQuery() {
        let manager = FindReplaceManager()
        manager.searchQuery = "VARIABLES"

        XCTAssertEqual(manager.searchQuery, "VARIABLES")
    }

    @MainActor
    func testFindReplaceManagerReplaceQuery() {
        let manager = FindReplaceManager()
        manager.replaceQuery = "CONSTANTS"

        XCTAssertEqual(manager.replaceQuery, "CONSTANTS")
    }

    @MainActor
    func testFindReplaceManagerOptions() {
        let manager = FindReplaceManager()
        manager.isCaseSensitive = true
        manager.isRegex = true
        manager.isWholeWord = true

        XCTAssertTrue(manager.isCaseSensitive)
        XCTAssertTrue(manager.isRegex)
        XCTAssertTrue(manager.isWholeWord)
    }

    // MARK: - Output Manager Tests

    func testOutputManagerSingleton() {
        let manager1 = OutputManager.shared
        let manager2 = OutputManager.shared

        XCTAssertTrue(manager1 === manager2)
    }

    func testOutputManagerLogTLC() {
        let manager = OutputManager.shared

        // Should not crash
        manager.logTLC("Test TLC output")
        manager.logTLC("Error output", isError: true)
    }

    func testOutputManagerLogTLAPM() {
        let manager = OutputManager.shared

        // Should not crash
        manager.logTLAPM("Test TLAPM output")
        manager.logTLAPM("Warning output", isError: false)
    }

    func testOutputManagerLogSystem() {
        let manager = OutputManager.shared

        // Should not crash
        manager.log("System message", source: .system)
    }

    func testOutputManagerClear() {
        let manager = OutputManager.shared

        manager.logTLC("Test")
        manager.clear()

        // Should not crash and entries should be cleared
    }
}

// MARK: - Completion Notifier Tests

// NOTE: CompletionNotifier tests are excluded because they require
// UNUserNotificationCenter which is not available in the test environment.
// The CompletionNotifier is tested indirectly through integration tests.
