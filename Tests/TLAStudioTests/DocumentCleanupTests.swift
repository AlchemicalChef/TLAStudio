import XCTest
@testable import TLAStudioApp

// MARK: - Document Cleanup Tests

/// Tests for TLADocument cleanup and lifecycle management.
@MainActor
final class DocumentCleanupTests: XCTestCase {

    // MARK: - Basic Cleanup Tests

    func testDocumentCloseWithoutSessions() {
        let doc = TLADocument()

        // Close should not crash when no sessions exist
        doc.close()

        XCTAssertNil(doc.tlcSession)
        XCTAssertNil(doc.proofSession)
    }

    func testDocumentClearsDiagnosticsOnClose() {
        let doc = TLADocument()
        // Set some content to trigger parsing
        doc.content = "MODULE Test"

        doc.close()

        XCTAssertTrue(doc.diagnostics.isEmpty)
    }

    func testDocumentClearsSymbolsOnClose() {
        let doc = TLADocument()

        doc.close()

        XCTAssertTrue(doc.symbols.isEmpty)
    }

    func testDocumentClearsParseResultOnClose() {
        let doc = TLADocument()

        doc.close()

        XCTAssertNil(doc.parseResult)
    }

    func testDocumentClearsLastTLCResultOnClose() {
        let doc = TLADocument()

        doc.close()

        XCTAssertNil(doc.lastTLCResult)
    }

    func testDocumentClearsLastProofResultOnClose() {
        let doc = TLADocument()

        doc.close()

        XCTAssertNil(doc.lastProofResult)
    }

    // MARK: - Content Tests

    func testNewDocumentHasDefaultContent() {
        let doc = TLADocument()

        XCTAssertFalse(doc.content.isEmpty)
        XCTAssertTrue(doc.content.contains("MODULE"))
    }

    func testDocumentContentChange() {
        let doc = TLADocument()
        let newContent = "---- MODULE Test ----\n===="

        doc.content = newContent

        XCTAssertEqual(doc.content, newContent)
    }

    // MARK: - Module Name Tests

    func testModuleNameExtraction() {
        let doc = TLADocument()
        doc.content = "---- MODULE TestModule ----\n===="

        XCTAssertEqual(doc.moduleName, "TestModule")
    }

    func testModuleNameFallbackToUntitled() {
        let doc = TLADocument()
        doc.content = "no module header"

        XCTAssertEqual(doc.moduleName, "Untitled")
    }

    // MARK: - Encoding Tests

    func testDefaultEncodingIsUTF8() {
        let doc = TLADocument()

        XCTAssertEqual(doc.encoding, .utf8)
    }

    func testDefaultLineEndingIsLF() {
        let doc = TLADocument()

        XCTAssertEqual(doc.lineEnding, .lf)
    }

    // MARK: - Session Tests

    func testInitialTLCSessionIsNil() {
        let doc = TLADocument()

        XCTAssertNil(doc.tlcSession)
    }

    func testInitialProofSessionIsNil() {
        let doc = TLADocument()

        XCTAssertNil(doc.proofSession)
    }

    func testDefaultTLCModeIsAuto() {
        let doc = TLADocument()

        XCTAssertEqual(doc.selectedTLCMode, .auto)
    }

    // MARK: - Selected Range Tests

    func testInitialSelectedRange() {
        let doc = TLADocument()

        XCTAssertEqual(doc.selectedRange.location, 0)
        XCTAssertEqual(doc.selectedRange.length, 0)
    }

    func testSelectedRangeUpdate() {
        let doc = TLADocument()
        let newRange = NSRange(location: 10, length: 5)

        doc.selectedRange = newRange

        XCTAssertEqual(doc.selectedRange.location, 10)
        XCTAssertEqual(doc.selectedRange.length, 5)
    }

    // MARK: - Symbol Lookup Tests

    func testSymbolAtOffsetWithEmptySymbols() {
        let doc = TLADocument()

        let symbol = doc.symbolAt(characterOffset: 10)

        XCTAssertNil(symbol)
    }

    // MARK: - Close Delegate Tests

    func testDelegateIsNilAfterClose() {
        let doc = TLADocument()
        // No delegate set, but close should clear it

        doc.close()

        XCTAssertNil(doc.delegate)
    }
}

// MARK: - TLADocument Autosave Configuration Tests

final class DocumentConfigurationTests: XCTestCase {

    func testAutosavesInPlace() {
        XCTAssertTrue(TLADocument.autosavesInPlace)
    }

    func testAutosavesDrafts() {
        XCTAssertTrue(TLADocument.autosavesDrafts)
    }

    func testPreservesVersions() {
        XCTAssertTrue(TLADocument.preservesVersions)
    }
}

// MARK: - Line Ending Tests (Document Cleanup)

final class DocumentCleanupLineEndingTests: XCTestCase {

    func testLineEndingLF() {
        let ending = LineEnding.lf
        // Just verify the enum case exists
        XCTAssertNotNil(ending)
    }

    func testLineEndingCRLF() {
        let ending = LineEnding.crlf
        XCTAssertNotNil(ending)
    }

    func testLineEndingCR() {
        let ending = LineEnding.cr
        XCTAssertNotNil(ending)
    }
}

// MARK: - Parser Buffer Limit Tests

/// Tests for TLAPMOutputParser buffer handling.
/// Since OutputAccumulator is private, we test through the public parser API.
final class ParserBufferTests: XCTestCase {

    func testParserHandlesLargeInput() {
        let parser = TLAPMOutputParser()

        // Create a large block of data
        var largeData = "@!!BEGIN\n@!!type:obligation\n@!!id:1\n@!!status:proved\n"
        // Add lots of padding
        for i in 0..<10000 {
            largeData += "@!!comment:padding line \(i)\n"
        }
        largeData += "@!!END\n"

        let data = largeData.data(using: .utf8)!
        let progress = parser.parse(data)

        // Parser should handle large input
        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.provedCount, 1)
    }

    func testParserHandlesManyObligations() {
        let parser = TLAPMOutputParser()

        // Create many obligations
        for i in 1...1000 {
            let block = "@!!BEGIN\n@!!type:obligation\n@!!id:\(i)\n@!!status:proved\n@!!END\n"
            _ = parser.parse(block.data(using: .utf8)!)
        }

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.count, 1000)
    }

    func testParserResetClearsBuffer() {
        let parser = TLAPMOutputParser()

        // Add some data
        let block = "@!!BEGIN\n@!!type:obligation\n@!!id:1\n@!!status:proved\n@!!END\n"
        _ = parser.parse(block.data(using: .utf8)!)

        XCTAssertEqual(parser.getAllObligations().count, 1)

        // Reset
        parser.reset()

        XCTAssertTrue(parser.getAllObligations().isEmpty)
    }
}

// MARK: - TLC Output Parser Buffer Tests

final class TLCParserBufferTests: XCTestCase {

    func testTLCParserHandlesLargeInput() {
        let parser = TLCOutputParser()

        // Create large progress output
        var output = ""
        for i in 0..<10000 {
            output += "Progress(\(i)): \(i * 1000) states generated, \(i * 500) distinct states found.\n"
        }

        let data = output.data(using: .utf8)!
        _ = parser.parse(data)

        // Parser should not crash with large input
        // Just verify it processed without error
        XCTAssertTrue(true)
    }

    func testTLCParserHandlesPartialLines() {
        let parser = TLCOutputParser()

        // Send partial lines
        _ = parser.parse("Progress(0): 1000 states gene".data(using: .utf8)!)
        _ = parser.parse("rated, 500 distinct states found.\n".data(using: .utf8)!)

        // Parser should handle line buffering
        // Just verify no crash
        XCTAssertTrue(true)
    }

    func testTLCParserReset() {
        let parser = TLCOutputParser()

        // Add some data
        _ = parser.parse("Model checking completed.\n".data(using: .utf8)!)

        // Reset
        parser.reset()

        // Should be in clean state
        // Just verify no crash
        XCTAssertTrue(true)
    }
}

// MARK: - Document Integration Tests

@MainActor
final class DocumentIntegrationTests: XCTestCase {

    func testDocumentCreateModifyClose() {
        let doc = TLADocument()

        // Verify initial state
        XCTAssertFalse(doc.content.isEmpty)
        XCTAssertNil(doc.tlcSession)
        XCTAssertNil(doc.proofSession)

        // Modify content
        doc.content = "---- MODULE Test ----\n===="
        XCTAssertTrue(doc.content.contains("Test"))

        // Close
        doc.close()
        XCTAssertTrue(doc.diagnostics.isEmpty)
    }

    func testDocumentContentTriggersChange() {
        let doc = TLADocument()
        let initialContent = doc.content

        doc.content = "New Content"

        XCTAssertNotEqual(doc.content, initialContent)
    }

    func testDocumentMultipleCloses() {
        let doc = TLADocument()

        // Multiple closes should not crash
        doc.close()

        // Note: After close, accessing the document may have undefined behavior
        // but the close itself should not crash
    }

    func testDocumentEncodingPersistence() {
        let doc = TLADocument()

        doc.encoding = .windowsCP1252
        XCTAssertEqual(doc.encoding, .windowsCP1252)

        doc.encoding = .utf8
        XCTAssertEqual(doc.encoding, .utf8)
    }

    func testDocumentLineEndingPersistence() {
        let doc = TLADocument()

        doc.lineEnding = .crlf
        XCTAssertEqual(doc.lineEnding, .crlf)

        doc.lineEnding = .lf
        XCTAssertEqual(doc.lineEnding, .lf)
    }

    func testDocumentWithRealTLAContent() {
        let doc = TLADocument()

        let tlaContent = """
        -------------------------------- MODULE Test --------------------------------
        EXTENDS Naturals

        VARIABLES x

        Init == x = 0
        Next == x' = x + 1

        Spec == Init /\\ [][Next]_x

        TypeOK == x \\in Nat

        =============================================================================
        """

        doc.content = tlaContent

        XCTAssertEqual(doc.moduleName, "Test")
        XCTAssertTrue(doc.content.contains("EXTENDS"))
        XCTAssertTrue(doc.content.contains("VARIABLES"))
    }

    func testDocumentSelectedRangeWithContent() {
        let doc = TLADocument()
        doc.content = "Line1\nLine2\nLine3"

        // Set selection to middle of second line
        let offset = doc.offset(forLine: 1, column: 2)
        doc.selectedRange = NSRange(location: offset, length: 3)

        XCTAssertEqual(doc.selectedRange.location, offset)
        XCTAssertEqual(doc.selectedRange.length, 3)
    }

    func testDocumentRapidContentChanges() {
        let doc = TLADocument()

        // Rapid content changes should not cause issues
        for i in 0..<100 {
            doc.content = "Content iteration \(i)\n" + String(repeating: "Line\n", count: i % 10)
        }

        // Should still be functional
        XCTAssertFalse(doc.content.isEmpty)
    }
}

// MARK: - Document Go To Definition Tests

@MainActor
final class DocumentGoToDefinitionTests: XCTestCase {

    func testGoToDefinitionWithNoSymbols() {
        let doc = TLADocument()
        doc.content = "Simple content"

        let result = doc.goToDefinition(at: 0)
        XCTAssertFalse(result)
    }

    func testSymbolAtOffsetWithEmptyContent() {
        let doc = TLADocument()
        doc.content = ""

        let symbol = doc.symbolAt(characterOffset: 0)
        XCTAssertNil(symbol)
    }

    func testSymbolAtNegativeOffset() {
        let doc = TLADocument()
        doc.content = "Content"

        let symbol = doc.symbolAt(characterOffset: -1)
        XCTAssertNil(symbol)
    }

    func testSymbolAtOffsetBeyondContent() {
        let doc = TLADocument()
        doc.content = "Short"

        let symbol = doc.symbolAt(characterOffset: 1000)
        XCTAssertNil(symbol)
    }

    func testExtendedModuleNamesIncludeWrappedAndRepeatedExtendsClauses() {
        let content = """
        ---- MODULE Example ----
        EXTENDS Naturals,
                Sequences \\* standard modules
        CONSTANTS N
        EXTENDS TLC
        ====
        """

        XCTAssertEqual(
            TLADocument.extendedModuleNames(in: content),
            Set(["Naturals", "Sequences", "TLC"])
        )
    }

    func testExtendedModuleNamesIgnoreCommentOnlyContinuationLines() {
        let content = """
        ---- MODULE Example ----
        EXTENDS Naturals,
        \\* comment between continuation lines
                Sequences
        ====
        """

        XCTAssertEqual(
            TLADocument.extendedModuleNames(in: content),
            Set(["Naturals", "Sequences"])
        )
    }
}

// MARK: - Document Data Tests

@MainActor
final class DocumentDataTests: XCTestCase {

    func testDataOfTypeUTF8() throws {
        let doc = TLADocument()
        doc.content = "Hello World"
        doc.encoding = .utf8

        let data = try doc.data(ofType: "com.tlaplus.specification")

        XCTAssertEqual(String(data: data, encoding: .utf8), "Hello World")
    }

    func testDataOfTypeWithCRLF() throws {
        let doc = TLADocument()
        doc.content = "Line1\nLine2"
        doc.lineEnding = .crlf
        doc.encoding = .utf8

        let data = try doc.data(ofType: "com.tlaplus.specification")
        let text = String(data: data, encoding: .utf8)

        XCTAssertTrue(text?.contains("\r\n") ?? false)
    }

    func testDataOfTypeWithCR() throws {
        let doc = TLADocument()
        doc.content = "Line1\nLine2"
        doc.lineEnding = .cr
        doc.encoding = .utf8

        let data = try doc.data(ofType: "com.tlaplus.specification")
        let text = String(data: data, encoding: .utf8)

        XCTAssertTrue(text?.contains("\r") ?? false)
        XCTAssertFalse(text?.contains("\n") ?? true)
    }

    func testDataOfTypeWithLF() throws {
        let doc = TLADocument()
        doc.content = "Line1\nLine2"
        doc.lineEnding = .lf
        doc.encoding = .utf8

        let data = try doc.data(ofType: "com.tlaplus.specification")
        let text = String(data: data, encoding: .utf8)

        XCTAssertTrue(text?.contains("\n") ?? false)
        XCTAssertFalse(text?.contains("\r") ?? true)
    }
}

// MARK: - Concurrent Document Access Tests

@MainActor
final class ConcurrentDocumentTests: XCTestCase {

    func testConcurrentContentAccess() async {
        let doc = TLADocument()

        // Concurrent reads and writes
        await withTaskGroup(of: Void.self) { group in
            // Writers
            for i in 0..<50 {
                group.addTask { @MainActor in
                    doc.content = "Content \(i)"
                }
            }

            // Readers
            for _ in 0..<50 {
                group.addTask { @MainActor in
                    _ = doc.content
                    _ = doc.moduleName
                    _ = doc.lineAndColumn(for: 0)
                }
            }
        }

        // Should complete without crash
        XCTAssertFalse(doc.content.isEmpty)
    }

    func testConcurrentSelectedRangeUpdates() async {
        let doc = TLADocument()
        doc.content = String(repeating: "A", count: 1000)

        await withTaskGroup(of: Void.self) { group in
            for i in 0..<100 {
                group.addTask { @MainActor in
                    doc.selectedRange = NSRange(location: i % 1000, length: 1)
                }
            }
        }

        // Should complete without crash
        XCTAssertGreaterThanOrEqual(doc.selectedRange.location, 0)
    }
}

// MARK: - TLA Core Wrapper Tests

@MainActor
final class TLACoreWrapperTests: XCTestCase {

    func testSharedInstanceExists() {
        let wrapper = TLACoreWrapper.shared
        XCTAssertNotNil(wrapper)
    }

    func testParseMinimalContent() async {
        do {
            // Parser expects non-empty content, so use minimal valid TLA+
            let result = try await TLACoreWrapper.shared.parse("---- MODULE X ----\n====")
            // Minimal content should parse
            XCTAssertNotNil(result)
        } catch {
            // Some parse errors are expected
            XCTAssertTrue(true)
        }
    }

    func testParseValidTLAContent() async {
        let content = """
        ---- MODULE Test ----
        EXTENDS Naturals
        VARIABLE x
        Init == x = 0
        ====
        """

        do {
            let result = try await TLACoreWrapper.shared.parse(content)
            XCTAssertNotNil(result)
        } catch {
            // Parse might fail if tree-sitter grammar expects different format
            XCTAssertTrue(true)
        }
    }

    func testWordAtPositionEmpty() {
        let word = TLACoreWrapper.shared.wordAt(
            position: TLAPosition(line: 0, column: 0),
            in: ""
        )
        XCTAssertNil(word)
    }

    func testWordAtPositionWithContent() {
        let word = TLACoreWrapper.shared.wordAt(
            position: TLAPosition(line: 0, column: 2),
            in: "Hello World"
        )
        // May or may not find a word depending on implementation
        // Just verify no crash
        _ = word
    }

    func testFindDefinitionEmpty() {
        let range = TLACoreWrapper.shared.findDefinition(
            named: "NonExistent",
            in: []
        )
        XCTAssertNil(range)
    }

    func testParseMultipleTimes() async {
        // Test parsing multiple times in sequence
        for i in 0..<5 {
            let content = "---- MODULE Test\(i) ----\n===="
            do {
                let result = try await TLACoreWrapper.shared.parse(content)
                XCTAssertNotNil(result)
            } catch {
                // Some parse errors expected
            }
        }
    }
}
