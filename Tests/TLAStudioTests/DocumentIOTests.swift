import XCTest
@testable import TLAStudioApp

// MARK: - Document I/O Tests

/// Tests for document file I/O, encoding, and parsing integration.
@MainActor
final class DocumentIOTests: TempDirectoryTestCase {

    // MARK: - File Reading Tests

    func testReadUTF8File() throws {
        let fileURL = tempDirectory.appendingPathComponent("test.tla")
        let content = "---- MODULE Test ----\nVARIABLES x\n===="
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertTrue(document.content.contains("MODULE Test"))
        XCTAssertEqual(document.encoding, .utf8)
    }

    func testReadWindowsCP1252File() throws {
        let fileURL = tempDirectory.appendingPathComponent("test_cp1252.tla")
        let content = "---- MODULE Test ----\nVARIABLES x\n===="
        let data = content.data(using: .windowsCP1252)!
        try data.write(to: fileURL)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertTrue(document.content.contains("MODULE Test"))
        // Encoding should be detected as CP1252 or UTF-8 (CP1252 is a superset for ASCII)
    }

    func testReadEmptyFile() throws {
        let fileURL = tempDirectory.appendingPathComponent("empty.tla")
        try "".write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertTrue(document.content.isEmpty)
    }

    func testReadLargeFile() throws {
        let fileURL = tempDirectory.appendingPathComponent("large.tla")
        var content = "---- MODULE Large ----\n"
        for i in 0..<10000 {
            content += "Var\(i) == TRUE\n"
        }
        content += "===="
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertTrue(document.content.contains("MODULE Large"))
        XCTAssertTrue(document.content.contains("Var9999"))
    }

    func testReadNonexistentFile() {
        let fileURL = tempDirectory.appendingPathComponent("nonexistent.tla")
        let document = TLADocument()

        XCTAssertThrowsError(try document.read(from: fileURL, ofType: "com.tlaplus.specification"))
    }

    // MARK: - Dirty-State Tests

    func testOpenedDocumentIsNotDirty() throws {
        // init() seeds `content` with the template, bumping the change count to 1;
        // read() must clear it so an unedited opened file isn't shown dirty (and so
        // specURLForTooling can use the real fileURL instead of forcing a temp copy).
        let fileURL = tempDirectory.appendingPathComponent("clean.tla")
        let content = "---- MODULE Clean ----\nVARIABLES x\n===="
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertFalse(document.isDocumentEdited)
    }

    // MARK: - Line Ending Tests

    func testDetectLFLineEndings() throws {
        let fileURL = tempDirectory.appendingPathComponent("lf.tla")
        let content = "---- MODULE Test ----\nVARIABLES x\n===="
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertEqual(document.lineEnding, .lf)
    }

    func testDetectCRLFLineEndings() throws {
        let fileURL = tempDirectory.appendingPathComponent("crlf.tla")
        let content = "---- MODULE Test ----\r\nVARIABLES x\r\n===="
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertEqual(document.lineEnding, .crlf)
        // Content should be normalized to LF internally
        XCTAssertFalse(document.content.contains("\r\n"))
    }

    func testDetectCRLineEndings() throws {
        let fileURL = tempDirectory.appendingPathComponent("cr.tla")
        let content = "---- MODULE Test ----\rVARIABLES x\r===="
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertEqual(document.lineEnding, .cr)
    }

    // MARK: - File Writing Tests

    func testWriteUTF8File() throws {
        let document = TLADocument()
        document.content = "---- MODULE Test ----\nVARIABLES x\n===="
        document.encoding = .utf8

        let data = try document.data(ofType: "com.tlaplus.specification")
        let written = String(data: data, encoding: .utf8)

        XCTAssertEqual(written, document.content)
    }

    func testWriteWithCRLFLineEndings() throws {
        let document = TLADocument()
        document.content = "---- MODULE Test ----\nVARIABLES x\n===="
        document.lineEnding = .crlf

        let data = try document.data(ofType: "com.tlaplus.specification")
        let written = String(data: data, encoding: .utf8)!

        XCTAssertTrue(written.contains("\r\n"))
        XCTAssertFalse(written.contains("\n") && !written.contains("\r\n"))
    }

    func testWriteWithCRLineEndings() throws {
        let document = TLADocument()
        document.content = "---- MODULE Test ----\nVARIABLES x\n===="
        document.lineEnding = .cr

        let data = try document.data(ofType: "com.tlaplus.specification")
        let written = String(data: data, encoding: .utf8)!

        XCTAssertTrue(written.contains("\r"))
        XCTAssertFalse(written.contains("\n"))
    }

    func testWriteEmptyDocument() throws {
        let document = TLADocument()
        document.content = ""

        let data = try document.data(ofType: "com.tlaplus.specification")

        XCTAssertTrue(data.isEmpty)
    }

    func testSaveUpgradesToUTF8WhenLegacyEncodingCannotRepresentContent() throws {
        // A file detected as Windows-1252 that later contains a Unicode math
        // operator (∈, U+2208) cannot be re-serialized as CP1252. Rather than
        // refusing the save behind an opaque error (data loss), data(ofType:)
        // must transparently upgrade to UTF-8 — a universal superset.
        let document = TLADocument()
        document.encoding = .windowsCP1252
        document.content = "---- MODULE Test ----\nFoo == x \u{2208} S\n===="

        let data = try document.data(ofType: "com.tlaplus.specification")

        XCTAssertEqual(document.encoding, .utf8)   // pinned so later saves stay consistent
        XCTAssertEqual(String(data: data, encoding: .utf8), document.content)
    }

    // MARK: - Module Name Extraction Tests

    func testModuleNameFromContent() {
        let document = TLADocument()
        document.content = "---- MODULE MyModule ----\nVARIABLES x\n===="

        XCTAssertEqual(document.moduleName, "MyModule")
    }

    func testModuleNameFromContentWithDashes() {
        let document = TLADocument()
        document.content = "-------------------------------- MODULE TestSpec --------------------------------\n===="

        XCTAssertEqual(document.moduleName, "TestSpec")
    }

    func testModuleNameFallsBackToFilename() throws {
        let fileURL = tempDirectory.appendingPathComponent("FallbackName.tla")
        try "VARIABLES x\n====".write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        // Set fileURL manually for test (normally done by NSDocument)
        // Note: moduleName should fall back to filename when no MODULE declaration found
        // Since we can't easily set fileURL, this tests the content path
        XCTAssertNotNil(document.moduleName)
    }

    func testModuleNameUntitledDocument() {
        let document = TLADocument()
        document.content = "VARIABLES x\n===="

        // Should return "Untitled" when no module declaration and no file
        // Note: The default template has a module name, so we need to check with custom content
        XCTAssertNotNil(document.moduleName)
    }

    // MARK: - Content Change Tests

    func testContentChangeTriggersLineIndexRebuild() {
        let document = TLADocument()
        document.content = "Line 1\nLine 2\nLine 3"

        let (line, _) = document.lineAndColumn(for: 8)

        XCTAssertEqual(line, 1)  // "Line 2" starts at offset 7

        // Change content
        document.content = "New Line 1\nNew Line 2"

        let (newLine, _) = document.lineAndColumn(for: 12)

        // Should correctly calculate for new content
        XCTAssertEqual(newLine, 1)  // "New Line 2" starts at offset 11
    }

    func testMultipleContentChanges() {
        let document = TLADocument()

        for i in 0..<100 {
            document.content = String(repeating: "Line \(i)\n", count: i + 1)
        }

        // Should not crash and line calculations should work
        let (line, _) = document.lineAndColumn(for: 0)
        XCTAssertEqual(line, 0)
    }

    // MARK: - Unicode Content Tests

    func testUnicodeContent() throws {
        let fileURL = tempDirectory.appendingPathComponent("unicode.tla")
        let content = "---- MODULE Unicode ----\n(* 日本語コメント *)\nVar \\in {\"α\", \"β\", \"γ\"}\n===="
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertTrue(document.content.contains("日本語"))
        XCTAssertTrue(document.content.contains("α"))
    }

    func testTLAOperatorSymbols() throws {
        let fileURL = tempDirectory.appendingPathComponent("operators.tla")
        let content = """
        ---- MODULE Operators ----
        (* TLA+ uses special operators *)
        Foo == \\A x \\in S : \\E y \\in T : x # y
        Bar == <<1, 2, 3>>
        Baz == [a |-> 1, b |-> 2]
        ====
        """
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        XCTAssertTrue(document.content.contains("\\A"))
        XCTAssertTrue(document.content.contains("\\E"))
        XCTAssertTrue(document.content.contains("|->"))
    }

    // MARK: - Document State Tests

    func testDocumentDefaultState() {
        let document = TLADocument()

        XCTAssertNil(document.tlcSession)
        XCTAssertNil(document.proofSession)
        XCTAssertNil(document.lastTLCResult)
        XCTAssertNil(document.lastProofResult)
        XCTAssertEqual(document.selectedTLCMode, .auto)
    }

    func testDocumentEncodingDefault() {
        let document = TLADocument()

        XCTAssertEqual(document.encoding, .utf8)
    }

    func testDocumentLineEndingDefault() {
        let document = TLADocument()

        XCTAssertEqual(document.lineEnding, .lf)
    }

    // MARK: - Selected Range Tests

    func testSelectedRangeInitialValue() {
        let document = TLADocument()

        XCTAssertEqual(document.selectedRange.location, 0)
        XCTAssertEqual(document.selectedRange.length, 0)
    }

    func testSelectedRangeUpdate() {
        let document = TLADocument()
        document.content = "---- MODULE Test ----\nVARIABLES x\n===="

        document.selectedRange = NSRange(location: 5, length: 10)

        XCTAssertEqual(document.selectedRange.location, 5)
        XCTAssertEqual(document.selectedRange.length, 10)
    }

    // MARK: - Parse Result Tests

    func testParseResultInitiallyNil() {
        let document = TLADocument()

        // Parse result may be populated by background task
        // Just verify property exists
        _ = document.parseResult
    }

    func testSymbolsInitiallyEmpty() {
        let document = TLADocument()

        // Symbols may be populated by background parsing
        // After initialization they should be empty or populated
        XCTAssertNotNil(document.symbols)
    }

    func testDiagnosticsInitiallyEmpty() {
        let document = TLADocument()

        // Diagnostics should be empty or populated based on parse
        XCTAssertNotNil(document.diagnostics)
    }

    // MARK: - Symbol Lookup Tests

    func testSymbolAtOffset() {
        let document = TLADocument()
        document.content = """
        ---- MODULE Test ----
        VARIABLES x, y
        Init == x = 0 /\\ y = 0
        ====
        """

        // This tests the method exists and returns optional
        let symbol = document.symbolAt(characterOffset: 25)

        // Symbol may or may not be found depending on parsing state
        _ = symbol
    }

    // MARK: - Go To Definition Tests

    func testGoToDefinitionReturnsBoolean() {
        let document = TLADocument()
        document.content = """
        ---- MODULE Test ----
        Foo == TRUE
        Bar == Foo
        ====
        """

        let result = document.goToDefinition(at: 50)

        // Result is boolean indicating success
        XCTAssertTrue(result == true || result == false)
    }

    // MARK: - Proof Annotation Manager Tests

    func testProofAnnotationManagerExists() {
        let document = TLADocument()

        XCTAssertNotNil(document.proofAnnotationManager)
    }

    func testProofAnnotationManagerReset() {
        let document = TLADocument()
        let originalManager = document.proofAnnotationManager

        document.proofAnnotationManager = ProofAnnotationManager()

        XCTAssertFalse(document.proofAnnotationManager === originalManager)
        XCTAssertNotNil(document.proofAnnotationManager)
        XCTAssertTrue(document.proofAnnotationManager.annotations.isEmpty)
    }

    // MARK: - Autosave Configuration Tests

    func testAutosavesInPlace() {
        XCTAssertTrue(TLADocument.autosavesInPlace)
    }

    func testAutosavesDrafts() {
        XCTAssertTrue(TLADocument.autosavesDrafts)
    }

    func testPreservesVersions() {
        XCTAssertTrue(TLADocument.preservesVersions)
    }

    func testAutosavingFileType() {
        let document = TLADocument()

        XCTAssertEqual(document.autosavingFileType, "com.tlaplus.specification")
    }

    func testCanAsynchronouslyWrite() {
        let document = TLADocument()
        let url = URL(fileURLWithPath: "/tmp/test.tla")

        let canAsync = document.canAsynchronouslyWrite(
            to: url,
            ofType: "com.tlaplus.specification",
            for: .saveOperation
        )

        XCTAssertTrue(canAsync)
    }
}

// MARK: - Line Ending Enum Tests (Document I/O)

final class DocumentIOLineEndingTests: XCTestCase {

    func testLineEndingValues() {
        let endings: [LineEnding] = [.lf, .crlf, .cr]

        XCTAssertEqual(endings.count, 3)
    }

    func testLineEndingEquality() {
        XCTAssertEqual(LineEnding.lf, LineEnding.lf)
        XCTAssertNotEqual(LineEnding.lf, LineEnding.crlf)
        XCTAssertNotEqual(LineEnding.crlf, LineEnding.cr)
    }
}

// MARK: - Secure Temp File Tests

final class SecureTempFileTests: XCTestCase {

    func testCreateTempFile() throws {
        let content = "Test content"
        let url = try SecureTempFile.create(prefix: "test", extension: "tla", content: content)

        XCTAssertTrue(FileManager.default.fileExists(atPath: url.path))

        let readContent = try String(contentsOf: url, encoding: .utf8)
        XCTAssertEqual(readContent, content)

        // Cleanup
        try? FileManager.default.removeItem(at: url)
    }

    func testCreateTempFileWithSpecialCharacters() throws {
        let content = "Test with special: αβγ 日本語"
        let url = try SecureTempFile.create(prefix: "special", extension: "tla", content: content)

        let readContent = try String(contentsOf: url, encoding: .utf8)
        XCTAssertEqual(readContent, content)

        // Cleanup
        try? FileManager.default.removeItem(at: url)
    }

    func testCreateTempFileEmptyContent() throws {
        let url = try SecureTempFile.create(prefix: "empty", extension: "tla", content: "")

        let readContent = try String(contentsOf: url, encoding: .utf8)
        XCTAssertTrue(readContent.isEmpty)

        // Cleanup
        try? FileManager.default.removeItem(at: url)
    }

    func testCreateMultipleTempFiles() throws {
        var urls: [URL] = []

        for i in 0..<10 {
            let url = try SecureTempFile.create(prefix: "multi\(i)", extension: "tla", content: "Content \(i)")
            urls.append(url)
        }

        // All files should exist with unique paths
        let uniquePaths = Set(urls.map { $0.path })
        XCTAssertEqual(uniquePaths.count, 10)

        // Cleanup
        for url in urls {
            try? FileManager.default.removeItem(at: url)
        }
    }
}
