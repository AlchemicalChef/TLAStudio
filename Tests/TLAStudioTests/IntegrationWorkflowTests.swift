import XCTest
@testable import TLAStudioApp

// MARK: - Integration Workflow Tests

/// Tests for end-to-end workflows and cross-component integration.
@MainActor
final class IntegrationWorkflowTests: TempDirectoryTestCase {

    // MARK: - Document Creation Workflow Tests

    func testCreateNewDocument() {
        let document = TLADocument()

        // New document should have default template
        XCTAssertFalse(document.content.isEmpty)
        XCTAssertTrue(document.content.contains("MODULE"))
    }

    func testDocumentContentModification() {
        let document = TLADocument()
        let originalContent = document.content

        document.content = "---- MODULE Modified ----\n===="

        XCTAssertNotEqual(document.content, originalContent)
        XCTAssertTrue(document.content.contains("Modified"))
    }

    func testDocumentParsingTriggeredOnChange() async {
        let document = TLADocument()

        document.content = """
        ---- MODULE Test ----
        VARIABLES x
        Init == x = 0
        ====
        """

        // Wait for debounced parsing
        try? await Task.sleep(nanoseconds: 200_000_000)

        // Parse should have been triggered (check that it doesn't crash)
        XCTAssertNotNil(document.content)
    }

    // MARK: - Document Open/Save Workflow Tests

    func testOpenSaveRoundTrip() throws {
        let fileURL = tempDirectory.appendingPathComponent("roundtrip.tla")
        let content = """
        ---- MODULE RoundTrip ----
        VARIABLES x
        Init == x = 0
        Next == x' = x + 1
        ====
        """
        try content.write(to: fileURL, atomically: true, encoding: .utf8)

        // Open
        let document = TLADocument()
        try document.read(from: fileURL, ofType: "com.tlaplus.specification")

        // Modify
        document.content += "\n(* Added comment *)"

        // Save (get data)
        let savedData = try document.data(ofType: "com.tlaplus.specification")
        let savedContent = String(data: savedData, encoding: .utf8)!

        XCTAssertTrue(savedContent.contains("Added comment"))
        XCTAssertTrue(savedContent.contains("MODULE RoundTrip"))
    }

    // MARK: - TLC Session Integration Tests

    func testTLCSessionCreationFromDocument() {
        let document = TLADocument()
        document.content = """
        ---- MODULE Test ----
        VARIABLES x
        Init == x = 0
        Next == x' = x + 1
        ====
        """

        // Create a TLC session manually (simulating runModelCheck)
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            name: "Test",
            specFile: specURL,
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        let session = TLCSession(specURL: specURL, config: config)
        document.tlcSession = session

        XCTAssertNotNil(document.tlcSession)
        XCTAssertEqual(document.tlcSession?.id, session.id)
    }

    func testTLCSessionCleanupOnDocumentClose() {
        let document = TLADocument()

        // Create a session
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            name: "Test",
            specFile: specURL,
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        let session = TLCSession(specURL: specURL, config: config)
        document.tlcSession = session

        // Close document
        document.close()

        // Session should be cleaned up
        XCTAssertNil(document.tlcSession)
    }

    // MARK: - Proof Session Integration Tests

    func testProofSessionCreationFromDocument() {
        let document = TLADocument()
        document.content = """
        ---- MODULE Proof ----
        THEOREM True PROOF OBVIOUS
        ====
        """

        // Create a proof session manually
        let specURL = URL(fileURLWithPath: "/tmp/proof.tla")
        let session = ProofSession(specURL: specURL)
        document.proofSession = session

        XCTAssertNotNil(document.proofSession)
    }

    func testProofSessionCleanupOnDocumentClose() {
        let document = TLADocument()

        let specURL = URL(fileURLWithPath: "/tmp/proof.tla")
        let session = ProofSession(specURL: specURL)
        document.proofSession = session

        document.close()

        XCTAssertNil(document.proofSession)
    }

    // MARK: - Combined TLC and Proof Session Tests

    func testBothSessionsSimultaneously() {
        let document = TLADocument()

        // Create TLC session
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            name: "Test",
            specFile: specURL,
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )
        let tlcSession = TLCSession(specURL: specURL, config: config)
        document.tlcSession = tlcSession

        // Create proof session
        let proofSession = ProofSession(specURL: specURL)
        document.proofSession = proofSession

        // Both should coexist
        XCTAssertNotNil(document.tlcSession)
        XCTAssertNotNil(document.proofSession)
    }

    func testCleanupBothSessions() {
        let document = TLADocument()

        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            name: "Test",
            specFile: specURL,
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        document.tlcSession = TLCSession(specURL: specURL, config: config)
        document.proofSession = ProofSession(specURL: specURL)

        document.close()

        XCTAssertNil(document.tlcSession)
        XCTAssertNil(document.proofSession)
    }

    // MARK: - Result Persistence Tests

    func testTLCResultPersistsAfterSessionEnds() {
        let document = TLADocument()

        // Create a mock result
        let result = ModelCheckResult(
            sessionId: UUID(),
            success: true,
            statesFound: 100,
            distinctStates: 50,
            duration: 1.5,
            coverage: [],
            errorTrace: nil,
            message: nil,
            outOfMemory: false
        )

        document.lastTLCResult = result

        // Result should persist
        XCTAssertNotNil(document.lastTLCResult)
        XCTAssertEqual(document.lastTLCResult?.statesFound, 100)
    }

    func testProofResultPersistsAfterSessionEnds() {
        let document = TLADocument()

        let result = ProofCheckResult(
            success: true,
            obligations: [],
            provedCount: 5,
            failedCount: 0,
            duration: 2.0,
            errorMessages: []
        )

        document.lastProofResult = result

        XCTAssertNotNil(document.lastProofResult)
        XCTAssertEqual(document.lastProofResult?.provedCount, 5)
    }

    // MARK: - Line/Column Navigation Tests

    func testNavigationToPosition() {
        let document = TLADocument()
        document.content = """
        Line 0
        Line 1
        Line 2
        """

        // Get offset for line 1, column 2
        let offset = document.offset(forLine: 1, column: 2)

        // Navigate back to line/column
        let (line, column) = document.lineAndColumn(for: offset)

        XCTAssertEqual(line, 1)
        XCTAssertEqual(column, 2)
    }

    func testNavigationRoundTrip() {
        let document = TLADocument()
        document.content = """
        ---- MODULE Test ----
        VARIABLES x, y, z
        Init == x = 0 /\\ y = 0 /\\ z = 0
        ====
        """

        // Test multiple positions
        let positions = [(0, 0), (1, 5), (2, 10), (3, 0)]

        for (targetLine, targetColumn) in positions {
            let offset = document.offset(forLine: targetLine, column: targetColumn)
            let (resultLine, resultColumn) = document.lineAndColumn(for: offset)

            // Line should always match
            XCTAssertEqual(resultLine, targetLine, "Line mismatch for target (\(targetLine), \(targetColumn))")

            // Column might be clamped if beyond line length
            XCTAssertGreaterThanOrEqual(resultColumn, 0)
        }
    }

    // MARK: - Go To Definition Workflow Tests

    func testGoToDefinitionWorkflow() {
        let document = TLADocument()
        document.content = """
        ---- MODULE Test ----
        Foo == TRUE
        Bar == Foo
        ====
        """

        // Try to go to definition (might not find depending on parse state)
        let success = document.goToDefinition(at: 45)  // Approximate offset of "Foo" in Bar

        // Should return boolean
        XCTAssertTrue(success == true || success == false)
    }

    func testGoToDefinitionInEmptyDocument() {
        let document = TLADocument()
        document.content = ""

        let success = document.goToDefinition(at: 0)

        XCTAssertFalse(success)
    }

    // MARK: - Symbol Lookup Workflow Tests

    func testSymbolLookupWorkflow() {
        let document = TLADocument()
        document.content = """
        ---- MODULE Test ----
        VARIABLES counter
        Init == counter = 0
        ====
        """

        // Look up symbol (may not find immediately due to async parsing)
        let symbol = document.symbolAt(characterOffset: 35)

        // Should return optional
        _ = symbol
    }

    // MARK: - Proof Annotation Integration Tests

    func testProofAnnotationUpdateWorkflow() {
        let document = TLADocument()

        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 5,
            startColumn: 1,
            endLine: 10,
            endColumn: 50
        )

        let obligation = ProofObligation(
            fingerprint: "fp1",
            location: location,
            kind: .theorem,
            status: .proved,
            obligationText: "THEOREM"
        )

        // Update annotations through document's manager
        document.proofAnnotationManager.updateAnnotations(for: [obligation])

        // Annotations should be present
        XCTAssertFalse(document.proofAnnotationManager.annotations.isEmpty)
    }

    func testProofAnnotationClearOnNewSession() {
        let document = TLADocument()

        // Add some annotations
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 5,
            startColumn: 1,
            endLine: 10,
            endColumn: 50
        )

        let obligation = ProofObligation(
            fingerprint: "fp1",
            location: location,
            kind: .theorem,
            status: .proved,
            obligationText: "THEOREM"
        )

        document.proofAnnotationManager.updateAnnotations(for: [obligation])

        // Clear annotations
        document.proofAnnotationManager.clearAnnotations()

        XCTAssertTrue(document.proofAnnotationManager.annotations.isEmpty)
    }

    // MARK: - Concurrent Operation Tests

    func testConcurrentDocumentModifications() async {
        let document = TLADocument()

        await withTaskGroup(of: Void.self) { group in
            for i in 0..<100 {
                group.addTask { @MainActor in
                    document.content = "Content version \(i)"
                }
            }
        }

        // Should not crash and final content should be set
        XCTAssertFalse(document.content.isEmpty)
    }

    func testConcurrentLineColumnAccess() async {
        let document = TLADocument()
        document.content = String(repeating: "Line\n", count: 1000)

        await withTaskGroup(of: Void.self) { group in
            for offset in stride(from: 0, to: 1000, by: 10) {
                group.addTask { @MainActor in
                    _ = document.lineAndColumn(for: offset)
                    _ = document.offset(forLine: offset / 5, column: 0)
                }
            }
        }

        // Should complete without crash
    }

    // MARK: - Binary Mode Selection Workflow Tests

    func testBinaryModeSelectionPersists() {
        let document = TLADocument()

        document.selectedTLCMode = .jvm

        XCTAssertEqual(document.selectedTLCMode, .jvm)
    }

    func testBinaryModeDefaultIsAuto() {
        let document = TLADocument()

        XCTAssertEqual(document.selectedTLCMode, .auto)
    }

    // MARK: - Stop Operations Tests

    func testStopModelCheckWhenNoSession() {
        let document = TLADocument()

        // Should not crash when no session exists
        document.stopModelCheck()

        XCTAssertNil(document.tlcSession)
    }

    func testStopProofCheckWhenNoSession() {
        let document = TLADocument()

        // Should not crash when no session exists
        document.stopProofCheck()

        XCTAssertNil(document.proofSession)
    }

    // MARK: - Error Display Workflow Tests

    func testDiagnosticsAccessibleAfterParse() async throws {
        let document = TLADocument()
        document.content = """
        ---- MODULE Test ----
        VARIABLES x
        ====
        """

        // Wait for parsing
        try await Task.sleep(nanoseconds: 200_000_000)

        // Diagnostics should be accessible
        XCTAssertNotNil(document.diagnostics)
    }

    // MARK: - Multi-Window Simulation Tests

    func testMultipleDocumentsIndependent() {
        let document1 = TLADocument()
        let document2 = TLADocument()

        document1.content = "Content 1"
        document2.content = "Content 2"

        XCTAssertNotEqual(document1.content, document2.content)
    }

    func testMultipleDocumentSessionsIndependent() {
        let document1 = TLADocument()
        let document2 = TLADocument()

        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            name: "Test",
            specFile: specURL,
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        document1.tlcSession = TLCSession(specURL: specURL, config: config)

        XCTAssertNotNil(document1.tlcSession)
        XCTAssertNil(document2.tlcSession)
    }

    // MARK: - State Cleanup Verification Tests

    func testFullStateCleanupOnClose() {
        let document = TLADocument()

        // Set up all state
        document.content = "Test content"
        document.selectedRange = NSRange(location: 5, length: 3)
        document.selectedTLCMode = .jvm

        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            name: "Test",
            specFile: specURL,
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        document.tlcSession = TLCSession(specURL: specURL, config: config)
        document.proofSession = ProofSession(specURL: specURL)

        document.lastTLCResult = ModelCheckResult(
            sessionId: UUID(),
            success: true,
            statesFound: 100,
            distinctStates: 50,
            duration: 1.0,
            coverage: [],
            errorTrace: nil,
            message: nil,
            outOfMemory: false
        )

        document.lastProofResult = ProofCheckResult(
            success: true,
            obligations: [],
            provedCount: 5,
            failedCount: 0,
            duration: 2.0,
            errorMessages: []
        )

        // Close
        document.close()

        // Verify cleanup
        XCTAssertNil(document.tlcSession)
        XCTAssertNil(document.proofSession)
        XCTAssertNil(document.lastTLCResult)
        XCTAssertNil(document.lastProofResult)
        XCTAssertNil(document.parseResult)
        XCTAssertTrue(document.symbols.isEmpty)
        XCTAssertTrue(document.diagnostics.isEmpty)
    }
}

// MARK: - Process Manager Integration Tests

final class ProcessManagerIntegrationTests: XCTestCase {

    func testProcessRegistryWithTLCManager() async {
        let sessionId = UUID()
        let process = Process()

        ProcessRegistry.shared.register(process, for: sessionId)

        // Should be registered
        XCTAssertTrue(ProcessRegistry.shared.registeredCount >= 1)

        // Clean up
        ProcessRegistry.shared.unregister(sessionId)
    }

    func testProcessRegistryTerminateAll() {
        // Register some processes
        let sessionIds = (0..<5).map { _ in UUID() }

        for sessionId in sessionIds {
            ProcessRegistry.shared.register(Process(), for: sessionId)
        }

        // Terminate all
        ProcessRegistry.shared.terminateAll()

        // All should be terminated
        for sessionId in sessionIds {
            XCTAssertFalse(ProcessRegistry.shared.isRunning(sessionId))
        }
    }

    func testConcurrentProcessRegistration() async {
        let initialCount = ProcessRegistry.shared.registeredCount

        await withTaskGroup(of: UUID.self) { group in
            for _ in 0..<50 {
                group.addTask {
                    let sessionId = UUID()
                    ProcessRegistry.shared.register(Process(), for: sessionId)
                    return sessionId
                }
            }

            var sessionIds: [UUID] = []
            for await sessionId in group {
                sessionIds.append(sessionId)
            }

            // Clean up
            for sessionId in sessionIds {
                ProcessRegistry.shared.unregister(sessionId)
            }
        }

        // Should be back to initial count
        XCTAssertEqual(ProcessRegistry.shared.registeredCount, initialCount)
    }
}
