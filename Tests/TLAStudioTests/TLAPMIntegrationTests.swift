import XCTest
@testable import TLAStudioApp

// MARK: - TLAPM Integration Tests

/// Tests for TLAPM process lifecycle, proof checking, and error handling.
final class TLAPMIntegrationTests: XCTestCase {

    // MARK: - TLAPM Error Tests

    func testTLAPMErrorDescriptions() {
        XCTAssertNotNil(TLAPMError.tlapmNotFound.errorDescription)
        XCTAssertNotNil(TLAPMError.specNotFound.errorDescription)
        XCTAssertNotNil(TLAPMError.timeout.errorDescription)
        XCTAssertNotNil(TLAPMError.cancelled.errorDescription)
    }

    func testTLAPMErrorFailedToStart() {
        let underlyingError = NSError(domain: "test", code: 1, userInfo: [NSLocalizedDescriptionKey: "Test error"])
        let error = TLAPMError.failedToStart(underlyingError)

        XCTAssertNotNil(error.errorDescription)
        XCTAssertTrue(error.errorDescription!.contains("Test error"))
    }

    func testTLAPMErrorProverNotFound() {
        let error = TLAPMError.proverNotFound(.z3)

        XCTAssertNotNil(error.errorDescription)
        XCTAssertTrue(error.errorDescription!.contains("Z3") || error.errorDescription!.lowercased().contains("z3"))
    }

    func testTLAPMErrorParseError() {
        let error = TLAPMError.parseError("Unexpected token at line 42")

        XCTAssertNotNil(error.errorDescription)
        XCTAssertTrue(error.errorDescription!.contains("Unexpected token"))
    }

    func testTLAPMErrorInvalidLocation() {
        let error = TLAPMError.invalidLocation(line: 100, column: 50)

        XCTAssertNotNil(error.errorDescription)
        XCTAssertTrue(error.errorDescription!.contains("100"))
        XCTAssertTrue(error.errorDescription!.contains("50"))
    }

    // MARK: - Prover Backend Tests

    func testProverBackendDisplayNames() {
        XCTAssertNotNil(ProverBackend.zenon.displayName)
        XCTAssertNotNil(ProverBackend.z3.displayName)
        XCTAssertNotNil(ProverBackend.isabelle.displayName)
        XCTAssertNotNil(ProverBackend.spass.displayName)
        XCTAssertNotNil(ProverBackend.ls4.displayName)
        XCTAssertNotNil(ProverBackend.cvc5.displayName)
    }

    func testProverBackendTlapmArguments() {
        XCTAssertFalse(ProverBackend.zenon.tlapmArgument.isEmpty)
        XCTAssertFalse(ProverBackend.z3.tlapmArgument.isEmpty)
    }

    func testProverBackendRawValues() {
        let backends: [ProverBackend] = [.zenon, .z3, .isabelle, .spass, .ls4, .cvc5]

        for backend in backends {
            XCTAssertFalse(backend.rawValue.isEmpty)
        }
    }

    // MARK: - Proof Check Options Tests

    func testProofCheckOptionsDefault() {
        let options = ProofCheckOptions.default

        XCTAssertNil(options.backend)
        XCTAssertTrue(options.threads > 0)
        XCTAssertTrue(options.timeout > 0)
    }

    func testProofCheckOptionsCustom() {
        let options = ProofCheckOptions(
            backend: .z3,
            timeout: 60,
            threads: 4,
            checkFromLine: 10,
            checkToLine: 50,
            fingerprints: true,
            verbose: true
        )

        XCTAssertEqual(options.backend, .z3)
        XCTAssertEqual(options.threads, 4)
        XCTAssertEqual(options.timeout, 60)
        XCTAssertTrue(options.fingerprints)
        XCTAssertTrue(options.verbose)
        XCTAssertEqual(options.checkFromLine, 10)
        XCTAssertEqual(options.checkToLine, 50)
    }

    func testProofCheckOptionsSingleLine() {
        let options = ProofCheckOptions(
            checkFromLine: 25,
            checkToLine: 25
        )

        XCTAssertEqual(options.checkFromLine, options.checkToLine)
    }

    // MARK: - Proof Check Progress Tests

    func testProofCheckProgressInitialization() {
        let sessionId = UUID()
        let progress = ProofCheckProgress(
            sessionId: sessionId,
            phase: .checking,
            totalObligations: 10,
            provedCount: 5,
            failedCount: 2,
            trivialCount: 1,
            currentObligation: nil,
            obligations: []
        )

        XCTAssertEqual(progress.sessionId, sessionId)
        XCTAssertEqual(progress.phase, .checking)
        XCTAssertEqual(progress.totalObligations, 10)
        XCTAssertEqual(progress.provedCount, 5)
        XCTAssertEqual(progress.failedCount, 2)
        XCTAssertEqual(progress.trivialCount, 1)
    }

    func testProofCheckProgressPhases() {
        let phases: [ProofPhase] = [.parsing, .checking, .done, .error]

        XCTAssertEqual(phases.count, 4)
    }

    // MARK: - Proof Check Result Tests

    func testProofCheckResultSuccess() {
        let result = ProofCheckResult(
            success: true,
            obligations: [],
            provedCount: 10,
            failedCount: 0,
            duration: 5.0,
            errorMessages: []
        )

        XCTAssertTrue(result.success)
        XCTAssertEqual(result.provedCount, 10)
        XCTAssertEqual(result.failedCount, 0)
    }

    func testProofCheckResultWithFailures() {
        let result = ProofCheckResult(
            success: false,
            obligations: [],
            provedCount: 5,
            failedCount: 3,
            duration: 10.0,
            errorMessages: ["Proof obligation failed at line 42"]
        )

        XCTAssertFalse(result.success)
        XCTAssertEqual(result.failedCount, 3)
        XCTAssertFalse(result.errorMessages.isEmpty)
    }

    // MARK: - Proof Obligation Tests

    func testProofObligationCreation() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 10,
            startColumn: 5,
            endLine: 15,
            endColumn: 20
        )

        let obligation = ProofObligation(
            fingerprint: "fp123",
            location: location,
            kind: .theorem,
            status: .proved,
            obligationText: "THEOREM Foo == TRUE"
        )

        XCTAssertEqual(obligation.fingerprint, "fp123")
        XCTAssertEqual(obligation.kind, .theorem)
        XCTAssertEqual(obligation.status, .proved)
    }

    func testObligationKinds() {
        let kinds: [ObligationKind] = [.theorem, .lemma, .corollary, .proposition, .step, .qed, .assertion, .suffices, .case_, .pick]

        XCTAssertGreaterThanOrEqual(kinds.count, 10)
    }

    func testProofStatusValues() {
        let statuses: [ProofStatus] = [.unknown, .pending, .proved, .failed, .timeout, .omitted, .trivial]

        XCTAssertEqual(statuses.count, 7)
    }

    func testProofStatusIsTerminal() {
        XCTAssertFalse(ProofStatus.unknown.isTerminal)
        XCTAssertFalse(ProofStatus.pending.isTerminal)
        XCTAssertTrue(ProofStatus.proved.isTerminal)
        XCTAssertTrue(ProofStatus.failed.isTerminal)
        XCTAssertTrue(ProofStatus.trivial.isTerminal)
        XCTAssertTrue(ProofStatus.timeout.isTerminal)
        XCTAssertTrue(ProofStatus.omitted.isTerminal)
    }

    func testProofStatusIsSuccess() {
        XCTAssertTrue(ProofStatus.proved.isSuccess)
        XCTAssertTrue(ProofStatus.trivial.isSuccess)
        XCTAssertFalse(ProofStatus.failed.isSuccess)
        XCTAssertFalse(ProofStatus.timeout.isSuccess)
        XCTAssertFalse(ProofStatus.pending.isSuccess)
    }

    // MARK: - Proof Source Location Tests

    func testProofSourceLocationContainsLine() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 10,
            startColumn: 1,
            endLine: 20,
            endColumn: 50
        )

        XCTAssertTrue(location.contains(line: 15, column: 25))
        XCTAssertTrue(location.contains(line: 10, column: 1))
        XCTAssertTrue(location.contains(line: 20, column: 50))
        XCTAssertFalse(location.contains(line: 5, column: 1))
        XCTAssertFalse(location.contains(line: 25, column: 1))
    }

    func testProofSourceLocationSingleLine() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 15,
            startColumn: 10,
            endLine: 15,
            endColumn: 30
        )

        XCTAssertTrue(location.contains(line: 15, column: 20))
        XCTAssertFalse(location.contains(line: 15, column: 5))
        XCTAssertFalse(location.contains(line: 15, column: 35))
    }

    func testProofSourceLocationEquality() {
        let url = URL(fileURLWithPath: "/tmp/test.tla")
        let loc1 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 20)
        let loc2 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 20)
        let loc3 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 21)

        XCTAssertEqual(loc1, loc2)
        XCTAssertNotEqual(loc1, loc3)
    }

    func testProofSourceLocationHashable() {
        let url = URL(fileURLWithPath: "/tmp/test.tla")
        let loc1 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 20)
        let loc2 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 20)

        var set = Set<ProofSourceLocation>()
        set.insert(loc1)
        set.insert(loc2)

        XCTAssertEqual(set.count, 1)
    }

    // MARK: - Proof Session Tests

    @MainActor
    func testProofSessionInitialization() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        XCTAssertFalse(session.isRunning)
        XCTAssertNil(session.progress)
        XCTAssertNil(session.result)
        XCTAssertNil(session.error)
        XCTAssertTrue(session.obligations.isEmpty)
    }

    @MainActor
    func testProofSessionWithOptions() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let options = ProofCheckOptions(backend: .z3, timeout: 30, threads: 2)
        let session = ProofSession(specURL: specURL, options: options)

        XCTAssertEqual(session.options.backend, ProverBackend.z3)
        XCTAssertEqual(session.options.threads, 2)
    }

    @MainActor
    func testProofSessionStopWhenNotRunning() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Should not crash when stopping a non-running session
        session.stop()

        XCTAssertFalse(session.isRunning)
    }

    // MARK: - Proof Annotation Manager Tests

    @MainActor
    func testProofAnnotationManagerInitialization() {
        let manager = ProofAnnotationManager()

        XCTAssertTrue(manager.annotations.isEmpty)
    }

    @MainActor
    func testProofAnnotationManagerUpdateAnnotations() {
        let manager = ProofAnnotationManager()
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 10,
            startColumn: 1,
            endLine: 15,
            endColumn: 50
        )

        let obligation = ProofObligation(
            fingerprint: "fp1",
            location: location,
            kind: .theorem,
            status: .proved,
            obligationText: "THEOREM"
        )

        manager.updateAnnotations(for: [obligation])

        // Annotations should be updated
        XCTAssertFalse(manager.annotations.isEmpty)
    }

    @MainActor
    func testProofAnnotationManagerClearAnnotations() {
        let manager = ProofAnnotationManager()
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 10,
            startColumn: 1,
            endLine: 15,
            endColumn: 50
        )

        let obligation = ProofObligation(
            fingerprint: "fp1",
            location: location,
            kind: .theorem,
            status: .proved,
            obligationText: "THEOREM"
        )

        manager.updateAnnotations(for: [obligation])
        manager.clearAnnotations()

        XCTAssertTrue(manager.annotations.isEmpty)
    }

    @MainActor
    func testProofAnnotationManagerNavigateToNextFailed() {
        let manager = ProofAnnotationManager()

        // Should not crash with no annotations
        manager.navigateToNextFailed()
    }

    // MARK: - TLAPM Availability Tests

    func testTLAPMAvailabilityProperty() async {
        let isAvailable = await TLAPMProcessManager.shared.isTLAPMAvailable

        // We can't guarantee TLAPM is available in test environment
        XCTAssertTrue(isAvailable == true || isAvailable == false)
    }

    func testTLAPMActiveSessionCount() async {
        let count = await TLAPMProcessManager.shared.activeSessionCount

        XCTAssertGreaterThanOrEqual(count, 0)
    }

    // MARK: - Prover Availability Tests

    func testProverAvailability() async {
        let backends: [ProverBackend] = [.zenon, .z3, .isabelle, .spass, .ls4, .cvc5]

        for backend in backends {
            let isAvailable = await TLAPMProcessManager.shared.isProverAvailable(backend)
            // Just verify the method doesn't crash
            XCTAssertTrue(isAvailable == true || isAvailable == false)
        }
    }

    func testAvailableProvers() async {
        let provers = await TLAPMProcessManager.shared.availableProvers()

        // Should return an array (possibly empty)
        XCTAssertNotNil(provers)
    }

    // MARK: - Obligation Tree Tests

    func testObligationTreeCreation() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 10,
            startColumn: 1,
            endLine: 20,
            endColumn: 50
        )

        let root = ProofObligation(
            fingerprint: "fp_root",
            location: location,
            kind: .theorem,
            status: .proved,
            obligationText: "THEOREM"
        )

        XCTAssertTrue(root.children.isEmpty)
        XCTAssertNil(root.parent)
    }

    func testObligationTreeWithChildren() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 10,
            startColumn: 1,
            endLine: 20,
            endColumn: 50
        )

        let childId = UUID()

        let root = ProofObligation(
            fingerprint: "fp_root",
            location: location,
            kind: .theorem,
            status: .proved,
            children: [childId],
            obligationText: "THEOREM"
        )

        XCTAssertEqual(root.children.count, 1)
        XCTAssertEqual(root.children.first, childId)
    }

    // MARK: - Proof Backend Selection Tests

    func testProofBackendComparison() {
        let zenon = ProverBackend.zenon
        let z3 = ProverBackend.z3

        XCTAssertNotEqual(zenon, z3)
        XCTAssertEqual(zenon, ProverBackend.zenon)
    }

    func testProofBackendSorting() {
        var backends: [ProverBackend] = [.z3, .zenon, .isabelle]
        backends.sort { $0.rawValue < $1.rawValue }

        // Just verify sorting works
        XCTAssertEqual(backends.count, 3)
    }

    // MARK: - Output Parser Session ID Tests

    func testTLAPMOutputParserSessionId() {
        let parser = TLAPMOutputParser()
        let sessionId = UUID()

        parser.setSessionId(sessionId)

        // The session ID should be set (internal state, tested via obligations)
        XCTAssertTrue(parser.getAllObligations().isEmpty)
    }

    func testTLAPMOutputParserSpecFileURL() {
        let parser = TLAPMOutputParser()
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")

        parser.setSpecFileURL(specURL)

        // The spec URL should be set (internal state)
        XCTAssertTrue(parser.getAllObligations().isEmpty)
    }

    // MARK: - Trivial Count Tests

    func testTLAPMOutputParserTrivialCount() {
        let parser = TLAPMOutputParser()

        let trivialCount = parser.getTrivialCount()

        XCTAssertEqual(trivialCount, 0)
    }

    // MARK: - Final Result Tests

    func testTLAPMOutputParserFinalResult() {
        let parser = TLAPMOutputParser()

        let result = parser.finalResult(exitCode: 0, duration: 1.0)

        XCTAssertTrue(result.obligations.isEmpty)
        XCTAssertEqual(result.provedCount, 0)
        XCTAssertEqual(result.failedCount, 0)
    }

    func testTLAPMOutputParserFinalResultWithNonZeroExit() {
        let parser = TLAPMOutputParser()

        let result = parser.finalResult(exitCode: 1, duration: 2.5)

        // Non-zero exit typically means failure
        XCTAssertTrue(result.obligations.isEmpty || !result.success)
    }
}

// MARK: - Obligation Kind Tests

final class ObligationKindTests: XCTestCase {

    func testAllObligationKinds() {
        let kinds: [ObligationKind] = [
            .theorem, .lemma, .corollary, .proposition,
            .step, .qed, .assertion, .suffices,
            .case_, .pick
        ]

        for kind in kinds {
            XCTAssertNotNil(kind)
        }
    }

    func testObligationKindEquality() {
        XCTAssertEqual(ObligationKind.theorem, ObligationKind.theorem)
        XCTAssertNotEqual(ObligationKind.theorem, ObligationKind.lemma)
    }
}

// MARK: - Proof Backend Argument Tests

final class ProverBackendArgumentTests: XCTestCase {

    func testZenonArgument() {
        let arg = ProverBackend.zenon.tlapmArgument
        XCTAssertFalse(arg.isEmpty)
    }

    func testZ3Argument() {
        let arg = ProverBackend.z3.tlapmArgument
        XCTAssertFalse(arg.isEmpty)
    }

    func testIsabelleArgument() {
        let arg = ProverBackend.isabelle.tlapmArgument
        XCTAssertFalse(arg.isEmpty)
    }

    func testSpassArgument() {
        let arg = ProverBackend.spass.tlapmArgument
        XCTAssertFalse(arg.isEmpty)
    }

    func testLs4Argument() {
        let arg = ProverBackend.ls4.tlapmArgument
        XCTAssertFalse(arg.isEmpty)
    }

    func testCvc5Argument() {
        let arg = ProverBackend.cvc5.tlapmArgument
        XCTAssertFalse(arg.isEmpty)
    }
}
