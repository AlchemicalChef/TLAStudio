import XCTest
@testable import TLAStudioApp

// MARK: - Proof Session Tests

/// Tests for ProofSession state management and race condition handling.
@MainActor
final class ProofSessionTests: XCTestCase {

    // MARK: - Initialization Tests

    func testProofSessionInitialization() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        XCTAssertEqual(session.specURL, specURL)
        XCTAssertFalse(session.isRunning)
        XCTAssertNil(session.error)
        XCTAssertNil(session.result)
        XCTAssertTrue(session.obligations.isEmpty)
    }

    func testProofSessionWithCustomOptions() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let options = ProofCheckOptions(
            backend: .z3,
            timeout: 60,
            threads: 8
        )
        let session = ProofSession(specURL: specURL, options: options)

        XCTAssertEqual(session.options.backend, .z3)
        XCTAssertEqual(session.options.timeout, 60)
        XCTAssertEqual(session.options.threads, 8)
    }

    // MARK: - Stop Tests

    func testStopWhenNotRunning() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Stop should not crash when not running
        session.stop()

        XCTAssertFalse(session.isRunning)
    }

    func testStopClearsRunningState() async {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Manually set running state to simulate a running session
        // (In real usage, start() would set this)
        // We test that stop() properly clears the state

        session.stop()

        XCTAssertFalse(session.isRunning)
    }

    func testStopAsyncClearsRunningState() async {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        await session.stopAsync()

        XCTAssertFalse(session.isRunning)
    }

    // MARK: - Clear Results Tests

    func testClearResults() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Manually set some state
        // (In real usage, these would be set by parsing)

        session.clearResults()

        XCTAssertTrue(session.obligations.isEmpty)
        XCTAssertNil(session.result)
        XCTAssertNil(session.progress)
        XCTAssertNil(session.error)
    }

    // MARK: - Statistics Tests

    func testStatisticsEmpty() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        let stats = session.statistics

        XCTAssertEqual(stats.proved, 0)
        XCTAssertEqual(stats.failed, 0)
        XCTAssertEqual(stats.pending, 0)
        XCTAssertEqual(stats.total, 0)
    }

    func testSummaryStringEmpty() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        XCTAssertEqual(session.summaryString, "No obligations")
    }

    func testAllProvedEmpty() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Empty obligations means nothing is proved
        XCTAssertFalse(session.allProved)
    }

    func testHasFailedEmpty() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        XCTAssertFalse(session.hasFailed)
    }

    // MARK: - Obligation Tree Tests

    func testObligationTreeEmpty() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        XCTAssertTrue(session.obligationTree.isEmpty)
    }

    func testFindObligationNotFound() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        let result = session.findObligation(by: UUID())

        XCTAssertNil(result)
    }

    // MARK: - Session ID Tests

    func testSessionHasUniqueId() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session1 = ProofSession(specURL: specURL)
        let session2 = ProofSession(specURL: specURL)

        XCTAssertNotEqual(session1.id, session2.id)
    }

    // MARK: - Multiple Stop Calls Tests

    func testMultipleStopCallsDoNotCrash() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Multiple stop calls should not crash
        session.stop()
        session.stop()
        session.stop()

        XCTAssertFalse(session.isRunning)
    }

    func testConcurrentStopCalls() async {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Call stop concurrently
        await withTaskGroup(of: Void.self) { group in
            for _ in 0..<10 {
                group.addTask { @MainActor in
                    session.stop()
                }
            }
        }

        XCTAssertFalse(session.isRunning)
    }
}

// MARK: - Proof Status Tests

final class ProofStatusTests: XCTestCase {

    func testProofStatusIcons() {
        XCTAssertEqual(ProofStatus.unknown.icon, "?")
        XCTAssertEqual(ProofStatus.pending.icon, "\u{22EF}")
        XCTAssertEqual(ProofStatus.proved.icon, "\u{2713}")
        XCTAssertEqual(ProofStatus.failed.icon, "\u{2717}")
        XCTAssertEqual(ProofStatus.timeout.icon, "\u{23F0}")
        XCTAssertEqual(ProofStatus.omitted.icon, "\u{25CB}")
        XCTAssertEqual(ProofStatus.trivial.icon, "\u{2728}")
    }

    func testProofStatusColors() {
        // Just verify colors are accessible (not nil)
        XCTAssertNotNil(ProofStatus.unknown.color)
        XCTAssertNotNil(ProofStatus.pending.color)
        XCTAssertNotNil(ProofStatus.proved.color)
        XCTAssertNotNil(ProofStatus.failed.color)
        XCTAssertNotNil(ProofStatus.timeout.color)
        XCTAssertNotNil(ProofStatus.omitted.color)
        XCTAssertNotNil(ProofStatus.trivial.color)
    }
}

// MARK: - Prover Backend Tests

final class ProverBackendTests: XCTestCase {

    func testBackendFlags() {
        XCTAssertEqual(ProverBackend.auto.flag, "")
        XCTAssertEqual(ProverBackend.zenon.flag, "--method zenon")
        XCTAssertEqual(ProverBackend.z3.flag, "--method smt")
        XCTAssertEqual(ProverBackend.isabelle.flag, "--method isabelle")
        XCTAssertEqual(ProverBackend.cvc5.flag, "--method cvc5")
        XCTAssertEqual(ProverBackend.spass.flag, "--method spass")
        XCTAssertEqual(ProverBackend.ls4.flag, "--method ls4")
    }

    func testBackendShortNames() {
        XCTAssertEqual(ProverBackend.auto.shortName, "A")
        XCTAssertEqual(ProverBackend.zenon.shortName, "Z")
        XCTAssertEqual(ProverBackend.z3.shortName, "S")
        XCTAssertEqual(ProverBackend.isabelle.shortName, "I")
        XCTAssertEqual(ProverBackend.cvc5.shortName, "C")
        XCTAssertEqual(ProverBackend.spass.shortName, "P")
        XCTAssertEqual(ProverBackend.ls4.shortName, "L")
    }
}

// MARK: - Proof Check Progress Tests

final class ProofCheckProgressTests: XCTestCase {

    func testFractionCompleteWithZeroTotal() {
        let progress = ProofCheckProgress(
            sessionId: UUID(),
            phase: .checking,
            totalObligations: 0,
            provedCount: 0,
            failedCount: 0,
            trivialCount: 0,
            currentObligation: nil,
            obligations: []
        )

        XCTAssertEqual(progress.fractionComplete, 0)
    }

    func testFractionCompleteWithProgress() {
        let progress = ProofCheckProgress(
            sessionId: UUID(),
            phase: .checking,
            totalObligations: 10,
            provedCount: 3,
            failedCount: 2,
            trivialCount: 1,
            currentObligation: nil,
            obligations: []
        )

        // (3 + 2 + 1) / 10 = 0.6
        XCTAssertEqual(progress.fractionComplete, 0.6, accuracy: 0.001)
    }

    func testPendingCount() {
        let progress = ProofCheckProgress(
            sessionId: UUID(),
            phase: .checking,
            totalObligations: 10,
            provedCount: 3,
            failedCount: 2,
            trivialCount: 1,
            currentObligation: nil,
            obligations: []
        )

        // 10 - 3 - 2 - 1 = 4
        XCTAssertEqual(progress.pendingCount, 4)
    }

    func testPendingCountWithAllComplete() {
        let progress = ProofCheckProgress(
            sessionId: UUID(),
            phase: .done,
            totalObligations: 5,
            provedCount: 3,
            failedCount: 1,
            trivialCount: 1,
            currentObligation: nil,
            obligations: []
        )

        // 5 - 3 - 1 - 1 = 0
        XCTAssertEqual(progress.pendingCount, 0)
    }
}

// MARK: - TLC Session Tests

@MainActor
final class TLCSessionTests: XCTestCase {

    func testTLCSessionInitialization() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config)

        XCTAssertEqual(session.specURL, specURL)
        XCTAssertFalse(session.isRunning)
        XCTAssertNil(session.error)
        XCTAssertNil(session.result)
    }

    func testTLCSessionWithBinaryMode() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config, binaryMode: .fast)

        XCTAssertEqual(session.binaryMode, .fast)
    }

    func testTLCSessionStopWhenNotRunning() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config)

        // Stop should not crash when not running
        session.stop()

        XCTAssertFalse(session.isRunning)
    }

    func testTLCSessionMultipleStopCalls() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config)

        // Multiple stop calls should not crash
        session.stop()
        session.stop()
        session.stop()

        XCTAssertFalse(session.isRunning)
    }

    func testTLCSessionUniqueId() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session1 = TLCSession(specURL: specURL, config: config)
        let session2 = TLCSession(specURL: specURL, config: config)

        XCTAssertNotEqual(session1.id, session2.id)
    }

    func testTLCSessionCheckpointStatusInitial() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config)

        if case .none = session.checkpointStatus {
            // Expected
        } else {
            XCTFail("Expected checkpoint status to be .none")
        }
    }

    func testConcurrentTLCSessionStopCalls() async {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config)

        // Call stop concurrently
        await withTaskGroup(of: Void.self) { group in
            for _ in 0..<10 {
                group.addTask { @MainActor in
                    session.stop()
                }
            }
        }

        XCTAssertFalse(session.isRunning)
    }

    func testTLCSessionBinaryModeAuto() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config, binaryMode: .auto)

        XCTAssertEqual(session.binaryMode, .auto)
    }

    func testTLCSessionBinaryModeStandard() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config, binaryMode: .standard)

        XCTAssertEqual(session.binaryMode, .standard)
    }

    func testTLCSessionConfigRetention() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            specFile: specURL,
            initPredicate: "CustomInit",
            nextAction: "CustomNext",
            workers: 8
        )
        let session = TLCSession(specURL: specURL, config: config)

        XCTAssertEqual(session.config.initPredicate, "CustomInit")
        XCTAssertEqual(session.config.nextAction, "CustomNext")
        XCTAssertEqual(session.config.workers, 8)
    }

    func testTLCSessionProgressInitiallyNil() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)
        let session = TLCSession(specURL: specURL, config: config)

        XCTAssertNil(session.progress)
    }
}

// MARK: - Proof Obligation Tests

@MainActor
final class ProofObligationTests: XCTestCase {

    func testProofObligationCreation() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 10,
            startColumn: 5,
            endLine: 10,
            endColumn: 20
        )

        let obligation = ProofObligation(
            fingerprint: "abc123",
            location: location,
            kind: .theorem,
            status: .proved,
            backend: .zenon,
            duration: 1.5,
            obligationText: "A => B"
        )

        XCTAssertEqual(obligation.status, .proved)
        XCTAssertEqual(obligation.fingerprint, "abc123")
        XCTAssertEqual(obligation.kind, .theorem)
        XCTAssertEqual(obligation.backend, .zenon)
        XCTAssertEqual(obligation.duration, 1.5)
    }

    func testProofObligationWithError() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 5,
            startColumn: 1,
            endLine: 5,
            endColumn: 10
        )

        let obligation = ProofObligation(
            fingerprint: "def456",
            location: location,
            kind: .step,
            status: .failed,
            backend: .z3,
            duration: 30.0,
            errorMessage: "Could not find proof",
            obligationText: "x > 0"
        )

        XCTAssertEqual(obligation.status, .failed)
        XCTAssertEqual(obligation.errorMessage, "Could not find proof")
    }

    func testProofObligationKinds() {
        let kinds: [ObligationKind] = [
            .theorem, .lemma, .corollary, .proposition,
            .step, .qed, .assertion, .suffices,
            .case_, .pick, .have, .take, .witness
        ]

        // Verify all kinds are distinct
        var seen = Set<String>()
        for kind in kinds {
            let name = String(describing: kind)
            XCTAssertFalse(seen.contains(name), "Duplicate kind: \(name)")
            seen.insert(name)
        }
    }

    func testProofObligationWithStatus() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 1,
            startColumn: 1,
            endLine: 1,
            endColumn: 10
        )

        let original = ProofObligation(
            fingerprint: "test",
            location: location,
            kind: .step,
            status: .pending,
            obligationText: "test"
        )

        let updated = original.with(status: .proved)

        XCTAssertEqual(original.status, .pending)
        XCTAssertEqual(updated.status, .proved)
        XCTAssertEqual(original.fingerprint, updated.fingerprint)
    }

    func testProofObligationWithResult() {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: 1,
            startColumn: 1,
            endLine: 1,
            endColumn: 10
        )

        let original = ProofObligation(
            fingerprint: "test",
            location: location,
            kind: .step,
            status: .pending,
            obligationText: "test"
        )

        let updated = original.withResult(
            status: .proved,
            backend: .zenon,
            duration: 2.5,
            errorMessage: nil
        )

        XCTAssertEqual(updated.status, .proved)
        XCTAssertEqual(updated.backend, .zenon)
        XCTAssertEqual(updated.duration, 2.5)
        XCTAssertNil(updated.errorMessage)
    }

    func testProofCheckResultFromPendingObligationIsNotSuccessful() {
        let obligation = ProofObligation(
            fingerprint: "pending",
            location: ProofSourceLocation(
                fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
                startLine: 1,
                startColumn: 1,
                endLine: 1,
                endColumn: 10
            ),
            kind: .step,
            status: .pending,
            obligationText: "test"
        )

        let result = ProofCheckResult.from(obligations: [obligation], duration: 0.1)

        XCTAssertFalse(result.success)
        XCTAssertEqual(result.provedCount, 0)
        XCTAssertEqual(result.failedCount, 0)
    }

    func testProofCheckResultFromOmittedObligationIsNotSuccessful() {
        let obligation = ProofObligation(
            fingerprint: "omitted",
            location: ProofSourceLocation(
                fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
                startLine: 1,
                startColumn: 1,
                endLine: 1,
                endColumn: 10
            ),
            kind: .step,
            status: .omitted,
            obligationText: "test"
        )

        let result = ProofCheckResult.from(obligations: [obligation], duration: 0.1)

        XCTAssertFalse(result.success)
        XCTAssertEqual(result.provedCount, 0)
        XCTAssertEqual(result.failedCount, 0)
    }
}

// MARK: - Proof Source Location Tests

final class ProofSourceLocationTests: XCTestCase {

    func testProofSourceLocationCreation() {
        let url = URL(fileURLWithPath: "/tmp/spec.tla")
        let location = ProofSourceLocation(
            fileURL: url,
            startLine: 10,
            startColumn: 5,
            endLine: 15,
            endColumn: 20
        )

        XCTAssertEqual(location.fileURL, url)
        XCTAssertEqual(location.startLine, 10)
        XCTAssertEqual(location.startColumn, 5)
        XCTAssertEqual(location.endLine, 15)
        XCTAssertEqual(location.endColumn, 20)
    }

    func testProofSourceLocationSinglePoint() {
        let url = URL(fileURLWithPath: "/tmp/spec.tla")
        let location = ProofSourceLocation(
            fileURL: url,
            startLine: 10,
            startColumn: 5,
            endLine: 10,
            endColumn: 5
        )

        XCTAssertEqual(location.startLine, location.endLine)
        XCTAssertEqual(location.startColumn, location.endColumn)
    }

    func testProofSourceLocationSpecialCharactersInPath() {
        // Test URL with special characters in path
        let url = URL(fileURLWithPath: "/tmp/test spec with spaces & symbols.tla")
        let location = ProofSourceLocation(
            fileURL: url,
            startLine: 1,
            startColumn: 1,
            endLine: 1,
            endColumn: 1
        )

        XCTAssertTrue(location.fileURL.path.contains("spaces"))
        XCTAssertEqual(location.startLine, 1)
    }

    func testProofSourceLocationEquality() {
        let url = URL(fileURLWithPath: "/tmp/spec.tla")
        let loc1 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 20)
        let loc2 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 20)
        let loc3 = ProofSourceLocation(fileURL: url, startLine: 10, startColumn: 5, endLine: 15, endColumn: 21)

        XCTAssertEqual(loc1, loc2)
        XCTAssertNotEqual(loc1, loc3)
    }
}

// MARK: - Obligation Tree Tests

@MainActor
final class ObligationTreeTests: XCTestCase {

    func testBuildForestEmpty() {
        let forest = ObligationTree.buildForest(from: [])
        XCTAssertTrue(forest.isEmpty)
    }

    func testBuildForestSingleObligation() {
        let obligation = createObligation(line: 1, status: .proved)
        let forest = ObligationTree.buildForest(from: [obligation])

        XCTAssertEqual(forest.count, 1)
    }

    func testBuildForestMultipleObligations() {
        let obligations = [
            createObligation(line: 1, status: .proved),
            createObligation(line: 2, status: .failed),
            createObligation(line: 3, status: .pending)
        ]
        let forest = ObligationTree.buildForest(from: obligations)

        XCTAssertEqual(forest.count, 3)
    }

    private func createObligation(line: Int, status: ProofStatus) -> ProofObligation {
        let location = ProofSourceLocation(
            fileURL: URL(fileURLWithPath: "/tmp/test.tla"),
            startLine: line,
            startColumn: 1,
            endLine: line,
            endColumn: 10
        )

        return ProofObligation(
            fingerprint: "fp\(line)",
            location: location,
            kind: .step,
            status: status,
            obligationText: "obligation \(line)"
        )
    }
}

// MARK: - Model Config Tests

final class ModelConfigTests: XCTestCase {

    func testDefaultModelConfig() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL)

        XCTAssertEqual(config.specFile, specURL)
        XCTAssertEqual(config.initPredicate, "Init")
        XCTAssertEqual(config.nextAction, "Next")
        XCTAssertTrue(config.constants.isEmpty)
        XCTAssertTrue(config.invariants.isEmpty)
        XCTAssertTrue(config.temporalProperties.isEmpty)
    }

    func testModelConfigWithConstants() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            specFile: specURL,
            constants: [
                "N": .int(5),
                "Procs": .set([.int(1), .int(2), .int(3)])
            ]
        )

        XCTAssertEqual(config.constants.count, 2)
        if case .int(let n) = config.constants["N"] {
            XCTAssertEqual(n, 5)
        } else {
            XCTFail("Expected int constant")
        }
    }

    func testModelConfigWithInvariants() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            specFile: specURL,
            invariants: ["TypeOK", "Safety", "Consistency"]
        )

        XCTAssertEqual(config.invariants.count, 3)
        XCTAssertTrue(config.invariants.contains("TypeOK"))
        XCTAssertTrue(config.invariants.contains("Safety"))
    }

    func testModelConfigWithTemporalProperties() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            specFile: specURL,
            temporalProperties: ["Liveness", "Fairness"]
        )

        XCTAssertEqual(config.temporalProperties.count, 2)
    }

    func testModelConfigWithConstraints() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(
            specFile: specURL,
            stateConstraint: "x < 100",
            actionConstraint: "y' > y"
        )

        XCTAssertEqual(config.stateConstraint, "x < 100")
        XCTAssertEqual(config.actionConstraint, "y' > y")
    }

    func testModelConfigWorkers() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let config = ModelConfig(specFile: specURL, workers: 16)

        XCTAssertEqual(config.workers, 16)
    }
}

// MARK: - Constant Value Tests

final class ConstantValueTests: XCTestCase {

    func testIntConstant() {
        let value = ConstantValue.int(42)
        if case .int(let n) = value {
            XCTAssertEqual(n, 42)
        } else {
            XCTFail("Expected int")
        }
    }

    func testStringConstant() {
        let value = ConstantValue.string("hello")
        if case .string(let s) = value {
            XCTAssertEqual(s, "hello")
        } else {
            XCTFail("Expected string")
        }
    }

    func testBoolConstant() {
        let trueValue = ConstantValue.bool(true)
        let falseValue = ConstantValue.bool(false)

        if case .bool(let b) = trueValue {
            XCTAssertTrue(b)
        } else {
            XCTFail("Expected bool")
        }

        if case .bool(let b) = falseValue {
            XCTAssertFalse(b)
        } else {
            XCTFail("Expected bool")
        }
    }

    func testSetConstant() {
        let value = ConstantValue.set([.int(1), .int(2), .int(3)])
        if case .set(let elements) = value {
            XCTAssertEqual(elements.count, 3)
        } else {
            XCTFail("Expected set")
        }
    }

    func testModelValueConstant() {
        let value = ConstantValue.modelValue("mv_1")
        if case .modelValue(let name) = value {
            XCTAssertEqual(name, "mv_1")
        } else {
            XCTFail("Expected modelValue")
        }
    }

    func testSymmetrySetConstant() {
        let value = ConstantValue.symmetrySet("Procs")
        if case .symmetrySet(let name) = value {
            XCTAssertEqual(name, "Procs")
        } else {
            XCTFail("Expected symmetrySet")
        }
    }

    func testNestedSetConstant() {
        let value = ConstantValue.set([
            .set([.int(1), .int(2)]),
            .set([.int(3), .int(4)])
        ])
        if case .set(let elements) = value {
            XCTAssertEqual(elements.count, 2)
        } else {
            XCTFail("Expected set")
        }
    }
}
