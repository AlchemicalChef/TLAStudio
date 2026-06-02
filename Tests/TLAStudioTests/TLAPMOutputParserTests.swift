import XCTest
@testable import TLAStudioApp

// MARK: - TLAPM Output Parser Tests

/// Tests for TLAPMOutputParser that handles TLAPM toolbox output format.
final class TLAPMOutputParserTests: XCTestCase {

    var parser: TLAPMOutputParser!

    override func setUp() {
        super.setUp()
        parser = TLAPMOutputParser()
    }

    override func tearDown() {
        parser = nil
        super.tearDown()
    }

    // MARK: - Helper Methods

    private func makeBlock(type: String, fields: [String: String]) -> Data {
        var lines = ["@!!BEGIN", "@!!type:\(type)"]
        for (key, value) in fields {
            lines.append("@!!\(key):\(value)")
        }
        lines.append("@!!END")
        let block = lines.joined(separator: "\n") + "\n"
        return block.data(using: .utf8)!
    }

    private func parseLine(_ line: String) -> ProofCheckProgress? {
        return parser.parse((line + "\n").data(using: .utf8)!)
    }

    // MARK: - Basic Block Parsing Tests

    func testParseEmptyBlock() {
        let data = "@!!BEGIN\n@!!END\n".data(using: .utf8)!
        let progress = parser.parse(data)
        XCTAssertNil(progress) // Block without type is ignored
    }

    func testParseUnknownBlockType() {
        let data = makeBlock(type: "unknown", fields: [:])
        let progress = parser.parse(data)
        XCTAssertNil(progress)
    }

    // MARK: - Obligation Block Tests

    func testParseObligationBlockBasic() {
        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved"
        ])
        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.totalObligations, 1)
        XCTAssertEqual(progress?.provedCount, 1)
    }

    func testParseObligationBlockWithLocation() {
        let url = URL(fileURLWithPath: "/test/spec.tla")
        parser.setSpecFileURL(url)

        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "loc": "10:5:15:20"
        ])
        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.count, 1)

        let location = obligations.first?.location
        XCTAssertEqual(location?.startLine, 10)
        XCTAssertEqual(location?.startColumn, 5)
        XCTAssertEqual(location?.endLine, 15)
        XCTAssertEqual(location?.endColumn, 20)
    }

    func testParseObligationBlockWithShortLocation() {
        let url = URL(fileURLWithPath: "/test/spec.tla")
        parser.setSpecFileURL(url)

        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "loc": "10:5"
        ])
        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        let obligations = parser.getAllObligations()
        let location = obligations.first?.location
        XCTAssertEqual(location?.startLine, 10)
        XCTAssertEqual(location?.startColumn, 5)
        XCTAssertEqual(location?.endLine, 10)
        XCTAssertEqual(location?.endColumn, 5)
    }

    func testParseObligationBlockWithBackend() {
        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "prover": "zenon"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .zenon)
    }

    func testParseObligationBlockWithDuration() {
        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "duration": "0.234"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        if let duration = obligations.first?.duration {
            XCTAssertEqual(duration, 0.234, accuracy: 0.001)
        } else {
            XCTFail("Expected duration to be set")
        }
    }

    func testParseObligationBlockWithFingerprint() {
        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "fp": "abc123"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.fingerprint, "abc123")
    }

    func testParseObligationBlockWithKind() {
        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "kind": "theorem"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.kind, .theorem)
    }

    func testParseObligationBlockWithText() {
        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "obl": "x > 0 => x >= 0"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.obligationText, "x > 0 => x >= 0")
    }

    func testParseObligationBlockWithReason() {
        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "failed",
            "reason": "Could not find proof"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.errorMessage, "Could not find proof")
    }

    func testParseObligationBlockWithMultilineReasonAndText() {
        let data = """
        @!!BEGIN
        @!!type:obligation
        @!!id:1
        @!!status:failed
        @!!reason:Could not find proof
        backend returned counterexample detail
        @!!obl:
        ASSUME x \\in Nat
        PROVE x >= 0
        @!!END

        """.data(using: .utf8)!

        _ = parser.parse(data)

        let obligation = parser.getAllObligations().first
        XCTAssertEqual(
            obligation?.errorMessage,
            "Could not find proof\nbackend returned counterexample detail"
        )
        XCTAssertEqual(
            obligation?.obligationText,
            "ASSUME x \\in Nat\nPROVE x >= 0"
        )
    }

    func testObligationsNumberDoesNotDoubleCountParsedObligations() {
        let data = """
        @!!BEGIN
        @!!type:obligationsnumber
        @!!count:2
        @!!END
        @!!BEGIN
        @!!type:obligation
        @!!id:1
        @!!status:proved
        @!!END
        @!!BEGIN
        @!!type:obligation
        @!!id:2
        @!!status:proved
        @!!END

        """.data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertEqual(progress?.totalObligations, 2)
        XCTAssertEqual(progress?.provedCount, 2)
        XCTAssertEqual(progress?.phase, .done)
    }

    func testObligationsNumberPreservesPendingUndiscoveredObligations() {
        let data = """
        @!!BEGIN
        @!!type:obligationsnumber
        @!!count:5
        @!!END
        @!!BEGIN
        @!!type:obligation
        @!!id:1
        @!!status:proved
        @!!END
        @!!BEGIN
        @!!type:obligation
        @!!id:2
        @!!status:proved
        @!!END

        """.data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertEqual(progress?.totalObligations, 5)
        XCTAssertEqual(progress?.provedCount, 2)
        XCTAssertEqual(progress?.phase, .checking)
    }

    // MARK: - Status Parsing Tests

    func testParseStatusProved() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .proved)
    }

    func testParseStatusProven() {
        // Alternative spelling
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proven"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .proved)
    }

    func testParseStatusFailed() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "failed"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .failed)
    }

    func testParseStatusTrivial() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "trivial"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .trivial)
    }

    func testParseStatusPending() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "pending"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .pending)
    }

    func testParseStatusToBeProved() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "to be proved"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .pending)
    }

    func testParseStatusChecking() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "checking"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .pending)
    }

    func testParseStatusTimeout() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "timeout"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .timeout)
    }

    func testParseStatusTimedOut() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "timedout"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .timeout)
    }

    func testParseStatusOmitted() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "omitted"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .omitted)
    }

    func testParseStatusInterrupted() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "interrupted"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .pending) // Interrupted treated as pending
    }

    func testParseStatusUnknown() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "unknown_status"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .unknown)
    }

    // MARK: - Backend Parsing Tests

    func testParseBackendZenon() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "zenon"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .zenon)
    }

    func testParseBackendZ3() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "z3"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .z3)
    }

    func testParseBackendSMT() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "smt"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .z3)
    }

    func testParseBackendIsabelle() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "isabelle"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .isabelle)
    }

    func testParseBackendSPASS() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "spass"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .spass)
    }

    func testParseBackendLS4() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "ls4"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .ls4)
    }

    func testParseBackendCVC5() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "cvc5"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .cvc5)
    }

    func testParseBackendAuto() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "auto"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.backend, .auto)
    }

    func testParseBackendUnknown() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "unknown_prover"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertNil(obligations.first?.backend)
    }

    // MARK: - Obligation Kind Parsing Tests

    func testParseKindTheorem() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "theorem"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .theorem)
    }

    func testParseKindLemma() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "lemma"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .lemma)
    }

    func testParseKindCorollary() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "corollary"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .corollary)
    }

    func testParseKindProposition() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "proposition"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .proposition)
    }

    func testParseKindStep() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "step"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .step)
    }

    func testParseKindQED() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "qed"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .qed)
    }

    func testParseKindAssertion() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "assertion"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .assertion)
    }

    func testParseKindAssert() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "assert"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .assertion)
    }

    func testParseKindSuffices() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "suffices"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .suffices)
    }

    func testParseKindCase() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "case"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .case_)
    }

    func testParseKindPick() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "pick"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .pick)
    }

    func testParseKindHave() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "have"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .have)
    }

    func testParseKindTake() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "take"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .take)
    }

    func testParseKindWitness() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "witness"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .witness)
    }

    func testParseKindDefault() {
        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "kind": "unknown_kind"])
        _ = parser.parse(data)
        XCTAssertEqual(parser.getAllObligations().first?.kind, .step)
    }

    // MARK: - Status Block Tests

    func testParseStatusBlockWithTotal() {
        let data = makeBlock(type: "status", fields: ["total": "10"])
        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.totalObligations, 10)
    }

    // MARK: - Error Block Tests

    func testParseErrorBlock() {
        let data = makeBlock(type: "error", fields: [
            "msg": "Syntax error in proof"
        ])
        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .error)
        XCTAssertEqual(progress?.failedCount, 1)
    }

    func testParseErrorBlockWithLocation() {
        let url = URL(fileURLWithPath: "/test/spec.tla")
        parser.setSpecFileURL(url)

        let data = makeBlock(type: "error", fields: [
            "msg": "Syntax error",
            "loc": "5:10:5:20"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.count, 1)
        XCTAssertEqual(obligations.first?.status, .failed)
        XCTAssertEqual(obligations.first?.location.startLine, 5)
    }

    // MARK: - Warning Block Tests

    func testParseWarningBlock() {
        let data = makeBlock(type: "warning", fields: [
            "msg": "Deprecated syntax"
        ])
        let progress = parser.parse(data)

        // Warnings don't return progress
        XCTAssertNil(progress)
    }

    // MARK: - Multiple Obligations Tests

    func testParseMultipleObligations() {
        let data1 = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"])
        let data2 = makeBlock(type: "obligation", fields: ["id": "2", "status": "proved"])
        let data3 = makeBlock(type: "obligation", fields: ["id": "3", "status": "failed"])

        _ = parser.parse(data1)
        _ = parser.parse(data2)
        let progress = parser.parse(data3)

        XCTAssertEqual(progress?.totalObligations, 3)
        XCTAssertEqual(progress?.provedCount, 2)
        XCTAssertEqual(progress?.failedCount, 1)
    }

    func testUpdateExistingObligation() {
        let data1 = makeBlock(type: "obligation", fields: ["id": "1", "status": "pending"])
        let data2 = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved", "prover": "zenon"])

        _ = parser.parse(data1)
        _ = parser.parse(data2)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.count, 1)
        XCTAssertEqual(obligations.first?.status, .proved)
        XCTAssertEqual(obligations.first?.backend, .zenon)
    }

    // MARK: - Non-Toolbox Line Tests

    func testIgnoreNonToolboxLines() {
        let progress = parseLine("Regular output line")
        XCTAssertNil(progress)
    }

    func testIgnoreEmptyLines() {
        let progress = parseLine("")
        XCTAssertNil(progress)
    }

    // MARK: - Buffer Handling Tests

    func testPartialBlockBuffering() {
        // Send block in parts
        _ = parser.parse("@!!BEGIN\n".data(using: .utf8)!)
        _ = parser.parse("@!!type:obligation\n".data(using: .utf8)!)
        _ = parser.parse("@!!id:1\n".data(using: .utf8)!)
        _ = parser.parse("@!!status:proved\n".data(using: .utf8)!)
        let progress = parser.parse("@!!END\n".data(using: .utf8)!)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.provedCount, 1)
    }

    func testMultipleBlocksInOneChunk() {
        let multiBlock = """
        @!!BEGIN
        @!!type:obligation
        @!!id:1
        @!!status:proved
        @!!END
        @!!BEGIN
        @!!type:obligation
        @!!id:2
        @!!status:proved
        @!!END
        """
        _ = parser.parse((multiBlock + "\n").data(using: .utf8)!)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.count, 2)
    }

    // MARK: - Session Management Tests

    func testSetSessionId() {
        let sessionId = UUID()
        parser.setSessionId(sessionId)

        let data = makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"])
        let progress = parser.parse(data)

        XCTAssertEqual(progress?.sessionId, sessionId)
    }

    func testSetSpecFileURL() {
        let url = URL(fileURLWithPath: "/path/to/spec.tla")
        parser.setSpecFileURL(url)

        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "loc": "10:5:15:20"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.location.fileURL, url)
    }

    func testReset() {
        // Parse some obligations
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "failed"]))

        XCTAssertEqual(parser.getAllObligations().count, 2)

        // Reset
        parser.reset()

        XCTAssertTrue(parser.getAllObligations().isEmpty)
    }

    // MARK: - Final Result Tests

    func testFinalResultSuccess() {
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "3", "status": "trivial"]))

        let result = parser.finalResult(exitCode: 0, duration: 1.5)

        XCTAssertTrue(result.success)
        XCTAssertEqual(result.provedCount, 3) // trivial counts as proved
        XCTAssertEqual(result.failedCount, 0)
        XCTAssertEqual(result.duration, 1.5)
        XCTAssertEqual(result.obligations.count, 3)
    }

    func testFinalResultFailure() {
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "failed"]))

        let result = parser.finalResult(exitCode: 1, duration: 2.0)

        XCTAssertFalse(result.success)
        XCTAssertEqual(result.provedCount, 1)
        XCTAssertEqual(result.failedCount, 1)
    }

    func testFinalResultWithNonZeroExitCode() {
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))

        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        // Even if all obligations proved, non-zero exit code means failure
        XCTAssertFalse(result.success)
    }

    func testFinalResultFailsWhenObligationsRemainUnproved() {
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "pending"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "3", "status": "omitted"]))

        let result = parser.finalResult(exitCode: 0, duration: 1.0)

        XCTAssertFalse(result.success)
        XCTAssertEqual(result.failedCount, 0)
        XCTAssertEqual(result.obligations.count, 3)
    }

    // MARK: - Progress Phase Tests

    func testPhaseChecking() {
        // Parse some obligations but not all completed
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        let progress = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "pending"]))

        XCTAssertEqual(progress?.phase, .checking)
    }

    func testPhaseDone() {
        // When all obligations are terminal (proved/failed) and no failures, phase is done
        // The parser sets totalObligations based on parsed obligations
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        let progress = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "proved"]))

        // With 2 proved out of 2 total (no pending), all obligations are complete
        // Note: The parser tracks done based on provedCount + failedCount == totalObligations
        XCTAssertEqual(progress?.totalObligations, 2)
        XCTAssertEqual(progress?.provedCount, 2)
        XCTAssertEqual(progress?.phase, .done)
    }

    func testPhaseError() {
        let progress = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "failed"]))

        XCTAssertEqual(progress?.phase, .error)
    }

    // MARK: - Progress Statistics Tests

    func testProgressFractionComplete() {
        // Parse 4 obligations, 2 proved, 2 pending
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "3", "status": "pending"]))
        let progress = parser.parse(makeBlock(type: "obligation", fields: ["id": "4", "status": "pending"]))

        // 2 proved out of 4 total = 0.5
        XCTAssertEqual(progress?.fractionComplete ?? 0, 0.5, accuracy: 0.01)
    }

    func testProgressPendingCount() {
        // Parse 5 obligations: 2 proved, 3 pending
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "proved"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "3", "status": "pending"]))
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "4", "status": "pending"]))
        let progress = parser.parse(makeBlock(type: "obligation", fields: ["id": "5", "status": "pending"]))

        XCTAssertEqual(progress?.pendingCount, 3)
    }

    func testProgressTrivialCount() {
        _ = parser.parse(makeBlock(type: "obligation", fields: ["id": "1", "status": "trivial"]))
        let progress = parser.parse(makeBlock(type: "obligation", fields: ["id": "2", "status": "trivial"]))

        XCTAssertEqual(progress?.trivialCount, 2)
    }

    // MARK: - Edge Cases

    func testInvalidLocationFormat() {
        let url = URL(fileURLWithPath: "/test/spec.tla")
        parser.setSpecFileURL(url)

        let data = makeBlock(type: "obligation", fields: [
            "id": "1",
            "status": "proved",
            "loc": "invalid"
        ])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        // With invalid location, uses default location
        XCTAssertEqual(obligations.first?.location.startLine, 1)
    }

    func testMissingObligationId() {
        let data = makeBlock(type: "obligation", fields: ["status": "proved"])
        let progress = parser.parse(data)

        // Block without ID is ignored
        XCTAssertNil(progress)
    }

    func testInvalidObligationId() {
        let data = makeBlock(type: "obligation", fields: ["id": "not_a_number", "status": "proved"])
        let progress = parser.parse(data)

        XCTAssertNil(progress)
    }

    func testMissingStatus() {
        let data = makeBlock(type: "obligation", fields: ["id": "1"])
        _ = parser.parse(data)

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.first?.status, .pending) // Default status
    }

    func testCarriageReturnHandling() {
        let data = "@!!BEGIN\r\n@!!type:obligation\r\n@!!id:1\r\n@!!status:proved\r\n@!!END\r\n".data(using: .utf8)!
        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.provedCount, 1)
    }

    // MARK: - Thread Safety Tests (Basic)

    func testConcurrentParsing() async {
        // Test that multiple concurrent parses don't crash
        await withTaskGroup(of: Void.self) { group in
            for i in 1...10 {
                group.addTask {
                    let data = self.makeBlock(type: "obligation", fields: [
                        "id": "\(i)",
                        "status": "proved"
                    ])
                    _ = self.parser.parse(data)
                }
            }
        }

        let obligations = parser.getAllObligations()
        XCTAssertEqual(obligations.count, 10)
    }
}

// MARK: - ProofCheckOptions Tests

final class ProofCheckOptionsTests: XCTestCase {

    func testDefaultOptions() {
        let options = ProofCheckOptions.default

        XCTAssertNil(options.backend)
        XCTAssertEqual(options.timeout, 30)
        XCTAssertEqual(options.threads, 4)
        XCTAssertNil(options.checkFromLine)
        XCTAssertNil(options.checkToLine)
        XCTAssertNil(options.stepName)
        XCTAssertTrue(options.fingerprints)
        XCTAssertFalse(options.verbose)
    }

    func testCustomOptions() {
        let options = ProofCheckOptions(
            backend: .z3,
            timeout: 60,
            threads: 8,
            checkFromLine: 10,
            checkToLine: 50,
            stepName: "Theorem1",
            fingerprints: false,
            verbose: true
        )

        XCTAssertEqual(options.backend, .z3)
        XCTAssertEqual(options.timeout, 60)
        XCTAssertEqual(options.threads, 8)
        XCTAssertEqual(options.checkFromLine, 10)
        XCTAssertEqual(options.checkToLine, 50)
        XCTAssertEqual(options.stepName, "Theorem1")
        XCTAssertFalse(options.fingerprints)
        XCTAssertTrue(options.verbose)
    }

    func testPartialCustomOptions() {
        let options = ProofCheckOptions(
            backend: .zenon,
            timeout: 45
        )

        XCTAssertEqual(options.backend, .zenon)
        XCTAssertEqual(options.timeout, 45)
        XCTAssertEqual(options.threads, 4) // Default
        XCTAssertTrue(options.fingerprints) // Default
    }
}
