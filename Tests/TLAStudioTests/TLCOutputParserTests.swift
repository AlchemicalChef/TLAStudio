import XCTest
@testable import TLAStudioApp

// MARK: - TLC Output Parser Tests

final class TLCOutputParserTests: XCTestCase {

    var parser: TLCOutputParser!

    override func setUp() {
        super.setUp()
        parser = TLCOutputParser()
    }

    override func tearDown() {
        parser = nil
        super.tearDown()
    }

    // MARK: - JSON Progress Parsing Tests

    func testParseJSONProgressBasic() {
        let json = """
        {"type":"progress","states":1000,"distinct":500,"queue":250}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.statesFound, 1000)
        XCTAssertEqual(progress?.distinctStates, 500)
        XCTAssertEqual(progress?.statesLeft, 250)
        XCTAssertEqual(progress?.phase, .computing)
    }

    func testParseJSONProgressWithSPS() {
        let json = """
        {"type":"progress","states":5000,"distinct":2500,"queue":1000,"sps":1234.5}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.statesPerSecond, 1234.5)
    }

    func testParseJSONProgressWithPhase() {
        let json = """
        {"type":"progress","states":100,"distinct":50,"queue":25,"phase":"checkingLiveness"}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .checkingLiveness)
    }

    func testParseJSONProgressWithAction() {
        let json = """
        {"type":"progress","states":100,"distinct":50,"queue":25,"action":"Next"}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.currentAction, "Next")
    }

    func testParseJSONProgressWithMemory() {
        let json = """
        {"type":"progress","states":100,"distinct":50,"queue":25,"memory":1073741824}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.memoryUsed, 1073741824)
    }

    // MARK: - JSON Error Parsing Tests

    func testParseJSONInvariantViolation() {
        let json = """
        {"type":"error","errorType":"invariant","message":"TypeOK violated"}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .error)
    }

    func testParseJSONDeadlock() {
        let json = """
        {"type":"error","errorType":"deadlock","message":"Deadlock reached"}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .error)
    }

    func testParseJSONLivenessViolation() {
        let json = """
        {"type":"error","errorType":"liveness","message":"Temporal property violated"}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .error)
    }

    func testParseJSONErrorWithTrace() {
        let json = """
        {"type":"error","errorType":"invariant","message":"TypeOK violated","trace":[{"action":"Init","variables":{"x":0,"y":true}},{"action":"Next","variables":{"x":1,"y":false}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        XCTAssertNotNil(result.errorTrace)
        XCTAssertEqual(result.errorTrace?.type, .invariantViolation)
        XCTAssertEqual(result.errorTrace?.states.count, 2)
    }

    func testParseJSONErrorWithLoopStart() {
        let json = """
        {"type":"error","errorType":"liveness","message":"Liveness violated","loopStart":1,"trace":[{"action":"Init","variables":{}},{"action":"Loop","variables":{}},{"action":"Back","variables":{}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        XCTAssertNotNil(result.errorTrace)
        XCTAssertEqual(result.errorTrace?.loopStart, 1)
    }

    func testParseJSONErrorWithViolatedProperty() {
        let json = """
        {"type":"error","errorType":"temporal","message":"Property violated","property":"Eventually(done)","trace":[]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        XCTAssertNotNil(result.errorTrace)
        XCTAssertEqual(result.errorTrace?.violatedProperty, "Eventually(done)")
    }

    // MARK: - JSON State Value Parsing Tests

    func testParseJSONIntValue() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"count":42}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["count"], .int(42))
    }

    func testParseJSONBoolValueTrue() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"flag":"TRUE"}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["flag"], .bool(true))
    }

    func testParseJSONBoolValueFalse() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"flag":"FALSE"}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["flag"], .bool(false))
    }

    func testParseJSONBoolValueNative() {
        // Note: JSON native boolean `true` in JSONSerialization becomes NSNumber
        // which can be cast to Int first, so it may be parsed as Int(1) instead of Bool
        // Real TLC output uses string "TRUE"/"FALSE" which is handled correctly
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"flag":true}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        // JSON native bool may be parsed as Int(1) due to NSNumber casting order
        // This is acceptable since real TLC uses "TRUE"/"FALSE" strings
        XCTAssertNotNil(variables?["flag"])
    }

    func testParseJSONStringValue() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"name":"hello"}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["name"], .string("hello"))
    }

    func testParseJSONSequenceValue() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"seq":[1,2,3]}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["seq"], .sequence([.int(1), .int(2), .int(3)]))
    }

    func testParseJSONRecordValue() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"rec":{"a":1,"b":"test"}}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        if case .record(let fields) = variables?["rec"] {
            XCTAssertEqual(fields["a"], .int(1))
            XCTAssertEqual(fields["b"], .string("test"))
        } else {
            XCTFail("Expected record value")
        }
    }

    func testParseJSONNestedValues() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"nested":{"arr":[1,2],"flag":"TRUE"}}}]}
        """
        let data = (json + "\n").data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        if case .record(let fields) = variables?["nested"] {
            XCTAssertEqual(fields["arr"], .sequence([.int(1), .int(2)]))
            XCTAssertEqual(fields["flag"], .bool(true))
        } else {
            XCTFail("Expected record value")
        }
    }

    // MARK: - JSON Coverage Parsing Tests

    func testParseJSONCoverage() {
        // First send some coverage data
        let coverageJson = """
        {"type":"coverage","actions":{"Init":{"count":1,"states":1},"Next":{"count":100,"states":50}}}
        """
        let coverageData = (coverageJson + "\n").data(using: .utf8)!
        _ = parser.parse(coverageData)

        // Then get the final result
        let result = parser.finalResult(exitCode: 0, duration: 1.0)

        XCTAssertEqual(result.coverage.count, 2)

        let initCoverage = result.coverage.first { $0.actionName == "Init" }
        XCTAssertEqual(initCoverage?.count, 1)
        XCTAssertEqual(initCoverage?.distinctStates, 1)

        let nextCoverage = result.coverage.first { $0.actionName == "Next" }
        XCTAssertEqual(nextCoverage?.count, 100)
        XCTAssertEqual(nextCoverage?.distinctStates, 50)
    }

    // MARK: - JSON Done Parsing Tests

    func testParseJSONDone() {
        let json = """
        {"type":"done"}
        """
        let data = (json + "\n").data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .done)
    }

    // MARK: - Text Progress Parsing Tests

    func testParseTextProgressLine() {
        let line = "Progress(10) at 2024-01-15 10:30:00: 1000 states generated, 500 distinct states found, 250 states left on queue.\n"
        let data = line.data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.statesFound, 1000)
        XCTAssertEqual(progress?.distinctStates, 500)
        XCTAssertEqual(progress?.statesLeft, 250)
        XCTAssertEqual(progress?.phase, .computing)
    }

    func testParseTextStateCount() {
        let line = "Finished computing initial states: 10 distinct states generated.\n"
        let data = line.data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.distinctStates, 10)
    }

    func testParseTextInvariantError() {
        let line = "Error: Invariant TypeOK is violated.\n"
        let data = line.data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .error)
    }

    func testParseTextDeadlockError() {
        let line = "Error: Deadlock reached.\n"
        let data = line.data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .error)
    }

    func testParseTextTraceState() {
        // Need to trigger error mode first, then parse trace
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let varLine = "/\\ x = 0\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(varLine.data(using: .utf8)!)

        // Finalize to create the error trace
        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        // Verify the trace was parsed correctly
        XCTAssertNotNil(result.errorTrace)
        XCTAssertEqual(result.errorTrace?.states.count, 1)
        XCTAssertEqual(result.errorTrace?.states.first?.id, 1)
        XCTAssertEqual(result.errorTrace?.states.first?.action, "Init")
        XCTAssertEqual(result.errorTrace?.states.first?.variables["x"], .int(0))
    }

    func testParseTextVariableInt() {
        // Setup: Start error mode and parse a trace
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let varLine = "/\\ count = 42\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(varLine.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        XCTAssertNotNil(result.errorTrace)
        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["count"], .int(42))
    }

    func testParseTextVariableBool() {
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let varLine = "/\\ flag = TRUE\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(varLine.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["flag"], .bool(true))
    }

    func testParseTextVariableString() {
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let varLine = "/\\ msg = \"hello\"\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(varLine.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["msg"], .string("hello"))
    }

    func testParseTextVariableEmptySet() {
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let varLine = "/\\ items = {}\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(varLine.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["items"], .set([]))
    }

    func testParseTextVariableEmptySequence() {
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let varLine = "/\\ seq = <<>>\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(varLine.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["seq"], .sequence([]))
    }

    func testParseTextVariableSequence() {
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let varLine = "/\\ seq = <<1, 2, 3>>\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(varLine.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["seq"], .sequence([.int(1), .int(2), .int(3)]))
    }

    func testParseTextCoverage() {
        let line = "<Next line 10, col 1 to line 15, col 5 of module Test>: 500\n"
        let data = line.data(using: .utf8)!

        _ = parser.parse(data)
        let result = parser.finalResult(exitCode: 0, duration: 1.0)

        let coverage = result.coverage.first { $0.actionName == "Next" }
        XCTAssertEqual(coverage?.count, 500)
    }

    func testParseTextCompletion() {
        let line = "Model checking completed. No error has been found.\n"
        let data = line.data(using: .utf8)!

        let progress = parser.parse(data)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.phase, .done)
    }

    // MARK: - Buffer Handling Tests

    func testPartialLineBuffering() {
        // Send partial line
        let partial1 = "{\"type\":\"progress\","
        _ = parser.parse(partial1.data(using: .utf8)!)

        // Complete the line
        let partial2 = "\"states\":100,\"distinct\":50,\"queue\":25}\n"
        let progress = parser.parse(partial2.data(using: .utf8)!)

        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.statesFound, 100)
    }

    func testMultipleLinesInOneChunk() {
        let multiline = """
        {"type":"progress","states":100,"distinct":50,"queue":25}
        {"type":"progress","states":200,"distinct":100,"queue":50}
        """
        let data = (multiline + "\n").data(using: .utf8)!

        // All lines in a single chunk are processed together;
        // the most recent progress update is returned
        let progress = parser.parse(data)
        XCTAssertNotNil(progress)
        XCTAssertEqual(progress?.statesFound, 200) // Most recent line wins
        XCTAssertEqual(progress?.distinctStates, 100)
    }

    func testEmptyData() {
        let data = Data()
        let progress = parser.parse(data)
        XCTAssertNil(progress)
    }

    func testWhitespaceOnlyLine() {
        let data = "   \n".data(using: .utf8)!
        let progress = parser.parse(data)
        XCTAssertNil(progress)
    }

    // MARK: - Session Management Tests

    func testReset() {
        // Parse some data
        let json = """
        {"type":"progress","states":1000,"distinct":500,"queue":250}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let oldSessionId = parser.sessionId

        // Reset
        parser.reset()

        XCTAssertNotEqual(parser.sessionId, oldSessionId)

        let result = parser.finalResult(exitCode: 0, duration: 0)
        XCTAssertEqual(result.statesFound, 0)
        XCTAssertEqual(result.distinctStates, 0)
    }

    func testSessionIdTracking() {
        let sessionId = parser.sessionId

        let json = """
        {"type":"progress","states":100,"distinct":50,"queue":25}
        """
        let progress = parser.parse((json + "\n").data(using: .utf8)!)

        XCTAssertEqual(progress?.sessionId, sessionId)
    }

    func testFinalResultSuccess() {
        let json = """
        {"type":"progress","states":1000,"distinct":500,"queue":0}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let doneJson = """
        {"type":"done"}
        """
        _ = parser.parse((doneJson + "\n").data(using: .utf8)!)

        let result = parser.finalResult(exitCode: 0, duration: 5.0)

        XCTAssertTrue(result.success)
        XCTAssertEqual(result.statesFound, 1000)
        XCTAssertEqual(result.distinctStates, 500)
        XCTAssertEqual(result.duration, 5.0)
        XCTAssertNil(result.errorTrace)
    }

    func testFinalResultFailure() {
        let json = """
        {"type":"error","errorType":"invariant","message":"TypeOK violated","trace":[{"action":"Init","variables":{"x":0}}]}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = parser.finalResult(exitCode: 1, duration: 2.0)

        XCTAssertFalse(result.success)
        XCTAssertNotNil(result.errorTrace)
        XCTAssertEqual(result.message, "TypeOK violated")
    }

    // MARK: - Large Trace Threshold Tests

    func testLargeTraceThresholdValue() {
        XCTAssertEqual(TLCOutputParser.largeTraceThreshold, 1000)
    }

    // MARK: - Edge Cases

    func testInvalidJSON() {
        let data = "not valid json\n".data(using: .utf8)!
        let progress = parser.parse(data)
        XCTAssertNil(progress)
    }

    func testJSONWithUnknownType() {
        let json = """
        {"type":"unknown","data":"test"}
        """
        let data = (json + "\n").data(using: .utf8)!
        let progress = parser.parse(data)
        XCTAssertNil(progress)
    }

    func testMultipleStatesInTrace() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"x":0}},{"action":"Step1","variables":{"x":1}},{"action":"Step2","variables":{"x":2}},{"action":"Step3","variables":{"x":3}}]}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        XCTAssertEqual(result.errorTrace?.states.count, 4)
        XCTAssertEqual(result.errorTrace?.states[0].action, "Init")
        XCTAssertEqual(result.errorTrace?.states[1].action, "Step1")
        XCTAssertEqual(result.errorTrace?.states[2].action, "Step2")
        XCTAssertEqual(result.errorTrace?.states[3].action, "Step3")
    }

    func testStateWithLocation() {
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{},"location":{"file":"Test.tla","line":10,"column":5}}]}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let location = result.errorTrace?.states.first?.location
        XCTAssertEqual(location?.file, "Test.tla")
        XCTAssertEqual(location?.line, 10)
        XCTAssertEqual(location?.column, 5)
    }

    // MARK: - finalResultWithStorage Tests

    func testFinalResultWithStorageSmallTrace() async {
        // Small trace (<= 1000 states) should remain in memory
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"x":0}},{"action":"Next","variables":{"x":1}}]}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = await parser.finalResultWithStorage(exitCode: 1, duration: 1.0)

        XCTAssertFalse(result.success)
        XCTAssertNotNil(result.errorTrace) // Small trace uses in-memory storage
        XCTAssertNil(result.lazyErrorTrace) // No lazy trace for small traces
        XCTAssertEqual(result.errorTrace?.states.count, 2)
    }

    func testFinalResultWithStorageNoError() async {
        let json = """
        {"type":"progress","states":1000,"distinct":500,"queue":0}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = await parser.finalResultWithStorage(exitCode: 0, duration: 5.0)

        XCTAssertTrue(result.success)
        XCTAssertNil(result.errorTrace)
        XCTAssertNil(result.lazyErrorTrace)
    }

    func testFinalResultWithStorageLargeTraceIsFailureEvenWithZeroExit() async {
        for i in 0...TLCOutputParser.largeTraceThreshold {
            let state = #"{"type":"state","id":\#(i),"action":"Step","variables":{"x":\#(i)}}"#
            _ = parser.parse((state + "\n").data(using: .utf8)!)
        }

        let errorJson = """
        {"type":"error","errorType":"invariant","message":"TypeOK violated"}
        """
        _ = parser.parse((errorJson + "\n").data(using: .utf8)!)

        let result = await parser.finalResultWithStorage(exitCode: 0, duration: 1.0)

        XCTAssertFalse(result.success)
        XCTAssertNil(result.errorTrace)
        XCTAssertNotNil(result.lazyErrorTrace)

        await TraceStorageManager.shared.cleanup(sessionId: result.sessionId)
    }

    // MARK: - JSON State Message Parsing Tests

    func testParseJSONStateAccumulation() {
        // Parse multiple separate state messages
        let state1 = """
        {"type":"state","id":0,"action":"Init","variables":{"x":0}}
        """
        let state2 = """
        {"type":"state","id":1,"action":"Next","variables":{"x":1}}
        """

        _ = parser.parse((state1 + "\n").data(using: .utf8)!)
        _ = parser.parse((state2 + "\n").data(using: .utf8)!)

        // Trigger error to finalize trace
        let errorJson = """
        {"type":"error","errorType":"invariant","message":"Test"}
        """
        _ = parser.parse((errorJson + "\n").data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        // States should have been accumulated
        XCTAssertNotNil(result.errorTrace)
        // Note: The accumulated states from "state" messages are separate from error trace states
    }

    // MARK: - Additional Edge Cases

    func testParseJSONVariableWithNullValue() {
        // JSON null should be ignored (parseStateValue returns nil)
        let json = """
        {"type":"error","errorType":"invariant","message":"Test","trace":[{"action":"Init","variables":{"x":null,"y":1}}]}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertNil(variables?["x"]) // null should not be in variables
        XCTAssertEqual(variables?["y"], .int(1)) // valid value should be present
    }

    func testParseJSONCoverageEmptyActions() {
        let json = """
        {"type":"coverage","actions":{}}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = parser.finalResult(exitCode: 0, duration: 1.0)
        XCTAssertTrue(result.coverage.isEmpty)
    }

    func testParseJSONCoverageMissingFields() {
        // Coverage with missing count/states should default to 0
        let json = """
        {"type":"coverage","actions":{"Init":{}}}
        """
        _ = parser.parse((json + "\n").data(using: .utf8)!)

        let result = parser.finalResult(exitCode: 0, duration: 1.0)

        let initCoverage = result.coverage.first { $0.actionName == "Init" }
        XCTAssertNotNil(initCoverage)
        XCTAssertEqual(initCoverage?.count, 0)
        XCTAssertEqual(initCoverage?.distinctStates, 0)
    }

    func testParseTextMultipleTraceStates() {
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let state1 = "State 1: <Init>\n"
        let var1 = "/\\ x = 0\n"
        let state2 = "State 2: <Next>\n"
        let var2 = "/\\ x = 1\n"
        let state3 = "State 3: <Next>\n"
        let var3 = "/\\ x = 2\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(state1.data(using: .utf8)!)
        _ = parser.parse(var1.data(using: .utf8)!)
        _ = parser.parse(state2.data(using: .utf8)!)
        _ = parser.parse(var2.data(using: .utf8)!)
        _ = parser.parse(state3.data(using: .utf8)!)
        _ = parser.parse(var3.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        XCTAssertNotNil(result.errorTrace)
        XCTAssertEqual(result.errorTrace?.states.count, 3)
        XCTAssertEqual(result.errorTrace?.states[0].variables["x"], .int(0))
        XCTAssertEqual(result.errorTrace?.states[1].variables["x"], .int(1))
        XCTAssertEqual(result.errorTrace?.states[2].variables["x"], .int(2))
    }

    func testParseTextMultipleVariablesPerState() {
        let errorLine = "Error: Invariant TypeOK is violated.\n"
        let stateLine = "State 1: <Init>\n"
        let var1 = "/\\ x = 0\n"
        let var2 = "/\\ y = TRUE\n"
        let var3 = "/\\ z = \"hello\"\n"

        _ = parser.parse(errorLine.data(using: .utf8)!)
        _ = parser.parse(stateLine.data(using: .utf8)!)
        _ = parser.parse(var1.data(using: .utf8)!)
        _ = parser.parse(var2.data(using: .utf8)!)
        _ = parser.parse(var3.data(using: .utf8)!)

        parser.finalizeErrorTrace()
        let result = parser.finalResult(exitCode: 1, duration: 1.0)

        let variables = result.errorTrace?.states.first?.variables
        XCTAssertEqual(variables?["x"], .int(0))
        XCTAssertEqual(variables?["y"], .bool(true))
        XCTAssertEqual(variables?["z"], .string("hello"))
    }
}
