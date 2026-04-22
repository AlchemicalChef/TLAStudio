import XCTest
@testable import TLAStudioApp

// MARK: - Error Handling Tests

/// Tests for error handling across all components.
final class ErrorHandlingTests: XCTestCase {

    // MARK: - TLC Error Handling Tests

    func testTLCErrorEquality() {
        let error1 = TLCError.tlcNotFound
        let error2 = TLCError.tlcNotFound
        let error3 = TLCError.timeout

        // Errors should be comparable via localizedDescription
        XCTAssertEqual(error1.errorDescription, error2.errorDescription)
        XCTAssertNotEqual(error1.errorDescription, error3.errorDescription)
    }

    func testTLCErrorLocalizedDescription() {
        let errors: [TLCError] = [
            .tlcNotFound,
            .specNotFound,
            .timeout,
            .cancelled,
            .javaNotFound,
            .tla2toolsNotFound,
            .outOfMemory(suggestJVM: true),
            .outOfMemory(suggestJVM: false),
            .invalidConfig("test"),
            .failedToStart(NSError(domain: "test", code: 1)),
            .configWriteFailed(NSError(domain: "test", code: 2))
        ]

        for error in errors {
            XCTAssertNotNil(error.localizedDescription)
            XCTAssertFalse(error.localizedDescription.isEmpty)
        }
    }

    func testTLCErrorIsLocalizedError() {
        let error: Error = TLCError.tlcNotFound

        // Should conform to LocalizedError
        XCTAssertNotNil(error.localizedDescription)
    }

    // MARK: - TLAPM Error Handling Tests

    func testTLAPMErrorEquality() {
        let error1 = TLAPMError.tlapmNotFound
        let error2 = TLAPMError.tlapmNotFound
        let error3 = TLAPMError.timeout

        XCTAssertEqual(error1.errorDescription, error2.errorDescription)
        XCTAssertNotEqual(error1.errorDescription, error3.errorDescription)
    }

    func testTLAPMErrorLocalizedDescription() {
        let errors: [TLAPMError] = [
            .tlapmNotFound,
            .specNotFound,
            .timeout,
            .cancelled,
            .proverNotFound(.z3),
            .proverNotFound(.zenon),
            .parseError("test error"),
            .failedToStart(NSError(domain: "test", code: 1)),
            .invalidLocation(line: 10, column: 5)
        ]

        for error in errors {
            XCTAssertNotNil(error.localizedDescription)
            XCTAssertFalse(error.localizedDescription.isEmpty)
        }
    }

    func testTLAPMErrorIsLocalizedError() {
        let error: Error = TLAPMError.tlapmNotFound

        XCTAssertNotNil(error.localizedDescription)
    }

    // MARK: - Checkpoint Error Handling Tests

    func testCheckpointErrorDescriptions() {
        let errors: [CheckpointError] = [
            .notFound("test-checkpoint"),
            .invalidCheckpoint("test"),
            .recoveryFailed("reason"),
            .cleanupFailed("cleanup failed")
        ]

        for error in errors {
            XCTAssertNotNil(error.errorDescription)
            XCTAssertFalse(error.errorDescription!.isEmpty)
        }
    }

    // MARK: - Error Recovery Tests

    @MainActor
    func testTLCSessionCreation() {
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

        // Session should be created with nil error
        XCTAssertNil(session.error)
        XCTAssertFalse(session.isRunning)
    }

    @MainActor
    func testProofSessionCreation() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        let session = ProofSession(specURL: specURL)

        // Session should be created with nil error
        XCTAssertNil(session.error)
        XCTAssertFalse(session.isRunning)
    }

    // MARK: - Error Message Content Tests

    func testTLCNotFoundErrorMessage() {
        let error = TLCError.tlcNotFound

        XCTAssertTrue(error.errorDescription!.lowercased().contains("not found") ||
                      error.errorDescription!.lowercased().contains("missing"))
    }

    func testJavaNotFoundErrorMessage() {
        let error = TLCError.javaNotFound

        XCTAssertTrue(error.errorDescription!.lowercased().contains("java"))
    }

    func testTla2toolsNotFoundErrorMessage() {
        let error = TLCError.tla2toolsNotFound

        XCTAssertTrue(error.errorDescription!.lowercased().contains("tla2tools"))
    }

    func testTLAPMNotFoundErrorMessage() {
        let error = TLAPMError.tlapmNotFound

        XCTAssertTrue(error.errorDescription!.lowercased().contains("tlapm") ||
                      error.errorDescription!.lowercased().contains("proof"))
    }

    func testProverNotFoundErrorMessage() {
        let error = TLAPMError.proverNotFound(.z3)

        XCTAssertNotNil(error.errorDescription)
    }

    // MARK: - Wrapped Error Tests

    func testTLCFailedToStartWrapsError() {
        let underlying = NSError(domain: "TestDomain", code: 42, userInfo: [
            NSLocalizedDescriptionKey: "Process launch failed"
        ])
        let error = TLCError.failedToStart(underlying)

        XCTAssertTrue(error.errorDescription!.contains("Process launch failed"))
    }

    func testTLCConfigWriteFailedWrapsError() {
        let underlying = NSError(domain: NSPOSIXErrorDomain, code: Int(EACCES), userInfo: [
            NSLocalizedDescriptionKey: "Permission denied"
        ])
        let error = TLCError.configWriteFailed(underlying)

        XCTAssertNotNil(error.errorDescription)
    }

    func testTLAPMFailedToStartWrapsError() {
        let underlying = NSError(domain: "TestDomain", code: 99, userInfo: [
            NSLocalizedDescriptionKey: "Binary not executable"
        ])
        let error = TLAPMError.failedToStart(underlying)

        XCTAssertTrue(error.errorDescription!.contains("Binary not executable"))
    }

    // MARK: - Invalid Input Error Tests

    func testTLCInvalidConfigError() {
        let reasons = [
            "Missing INIT predicate",
            "Invalid constant value",
            "Spec name contains invalid characters",
            ""
        ]

        for reason in reasons {
            let error = TLCError.invalidConfig(reason)
            XCTAssertNotNil(error.errorDescription)
        }
    }

    func testTLAPMParseError() {
        let messages = [
            "Unexpected token at line 42",
            "Invalid proof structure",
            "Missing obligation fingerprint",
            ""
        ]

        for message in messages {
            let error = TLAPMError.parseError(message)
            XCTAssertNotNil(error.errorDescription)
        }
    }

    func testTLAPMInvalidLocationError() {
        let locations = [
            (line: 0, column: 0),
            (line: -1, column: 5),
            (line: 100, column: -1),
            (line: 999999, column: 999999)
        ]

        for loc in locations {
            let error = TLAPMError.invalidLocation(line: loc.line, column: loc.column)
            XCTAssertNotNil(error.errorDescription)
            XCTAssertTrue(error.errorDescription!.contains("\(loc.line)"))
        }
    }

    // MARK: - OOM Error Suggestion Tests

    func testOOMErrorWithJVMSuggestion() {
        let error = TLCError.outOfMemory(suggestJVM: true)

        XCTAssertTrue(error.errorDescription!.contains("JVM"))
    }

    func testOOMErrorWithoutJVMSuggestion() {
        let error = TLCError.outOfMemory(suggestJVM: false)

        XCTAssertFalse(error.errorDescription!.contains("JVM"))
    }

    // MARK: - Error Type Checking Tests

    func testErrorIsSpecificType() {
        let tlcError: Error = TLCError.tlcNotFound
        let tlapmError: Error = TLAPMError.tlapmNotFound

        if case TLCError.tlcNotFound = tlcError as! TLCError {
            XCTAssertTrue(true)
        } else {
            XCTFail("Expected TLCError.tlcNotFound")
        }

        if case TLAPMError.tlapmNotFound = tlapmError as! TLAPMError {
            XCTAssertTrue(true)
        } else {
            XCTFail("Expected TLAPMError.tlapmNotFound")
        }
    }

    // MARK: - Concurrent Error Handling Tests

    func testConcurrentErrorCreation() async {
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<100 {
                group.addTask {
                    let error = TLCError.invalidConfig("Error \(i)")
                    XCTAssertNotNil(error.errorDescription)
                }
            }
        }
    }

    // MARK: - Error Description Consistency Tests

    func testErrorDescriptionIsConsistent() {
        let error = TLCError.tlcNotFound

        let desc1 = error.errorDescription
        let desc2 = error.errorDescription

        XCTAssertEqual(desc1, desc2)
    }

    func testErrorDescriptionIsNotEmpty() {
        let tlcErrors: [TLCError] = [
            .tlcNotFound, .specNotFound, .timeout, .cancelled,
            .javaNotFound, .tla2toolsNotFound
        ]

        let tlapmErrors: [TLAPMError] = [
            .tlapmNotFound, .specNotFound, .timeout, .cancelled
        ]

        for error in tlcErrors {
            XCTAssertFalse(error.errorDescription?.isEmpty ?? true)
        }

        for error in tlapmErrors {
            XCTAssertFalse(error.errorDescription?.isEmpty ?? true)
        }
    }
}

// MARK: - Parser Error Handling Tests

final class ParserErrorHandlingTests: XCTestCase {

    // MARK: - TLC Parser Error Tests

    func testTLCParserHandlesEmptyInput() {
        let parser = TLCOutputParser()

        let result = parser.parseThreadSafe(Data())

        // Empty data should not crash
        XCTAssertNil(result)
    }

    func testTLCParserHandlesInvalidUTF8() {
        let parser = TLCOutputParser()

        // Invalid UTF-8 sequence
        let invalidData = Data([0xFF, 0xFE, 0x00, 0x01])

        let result = parser.parseThreadSafe(invalidData)

        // Should handle gracefully
        XCTAssertNil(result)
    }

    func testTLCParserHandlesPartialJSON() {
        let parser = TLCOutputParser()

        let partialJSON = "{\"type\": \"progress\", \"states\":"
        let data = partialJSON.data(using: .utf8)!

        // Should not crash on partial JSON
        _ = parser.parseThreadSafe(data)
    }

    func testTLCParserHandlesMalformedJSON() {
        let parser = TLCOutputParser()

        let malformed = "{not valid json}"
        let data = malformed.data(using: .utf8)!

        // Should handle gracefully
        _ = parser.parseThreadSafe(data)
    }

    // MARK: - TLAPM Parser Error Tests

    func testTLAPMParserHandlesEmptyInput() {
        let parser = TLAPMOutputParser()

        let result = parser.parse(Data())

        // Empty data should not crash
        XCTAssertNil(result)
    }

    func testTLAPMParserHandlesInvalidUTF8() {
        let parser = TLAPMOutputParser()

        let invalidData = Data([0xFF, 0xFE, 0x00, 0x01])

        let result = parser.parse(invalidData)

        XCTAssertNil(result)
    }

    func testTLAPMParserHandlesPartialLine() {
        let parser = TLAPMOutputParser()

        let partial = "@!!BEGIN\n@!!type:ob"
        let data = partial.data(using: .utf8)!

        // Should not crash on partial toolbox output
        _ = parser.parse(data)
    }

    // MARK: - Buffer Overflow Prevention Tests

    func testTLCParserLargeInput() {
        let parser = TLCOutputParser()

        // Create a very large input
        let largeString = String(repeating: "x", count: 1_000_000)
        let data = largeString.data(using: .utf8)!

        // Should handle large input without crashing
        _ = parser.parseThreadSafe(data)
    }

    func testTLAPMParserLargeInput() {
        let parser = TLAPMOutputParser()

        let largeString = String(repeating: "@!!type:obligation\n", count: 10_000)
        let data = largeString.data(using: .utf8)!

        // Should handle large input without crashing
        _ = parser.parse(data)
    }

    // MARK: - Repeated Parsing Tests

    func testTLCParserRepeatedParsing() {
        let parser = TLCOutputParser()

        for i in 0..<1000 {
            let text = "Progress: \(i) states"
            let data = text.data(using: .utf8)!
            _ = parser.parseThreadSafe(data)
        }

        // Should not leak memory or crash
    }

    func testTLAPMParserRepeatedParsing() {
        let parser = TLAPMOutputParser()

        for i in 0..<1000 {
            let text = "@!!BEGIN\n@!!type:obligation\n@!!id:\(i)\n@!!END"
            let data = text.data(using: .utf8)!
            _ = parser.parse(data)
        }

        // Should not leak memory or crash
    }
}

// MARK: - Process Registry Error Handling Tests

final class ProcessRegistryErrorTests: XCTestCase {

    func testTerminateNonexistentProcess() {
        let registry = ProcessRegistry.shared
        let fakeId = UUID()

        // Should not crash
        registry.terminate(fakeId)
    }

    func testUnregisterNonexistentProcess() {
        let registry = ProcessRegistry.shared
        let fakeId = UUID()

        // Should not crash
        registry.unregister(fakeId)
    }

    func testIsRunningNonexistentProcess() {
        let registry = ProcessRegistry.shared
        let fakeId = UUID()

        let isRunning = registry.isRunning(fakeId)

        XCTAssertFalse(isRunning)
    }

    func testTerminateAllWithNoProcesses() {
        let registry = ProcessRegistry.shared

        // Should not crash
        registry.terminateAll()
    }
}

// MARK: - Output Accumulator Error Tests

final class OutputAccumulatorTests: XCTestCase {

    func testAccumulatorEmptyData() {
        // Test that empty data handling works
        // (OutputAccumulator is private, so we test indirectly through parsers)
        let parser = TLAPMOutputParser()

        _ = parser.parse(Data())

        // Should not crash
    }

    func testAccumulatorConcurrentAppends() async {
        // Test thread safety of output accumulation
        let parser = TLAPMOutputParser()

        await withTaskGroup(of: Void.self) { group in
            for i in 0..<100 {
                group.addTask {
                    let text = "Line \(i)\n"
                    let data = text.data(using: .utf8)!
                    _ = parser.parse(data)
                }
            }
        }

        // Should complete without data race
    }
}
