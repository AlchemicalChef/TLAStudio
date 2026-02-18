import XCTest
@testable import TLAStudioApp

// MARK: - ModelConfig Security Tests

/// Tests for TLC config file generation security — verifying that input sanitization
/// prevents injection of additional TLC directives through user-supplied values.
final class ModelConfigSecurityTests: XCTestCase {

    // MARK: - Init/Next Predicate Injection

    func testInitPredicateRejectsNewline() {
        let config = TestFactories.makeModelConfig(
            initPredicate: "Init\nINVARIANT Injected"
        )
        let content = config.generateConfigFile()

        // The injected INVARIANT should not appear
        XCTAssertFalse(content.contains("INIT Init\nINVARIANT Injected"),
                       "Newline in init predicate should be sanitized")
        XCTAssertFalse(content.contains("INVARIANT Injected"),
                       "Injected INVARIANT directive should not appear")
    }

    func testNextActionRejectsCarriageReturn() {
        let config = TestFactories.makeModelConfig(
            nextAction: "Next\r\nPROPERTY Injected"
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("PROPERTY Injected"),
                       "Carriage return injection in next action should be blocked")
    }

    func testInitPredicateRejectsCarriageReturn() {
        let config = TestFactories.makeModelConfig(
            initPredicate: "Init\rINVARIANT Injected"
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("INVARIANT Injected"),
                       "Carriage return in init predicate should be sanitized")
    }

    // MARK: - Invariant Injection

    func testInvariantRejectsNewlineInjection() {
        let config = TestFactories.makeModelConfig(
            invariants: ["TypeOK\nCONSTANT Injected = 42"]
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("CONSTANT Injected"),
                       "Newline injection in invariant should be blocked")
    }

    func testMultipleInvariantsWithOneInvalid() {
        let config = TestFactories.makeModelConfig(
            invariants: ["TypeOK", "Safety\nINJECTED", "Liveness"]
        )
        let content = config.generateConfigFile()

        // Valid invariants should be preserved
        XCTAssertTrue(content.contains("INVARIANT TypeOK"),
                      "Valid invariant TypeOK should be present")
        XCTAssertTrue(content.contains("INVARIANT Liveness"),
                      "Valid invariant Liveness should be present")
        // Injected directive should not appear
        XCTAssertFalse(content.contains("INJECTED"),
                       "Invalid invariant with injection should be dropped")
    }

    // MARK: - Temporal Property Injection

    func testTemporalPropertyRejectsNewlineInjection() {
        let config = TestFactories.makeModelConfig(
            temporalProperties: ["Liveness\nCONSTANT Evil = TRUE"]
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("CONSTANT Evil"),
                       "Newline injection in temporal property should be blocked")
    }

    // MARK: - Constant Name Validation

    func testConstantNameValidatesAsIdentifier() {
        let config = TestFactories.makeModelConfig(
            constants: ["ValidName": .int(42)]
        )
        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("CONSTANT ValidName = 42"))
    }

    func testConstantNameRejectsNonIdentifier() {
        let config = TestFactories.makeModelConfig(
            constants: ["not valid!": .int(42)]
        )
        let content = config.generateConfigFile()

        // Invalid constant name should be dropped entirely
        XCTAssertFalse(content.contains("not valid!"),
                       "Non-identifier constant name should be rejected")
        XCTAssertFalse(content.contains("CONSTANT not valid!"),
                       "Non-identifier constant name should not produce a CONSTANT line")
    }

    func testConstantNameRejectsInjectionAttempt() {
        let config = TestFactories.makeModelConfig(
            constants: ["N\nINVARIANT Injected": .int(3)]
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("INVARIANT Injected"),
                       "Newline in constant name should be rejected")
    }

    func testConstantNameRejectsSpaces() {
        let config = TestFactories.makeModelConfig(
            constants: ["has spaces": .int(1)]
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("has spaces"),
                       "Constant name with spaces should be rejected")
    }

    func testConstantNameAllowsUnderscores() {
        let config = TestFactories.makeModelConfig(
            constants: ["Max_Value": .int(100)]
        )
        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("CONSTANT Max_Value = 100"),
                      "Constant name with underscores should be accepted")
    }

    func testConstantNameAllowsLeadingUnderscore() {
        let config = TestFactories.makeModelConfig(
            constants: ["_private": .int(0)]
        )
        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("CONSTANT _private = 0"),
                      "Constant name with leading underscore should be accepted")
    }

    // MARK: - String Constant Escaping

    func testStringConstantEscapesBackslashes() {
        let config = TestFactories.makeModelConfig(
            constants: ["Path": .string("C:\\Users\\test")]
        )
        let content = config.generateConfigFile()

        // Backslashes should be escaped in the output
        XCTAssertTrue(content.contains("C:\\\\Users\\\\test"),
                      "Backslashes in string constants should be escaped")
    }

    func testStringConstantEscapesQuotes() {
        let config = TestFactories.makeModelConfig(
            constants: ["Msg": .string("He said \"hello\"")]
        )
        let content = config.generateConfigFile()

        // Quotes should be escaped
        XCTAssertTrue(content.contains("\\\"hello\\\""),
                      "Quotes in string constants should be escaped")
    }

    func testStringConstantWithEmbeddedNewlineRejected() {
        let config = TestFactories.makeModelConfig(
            constants: ["Evil": .string("line1\nINVARIANT Injected")]
        )
        let content = config.generateConfigFile()

        // The constant value contains a newline, so sanitizeTLCExpression
        // should reject the formatted value
        XCTAssertFalse(content.contains("INVARIANT Injected"),
                       "String constant with embedded newline should be rejected")
    }

    // MARK: - Constraint Injection

    func testStateConstraintRejectsNewline() {
        let config = TestFactories.makeModelConfig(
            stateConstraint: "x < 10\nINVARIANT Injected"
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("INVARIANT Injected"),
                       "Newline injection in state constraint should be blocked")
    }

    func testActionConstraintRejectsNewline() {
        let config = TestFactories.makeModelConfig(
            actionConstraint: "x' > x\nPROPERTY Injected"
        )
        let content = config.generateConfigFile()

        XCTAssertFalse(content.contains("PROPERTY Injected"),
                       "Newline injection in action constraint should be blocked")
    }

    // MARK: - Valid Configurations

    func testValidConfigGeneratesCorrectly() {
        let config = TestFactories.makeModelConfig(
            initPredicate: "Init",
            nextAction: "Next",
            constants: ["N": .int(3), "MaxVal": .int(100)],
            invariants: ["TypeOK", "Safety"],
            temporalProperties: ["Liveness"]
        )
        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("INIT Init"))
        XCTAssertTrue(content.contains("NEXT Next"))
        XCTAssertTrue(content.contains("CONSTANT MaxVal = 100"))
        XCTAssertTrue(content.contains("CONSTANT N = 3"))
        XCTAssertTrue(content.contains("INVARIANT TypeOK"))
        XCTAssertTrue(content.contains("INVARIANT Safety"))
        XCTAssertTrue(content.contains("PROPERTY Liveness"))
    }

    func testEmptyInvariantsSkipped() {
        let config = TestFactories.makeModelConfig(
            invariants: ["TypeOK", "", "Safety"]
        )
        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("INVARIANT TypeOK"))
        XCTAssertTrue(content.contains("INVARIANT Safety"))
        // Empty string should not produce an INVARIANT line
        let invariantCount = content.components(separatedBy: "INVARIANT ").count - 1
        XCTAssertEqual(invariantCount, 2, "Only non-empty invariants should be included")
    }
}
