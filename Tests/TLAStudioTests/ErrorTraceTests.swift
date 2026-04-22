import XCTest
@testable import TLAStudioApp

// MARK: - Error Trace Tests

/// Tests for ErrorTrace, TraceState, and StateValue types.
final class ErrorTraceTests: XCTestCase {

    // MARK: - ErrorTrace Tests

    func testErrorTraceCreation() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Invariant violated",
            states: [],
            loopStart: nil,
            violatedProperty: "TypeOK"
        )

        XCTAssertEqual(trace.type, .invariantViolation)
        XCTAssertEqual(trace.message, "Invariant violated")
        XCTAssertTrue(trace.states.isEmpty)
        XCTAssertNil(trace.loopStart)
        XCTAssertEqual(trace.violatedProperty, "TypeOK")
    }

    func testErrorTraceWithStates() {
        let states = [
            TraceState(id: 0, action: nil, variables: ["x": .int(0)]),
            TraceState(id: 1, action: "Next", variables: ["x": .int(1)])
        ]

        let trace = ErrorTrace(
            type: .deadlock,
            message: "Deadlock found",
            states: states
        )

        XCTAssertEqual(trace.states.count, 2)
        XCTAssertEqual(trace.states[0].id, 0)
        XCTAssertEqual(trace.states[1].id, 1)
    }

    func testErrorTraceWithLoopStart() {
        let trace = ErrorTrace(
            type: .livenessViolation,
            message: "Liveness violated",
            states: [
                TraceState(id: 0, action: nil, variables: [:]),
                TraceState(id: 1, action: "A", variables: [:]),
                TraceState(id: 2, action: "B", variables: [:])
            ],
            loopStart: 1
        )

        XCTAssertEqual(trace.loopStart, 1)
    }

    // MARK: - ErrorType Tests

    func testErrorTypeDisplayNames() {
        let types: [(ErrorTrace.ErrorType, String)] = [
            (.invariantViolation, "Invariant Violation"),
            (.deadlock, "Deadlock"),
            (.livenessViolation, "Liveness Violation"),
            (.assertionFailure, "Assertion Failure"),
            (.evaluationError, "Evaluation Error"),
            (.temporal, "Temporal Property Violation")
        ]

        for (errorType, expectedName) in types {
            XCTAssertEqual(errorType.displayName, expectedName)
        }
    }

    func testErrorTypeCodable() throws {
        let types: [ErrorTrace.ErrorType] = [
            .invariantViolation, .deadlock, .livenessViolation,
            .assertionFailure, .evaluationError, .temporal
        ]

        let encoder = JSONEncoder()
        let decoder = JSONDecoder()

        for type in types {
            let data = try encoder.encode(type)
            let decoded = try decoder.decode(ErrorTrace.ErrorType.self, from: data)
            XCTAssertEqual(type, decoded)
        }
    }

    // MARK: - TraceState Tests

    func testTraceStateCreation() {
        let state = TraceState(
            id: 5,
            action: "Increment",
            variables: ["counter": .int(10)],
            location: SourceLocation(line: 20, column: 5)
        )

        XCTAssertEqual(state.id, 5)
        XCTAssertEqual(state.action, "Increment")
        XCTAssertEqual(state.variables.count, 1)
        XCTAssertNotNil(state.location)
    }

    func testTraceStateDisplayName() {
        let initialState = TraceState(id: 0, action: nil, variables: [:])
        XCTAssertEqual(initialState.displayName, "Initial State")

        let stateWithAction = TraceState(id: 5, action: "MyAction", variables: [:])
        XCTAssertEqual(stateWithAction.displayName, "State 5: MyAction")

        let stateWithoutAction = TraceState(id: 3, action: nil, variables: [:])
        XCTAssertEqual(stateWithoutAction.displayName, "State 3")
    }

    func testTraceStateSortedVariableNames() {
        let state = TraceState(
            id: 0,
            action: nil,
            variables: ["z": .int(3), "a": .int(1), "m": .int(2)]
        )

        XCTAssertEqual(state.sortedVariableNames, ["a", "m", "z"])
    }

    func testChangedVariablesFromNil() {
        let state = TraceState(
            id: 0,
            action: nil,
            variables: ["x": .int(0), "y": .int(1)]
        )

        let changed = state.changedVariables(from: nil)

        // All variables should be considered changed when there's no previous state
        XCTAssertEqual(changed.count, 2)
        XCTAssertTrue(changed.contains("x"))
        XCTAssertTrue(changed.contains("y"))
    }

    func testChangedVariablesFromPrevious() {
        let previous = TraceState(
            id: 0,
            action: nil,
            variables: ["x": .int(0), "y": .int(1), "z": .int(2)]
        )

        let current = TraceState(
            id: 1,
            action: "Change",
            variables: ["x": .int(99), "y": .int(1), "z": .int(2)]  // Only x changed
        )

        let changed = current.changedVariables(from: previous)

        XCTAssertEqual(changed.count, 1)
        XCTAssertTrue(changed.contains("x"))
        XCTAssertFalse(changed.contains("y"))
        XCTAssertFalse(changed.contains("z"))
    }

    func testTraceStateCodable() throws {
        let state = TraceState(
            id: 1,
            action: "Test",
            variables: ["x": .int(42)],
            location: SourceLocation(line: 10, column: 5)
        )

        let encoder = JSONEncoder()
        let decoder = JSONDecoder()

        let data = try encoder.encode(state)
        let decoded = try decoder.decode(TraceState.self, from: data)

        XCTAssertEqual(decoded.id, state.id)
        XCTAssertEqual(decoded.action, state.action)
        XCTAssertEqual(decoded.variables.count, state.variables.count)
        XCTAssertEqual(decoded.sortedVariableNames, state.sortedVariableNames)
    }

    // MARK: - SourceLocation Tests

    func testSourceLocationCreation() {
        let location = SourceLocation(
            file: "Test.tla",
            line: 10,
            column: 5,
            endLine: 10,
            endColumn: 15
        )

        XCTAssertEqual(location.file, "Test.tla")
        XCTAssertEqual(location.line, 10)
        XCTAssertEqual(location.column, 5)
        XCTAssertEqual(location.endLine, 10)
        XCTAssertEqual(location.endColumn, 15)
    }

    func testSourceLocationDisplayString() {
        let locationWithFile = SourceLocation(file: "Spec.tla", line: 20, column: 10)
        XCTAssertEqual(locationWithFile.displayString, "Spec.tla:20:10")

        let locationWithoutFile = SourceLocation(line: 15, column: 3)
        XCTAssertEqual(locationWithoutFile.displayString, "line 15, column 3")
    }

    func testSourceLocationEquality() {
        let loc1 = SourceLocation(file: "A.tla", line: 1, column: 1)
        let loc2 = SourceLocation(file: "A.tla", line: 1, column: 1)
        let loc3 = SourceLocation(file: "B.tla", line: 1, column: 1)

        XCTAssertEqual(loc1, loc2)
        XCTAssertNotEqual(loc1, loc3)
    }
}

// MARK: - StateValue Extended Tests

final class ErrorTraceStateValueTests: XCTestCase {

    // MARK: - Basic Type Tests

    func testIntValue() {
        let value = StateValue.int(42)

        if case .int(let v) = value {
            XCTAssertEqual(v, 42)
        } else {
            XCTFail("Expected int value")
        }

        XCTAssertEqual(value.displayString, "42")
    }

    func testStringValue() {
        let value = StateValue.string("hello")

        if case .string(let v) = value {
            XCTAssertEqual(v, "hello")
        } else {
            XCTFail("Expected string value")
        }

        XCTAssertEqual(value.displayString, "\"hello\"")
    }

    func testBoolValue() {
        let trueVal = StateValue.bool(true)
        let falseVal = StateValue.bool(false)

        XCTAssertEqual(trueVal.displayString, "TRUE")
        XCTAssertEqual(falseVal.displayString, "FALSE")
    }

    func testModelValue() {
        let value = StateValue.modelValue("v1")
        XCTAssertEqual(value.displayString, "v1")
    }

    // MARK: - Collection Type Tests

    func testEmptySet() {
        let value = StateValue.set([])
        XCTAssertEqual(value.displayString, "{}")
    }

    func testSetWithElements() {
        let value = StateValue.set([
            StateValueWrapper(.int(1)),
            StateValueWrapper(.int(2)),
            StateValueWrapper(.int(3))
        ])

        // Set display is sorted
        XCTAssertTrue(value.displayString.contains("{"))
        XCTAssertTrue(value.displayString.contains("}"))
        XCTAssertTrue(value.displayString.contains("1"))
        XCTAssertTrue(value.displayString.contains("2"))
        XCTAssertTrue(value.displayString.contains("3"))
    }

    func testEmptySequence() {
        let value = StateValue.sequence([])
        XCTAssertEqual(value.displayString, "<<>>")
    }

    func testSequenceWithElements() {
        let value = StateValue.sequence([.int(1), .int(2), .int(3)])
        XCTAssertEqual(value.displayString, "<<1, 2, 3>>")
    }

    func testEmptyRecord() {
        let value = StateValue.record([:])
        XCTAssertEqual(value.displayString, "[]")
    }

    func testRecordWithFields() {
        let value = StateValue.record(["a": .int(1), "b": .string("x")])

        // Fields are sorted alphabetically
        let display = value.displayString
        XCTAssertTrue(display.contains("["))
        XCTAssertTrue(display.contains("]"))
        XCTAssertTrue(display.contains("a |->"))
        XCTAssertTrue(display.contains("b |->"))
    }

    func testTuple() {
        let value = StateValue.tuple([.int(1), .string("a"), .bool(true)])
        XCTAssertEqual(value.displayString, "<<1, \"a\", TRUE>>")
    }

    func testEmptyFunction() {
        let value = StateValue.function([:])
        XCTAssertEqual(value.displayString, "[x \\in {} |-> x]")
    }

    func testFunctionWithMapping() {
        let value = StateValue.function([
            StateValueWrapper(.int(1)): .string("a"),
            StateValueWrapper(.int(2)): .string("b")
        ])

        let display = value.displayString
        XCTAssertTrue(display.contains(":>"))
        XCTAssertTrue(display.contains("@@"))
    }

    // MARK: - Equality Tests

    func testStateValueEquality() {
        XCTAssertEqual(StateValue.int(5), StateValue.int(5))
        XCTAssertNotEqual(StateValue.int(5), StateValue.int(6))

        XCTAssertEqual(StateValue.string("a"), StateValue.string("a"))
        XCTAssertNotEqual(StateValue.string("a"), StateValue.string("b"))

        XCTAssertEqual(StateValue.bool(true), StateValue.bool(true))
        XCTAssertNotEqual(StateValue.bool(true), StateValue.bool(false))

        XCTAssertEqual(
            StateValue.sequence([.int(1), .int(2)]),
            StateValue.sequence([.int(1), .int(2)])
        )
        XCTAssertNotEqual(
            StateValue.sequence([.int(1), .int(2)]),
            StateValue.sequence([.int(2), .int(1)])
        )
    }

    // MARK: - Codable Tests

    func testStateValueCodableInt() throws {
        let value = StateValue.int(42)
        let data = try JSONEncoder().encode(value)
        let decoded = try JSONDecoder().decode(StateValue.self, from: data)

        XCTAssertEqual(value, decoded)
    }

    func testStateValueCodableString() throws {
        let value = StateValue.string("test")
        let data = try JSONEncoder().encode(value)
        let decoded = try JSONDecoder().decode(StateValue.self, from: data)

        XCTAssertEqual(value, decoded)
    }

    func testStateValueCodableBool() throws {
        for boolVal in [true, false] {
            let value = StateValue.bool(boolVal)
            let data = try JSONEncoder().encode(value)
            let decoded = try JSONDecoder().decode(StateValue.self, from: data)

            XCTAssertEqual(value, decoded)
        }
    }

    func testStateValueCodableSequence() throws {
        let value = StateValue.sequence([.int(1), .int(2), .int(3)])
        let data = try JSONEncoder().encode(value)
        let decoded = try JSONDecoder().decode(StateValue.self, from: data)

        XCTAssertEqual(value, decoded)
    }

    func testStateValueCodableRecord() throws {
        let value = StateValue.record(["x": .int(1), "y": .int(2)])
        let data = try JSONEncoder().encode(value)
        let decoded = try JSONDecoder().decode(StateValue.self, from: data)

        XCTAssertEqual(value, decoded)
    }

    func testStateValueCodableModelValue() throws {
        let value = StateValue.modelValue("v1")
        let data = try JSONEncoder().encode(value)
        let decoded = try JSONDecoder().decode(StateValue.self, from: data)

        XCTAssertEqual(value, decoded)
    }

    // MARK: - Nested Values Tests

    func testNestedSequence() {
        let value = StateValue.sequence([
            .sequence([.int(1), .int(2)]),
            .sequence([.int(3), .int(4)])
        ])

        let display = value.displayString
        XCTAssertTrue(display.contains("<<"))
        XCTAssertTrue(display.contains(">>"))
    }

    func testNestedRecord() {
        let value = StateValue.record([
            "outer": .record(["inner": .int(42)])
        ])

        let display = value.displayString
        XCTAssertTrue(display.contains("["))
        XCTAssertTrue(display.contains("outer"))
        XCTAssertTrue(display.contains("inner"))
    }

    // MARK: - StateValueWrapper Tests

    func testStateValueWrapperEquality() {
        let wrapper1 = StateValueWrapper(.int(5))
        let wrapper2 = StateValueWrapper(.int(5))
        let wrapper3 = StateValueWrapper(.int(6))

        XCTAssertEqual(wrapper1, wrapper2)
        XCTAssertNotEqual(wrapper1, wrapper3)
    }

    func testStateValueWrapperHashable() {
        var set: Set<StateValueWrapper> = []
        set.insert(StateValueWrapper(.int(1)))
        set.insert(StateValueWrapper(.int(1)))  // Duplicate
        set.insert(StateValueWrapper(.int(2)))

        XCTAssertEqual(set.count, 2)
    }

    func testStateValueWrapperInDictionary() {
        var dict: [StateValueWrapper: String] = [:]
        dict[StateValueWrapper(.int(1))] = "one"
        dict[StateValueWrapper(.int(2))] = "two"

        XCTAssertEqual(dict[StateValueWrapper(.int(1))], "one")
        XCTAssertEqual(dict[StateValueWrapper(.int(2))], "two")
    }

    // MARK: - Edge Cases

    func testNegativeInt() {
        let value = StateValue.int(-42)
        XCTAssertEqual(value.displayString, "-42")
    }

    func testEmptyString() {
        let value = StateValue.string("")
        XCTAssertEqual(value.displayString, "\"\"")
    }

    func testStringWithSpecialCharacters() {
        let value = StateValue.string("hello\nworld")
        XCTAssertTrue(value.displayString.contains("hello"))
        XCTAssertTrue(value.displayString.contains("world"))
    }

    func testLargeInt() {
        let value = StateValue.int(Int.max)
        XCTAssertEqual(value.displayString, "\(Int.max)")
    }
}
