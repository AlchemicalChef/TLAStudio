import XCTest
@testable import TLAStudioApp

final class DOTGeneratorTests: XCTestCase {

    // MARK: - Basic Generation Tests

    func testGenerateSimpleTrace() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Invariant SafetyInvariant is violated",
            states: [
                TraceState(id: 0, action: nil, variables: ["count": .int(0)]),
                TraceState(id: 1, action: "Increment", variables: ["count": .int(1)]),
                TraceState(id: 2, action: "Increment", variables: ["count": .int(2)])
            ]
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        // Verify basic structure
        XCTAssertTrue(dot.contains("digraph ErrorTrace"))
        XCTAssertTrue(dot.contains("state0"))
        XCTAssertTrue(dot.contains("state1"))
        XCTAssertTrue(dot.contains("state2"))
        XCTAssertTrue(dot.contains("state0 -> state1"))
        XCTAssertTrue(dot.contains("state1 -> state2"))
    }

    func testGenerateTraceWithLivenessLoop() {
        let trace = ErrorTrace(
            type: .livenessViolation,
            message: "Temporal property violated",
            states: [
                TraceState(id: 0, action: nil, variables: ["x": .int(0)]),
                TraceState(id: 1, action: "Step", variables: ["x": .int(1)]),
                TraceState(id: 2, action: "Step", variables: ["x": .int(2)]),
                TraceState(id: 3, action: "Loop", variables: ["x": .int(1)])
            ],
            loopStart: 1
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        // Verify loop back-edge
        XCTAssertTrue(dot.contains("state3 -> state1"))
        XCTAssertTrue(dot.contains("style=dashed"))
        XCTAssertTrue(dot.contains("color=red"))
    }

    func testGenerateTraceWithComplexVariables() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "TypeOK violated",
            states: [
                TraceState(id: 0, action: nil, variables: [
                    "set": .set([StateValueWrapper(.int(1)), StateValueWrapper(.int(2))]),
                    "record": .record(["a": .int(1), "b": .string("hello")]),
                    "seq": .sequence([.int(1), .int(2), .int(3)])
                ])
            ]
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        XCTAssertTrue(dot.contains("state0"))
        // Variables should be shown in the label
        XCTAssertTrue(dot.contains("set") || dot.contains("record") || dot.contains("seq"))
    }

    func testConfigurationDirections() {
        let trace = ErrorTrace(
            type: .deadlock,
            message: "Deadlock reached",
            states: [
                TraceState(id: 0, action: nil, variables: ["x": .int(0)]),
                TraceState(id: 1, action: "Step", variables: ["x": .int(1)])
            ]
        )

        for direction in DOTGenerator.Configuration.Direction.allCases {
            var config = DOTGenerator.Configuration()
            config.direction = direction
            let generator = DOTGenerator(configuration: config)
            let dot = generator.generate(from: trace)

            XCTAssertTrue(dot.contains("rankdir=\(direction.rawValue)"))
        }
    }

    func testConfigurationHideVariables() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: [
                TraceState(id: 0, action: nil, variables: ["x": .int(0), "y": .int(1)])
            ]
        )

        var config = DOTGenerator.Configuration()
        config.showVariables = false
        let generator = DOTGenerator(configuration: config)
        let dot = generator.generate(from: trace)

        // When variables are hidden, we shouldn't see the separator line
        XCTAssertFalse(dot.contains("─────────"))
    }

    // MARK: - Node Styling Tests

    func testInitialStateIsGreen() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: [
                TraceState(id: 0, action: nil, variables: [:])
            ]
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        // Initial state should have green fill
        XCTAssertTrue(dot.contains("#d4edda"))
    }

    func testErrorStateIsRed() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: [
                TraceState(id: 0, action: nil, variables: [:]),
                TraceState(id: 1, action: "Error", variables: [:])
            ]
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        // Final error state should have red fill
        XCTAssertTrue(dot.contains("#f8d7da"))
    }

    func testLoopStartIsOrange() {
        let trace = ErrorTrace(
            type: .livenessViolation,
            message: "Test",
            states: [
                TraceState(id: 0, action: nil, variables: [:]),
                TraceState(id: 1, action: "Loop", variables: [:]),
                TraceState(id: 2, action: "Back", variables: [:])
            ],
            loopStart: 1
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        // Loop start state should have orange fill
        XCTAssertTrue(dot.contains("#fff3cd"))
    }

    func testRoundedBoxKeepsFillStyle() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: [
                TraceState(id: 0, action: nil, variables: [:])
            ]
        )
        var config = DOTGenerator.Configuration()
        config.nodeShape = .roundedBox

        let generator = DOTGenerator(configuration: config)
        let dot = generator.generate(from: trace)

        XCTAssertTrue(dot.contains("shape=box"))
        XCTAssertTrue(dot.contains("style=\"filled,rounded\""))
        XCTAssertTrue(dot.contains("#d4edda"))
    }

    // MARK: - Edge Cases

    func testEmptyTrace() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Test",
            states: []
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        XCTAssertTrue(dot.contains("digraph ErrorTrace"))
        XCTAssertFalse(dot.contains("state0"))
    }

    func testSingleStateTrace() {
        let trace = ErrorTrace(
            type: .deadlock,
            message: "Deadlock in initial state",
            states: [
                TraceState(id: 0, action: nil, variables: ["x": .int(0)])
            ]
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        XCTAssertTrue(dot.contains("state0"))
        XCTAssertFalse(dot.contains("->"))  // No edges for single state
    }

    func testSpecialCharacterEscaping() {
        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Test with \"quotes\" and <brackets>",
            states: [
                TraceState(id: 0, action: nil, variables: ["msg": .string("Hello \"World\"")])
            ]
        )

        let generator = DOTGenerator()
        let dot = generator.generate(from: trace)

        // Should escape special characters
        XCTAssertTrue(dot.contains("\\\"") || !dot.contains("\"World\""))
    }
}

// MARK: - Checkpoint Info Tests

final class CheckpointInfoTests: XCTestCase {

    func testParseValidCheckpointDirectory() {
        let tempDir = FileManager.default.temporaryDirectory
        let checkpointDir = tempDir.appendingPathComponent("24-06-15-10-30-45")

        // Create the directory
        try? FileManager.default.createDirectory(at: checkpointDir, withIntermediateDirectories: true)
        try? "test".write(to: checkpointDir.appendingPathComponent("queue.chkpt"), atomically: true, encoding: .utf8)
        defer { try? FileManager.default.removeItem(at: checkpointDir) }

        let info = CheckpointInfo.from(directoryURL: checkpointDir, specName: "TestSpec")

        XCTAssertNotNil(info)
        XCTAssertEqual(info?.id, "24-06-15-10-30-45")
        XCTAssertEqual(info?.specName, "TestSpec")
    }

    func testCheckpointDisplayName() {
        let info = CheckpointInfo(
            id: "test-checkpoint",
            directoryURL: URL(fileURLWithPath: "/tmp/test"),
            createdAt: Date(),
            specName: "MySpec",
            distinctStates: 1000,
            statesFound: 5000
        )

        XCTAssertTrue(info.displayName.contains("MySpec"))
    }

    func testCheckpointAgeDescription() {
        let info = CheckpointInfo(
            id: "test",
            directoryURL: URL(fileURLWithPath: "/tmp/test"),
            createdAt: Date().addingTimeInterval(-3600), // 1 hour ago
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )

        // Should contain some time reference
        XCTAssertFalse(info.ageDescription.isEmpty)
    }

    func testCheckpointIsValid() {
        let tempDir = FileManager.default.temporaryDirectory
        let checkpointDir = tempDir.appendingPathComponent("valid-checkpoint-\(UUID().uuidString)")

        // Create directory
        try? FileManager.default.createDirectory(at: checkpointDir, withIntermediateDirectories: true)
        try? "test".write(to: checkpointDir.appendingPathComponent("states.chkpt"), atomically: true, encoding: .utf8)
        defer { try? FileManager.default.removeItem(at: checkpointDir) }

        let info = CheckpointInfo(
            id: "test",
            directoryURL: checkpointDir,
            createdAt: Date(),
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )

        XCTAssertTrue(info.isValid)
    }

    func testCheckpointIsInvalidForMissingDirectory() {
        let info = CheckpointInfo(
            id: "test",
            directoryURL: URL(fileURLWithPath: "/nonexistent/path/\(UUID().uuidString)"),
            createdAt: Date(),
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )

        XCTAssertFalse(info.isValid)
    }
}

// MARK: - Checkpoint Status Tests

final class CheckpointStatusTests: XCTestCase {

    func testStatusNone() {
        let status = CheckpointStatus.none
        XCTAssertFalse(status.isActive)
        XCTAssertTrue(status.displayMessage.isEmpty)
    }

    func testStatusSaving() {
        let status = CheckpointStatus.saving
        XCTAssertTrue(status.isActive)
        XCTAssertTrue(status.displayMessage.contains("Creating"))
    }

    func testStatusRestoring() {
        let checkpoint = CheckpointInfo(
            id: "test",
            directoryURL: URL(fileURLWithPath: "/tmp"),
            createdAt: Date(),
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )
        let status = CheckpointStatus.restoring(checkpoint)
        XCTAssertTrue(status.isActive)
        XCTAssertTrue(status.displayMessage.contains("Restoring"))
    }

    func testStatusEquality() {
        XCTAssertEqual(CheckpointStatus.none, CheckpointStatus.none)
        XCTAssertEqual(CheckpointStatus.saving, CheckpointStatus.saving)
        XCTAssertNotEqual(CheckpointStatus.none, CheckpointStatus.saving)
    }
}

// MARK: - Model Config Tests

final class ModelConfigCheckpointTests: XCTestCase {

    func testDefaultCheckpointSettings() {
        let config = ModelConfig(
            specFile: URL(fileURLWithPath: "/tmp/test.tla")
        )

        XCTAssertTrue(config.checkpointEnabled)
        XCTAssertFalse(config.autoCleanupCheckpoints)
        XCTAssertEqual(config.checkpointInterval, 300) // 5 minutes
    }

    func testCustomCheckpointSettings() {
        let config = ModelConfig(
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            checkpointInterval: 600,
            checkpointDir: URL(fileURLWithPath: "/tmp/checkpoints"),
            checkpointEnabled: false,
            autoCleanupCheckpoints: true
        )

        XCTAssertFalse(config.checkpointEnabled)
        XCTAssertTrue(config.autoCleanupCheckpoints)
        XCTAssertEqual(config.checkpointInterval, 600)
        XCTAssertEqual(config.checkpointDir?.path, "/tmp/checkpoints")
    }
}

// MARK: - Graph Export Format Tests

final class GraphExportFormatTests: XCTestCase {

    func testAllFormatsHaveExtensions() {
        for format in GraphExportFormat.allCases {
            XCTAssertFalse(format.fileExtension.isEmpty)
            XCTAssertEqual(format.fileExtension, format.rawValue)
        }
    }

    func testAllFormatsHaveDisplayNames() {
        for format in GraphExportFormat.allCases {
            XCTAssertFalse(format.displayName.isEmpty)
        }
    }

    func testGraphvizFormats() {
        XCTAssertEqual(GraphExportFormat.svg.graphvizFormat, "svg")
        XCTAssertEqual(GraphExportFormat.png.graphvizFormat, "png")
        XCTAssertEqual(GraphExportFormat.pdf.graphvizFormat, "pdf")
        XCTAssertEqual(GraphExportFormat.dot.graphvizFormat, "dot")
    }
}
