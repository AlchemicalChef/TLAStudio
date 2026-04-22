import XCTest
@testable import TLAStudioApp

final class CheckpointManagerTests: TempDirectoryTestCase {

    // MARK: - Discovery Tests

    func testDiscoverCheckpointsInEmptyDirectory() async throws {
        let checkpoints = try await CheckpointManager.shared.discoverCheckpoints(
            in: tempDirectory,
            specName: "TestSpec"
        )
        XCTAssertTrue(checkpoints.isEmpty)
    }

    func testDiscoverCheckpointsFindsValidCheckpoints() async throws {
        // Create some checkpoint directories
        let checkpoint1 = tempDirectory.appendingPathComponent("24-01-15-10-30-00")
        let checkpoint2 = tempDirectory.appendingPathComponent("24-01-16-11-30-00")

        try FileManager.default.createDirectory(at: checkpoint1, withIntermediateDirectories: true)
        try FileManager.default.createDirectory(at: checkpoint2, withIntermediateDirectories: true)

        // Create a checkpoint file in one
        try "test".write(to: checkpoint1.appendingPathComponent("queue.chkpt"), atomically: true, encoding: .utf8)

        let checkpoints = try await CheckpointManager.shared.discoverCheckpoints(
            in: tempDirectory,
            specName: "TestSpec"
        )

        XCTAssertEqual(checkpoints.count, 2)
        // Should be sorted newest first
        XCTAssertEqual(checkpoints.first?.id, "24-01-16-11-30-00")
    }

    func testDiscoverCheckpointsIgnoresFiles() async throws {
        // Create a file (not directory)
        let filePath = tempDirectory.appendingPathComponent("24-01-15-10-30-00.txt")
        try "test".write(to: filePath, atomically: true, encoding: .utf8)

        let checkpoints = try await CheckpointManager.shared.discoverCheckpoints(
            in: tempDirectory,
            specName: "TestSpec"
        )

        XCTAssertTrue(checkpoints.isEmpty)
    }

    func testDiscoverCheckpointsIgnoresInvalidDirectoryNames() async throws {
        // Create directory with invalid name
        let invalidDir = tempDirectory.appendingPathComponent("not-a-checkpoint")
        try FileManager.default.createDirectory(at: invalidDir, withIntermediateDirectories: true)

        let checkpoints = try await CheckpointManager.shared.discoverCheckpoints(
            in: tempDirectory,
            specName: "TestSpec"
        )

        XCTAssertTrue(checkpoints.isEmpty)
    }

    // MARK: - Validation Tests

    func testValidateExistingCheckpoint() async throws {
        let checkpointDir = tempDirectory.appendingPathComponent("24-01-15-10-30-00")
        try FileManager.default.createDirectory(at: checkpointDir, withIntermediateDirectories: true)

        let checkpoint = CheckpointInfo(
            id: "24-01-15-10-30-00",
            directoryURL: checkpointDir,
            createdAt: Date(),
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )

        let isValid = await CheckpointManager.shared.validateCheckpoint(checkpoint)
        XCTAssertTrue(isValid)
    }

    func testValidateNonExistentCheckpoint() async throws {
        let checkpoint = CheckpointInfo(
            id: "nonexistent",
            directoryURL: tempDirectory.appendingPathComponent("nonexistent"),
            createdAt: Date(),
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )

        let isValid = await CheckpointManager.shared.validateCheckpoint(checkpoint)
        XCTAssertFalse(isValid)
    }

    // MARK: - Cleanup Tests

    func testCleanupKeepsRecentCheckpoints() async throws {
        // Create 5 checkpoints
        for i in 0..<5 {
            let dir = tempDirectory.appendingPathComponent("24-01-\(String(format: "%02d", 10 + i))-10-30-00")
            try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
            // Add a small delay to ensure different modification times
        }

        let removed = try await CheckpointManager.shared.cleanupOldCheckpoints(
            in: tempDirectory,
            keepRecent: 3
        )

        XCTAssertEqual(removed, 2)

        // Verify 3 remain
        let remaining = try await CheckpointManager.shared.discoverCheckpoints(
            in: tempDirectory,
            specName: "Test"
        )
        XCTAssertEqual(remaining.count, 3)
    }

    func testCleanupWithFewerThanKeepRecent() async throws {
        // Create only 2 checkpoints
        for i in 0..<2 {
            let dir = tempDirectory.appendingPathComponent("24-01-\(String(format: "%02d", 10 + i))-10-30-00")
            try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        }

        let removed = try await CheckpointManager.shared.cleanupOldCheckpoints(
            in: tempDirectory,
            keepRecent: 3
        )

        XCTAssertEqual(removed, 0)
    }

    // MARK: - Delete Tests

    func testDeleteCheckpoint() async throws {
        let checkpointDir = tempDirectory.appendingPathComponent("24-01-15-10-30-00")
        try FileManager.default.createDirectory(at: checkpointDir, withIntermediateDirectories: true)

        let checkpoint = CheckpointInfo(
            id: "24-01-15-10-30-00",
            directoryURL: checkpointDir,
            createdAt: Date(),
            specName: "Test",
            distinctStates: nil,
            statesFound: nil
        )

        try await CheckpointManager.shared.deleteCheckpoint(checkpoint)

        XCTAssertFalse(FileManager.default.fileExists(atPath: checkpointDir.path))
    }

    // MARK: - Path Tests

    func testDefaultMetadir() async {
        let specURL = URL(fileURLWithPath: "/Users/test/MySpec.tla")
        let metadir = await CheckpointManager.shared.defaultMetadir(for: specURL)

        XCTAssertEqual(metadir.lastPathComponent, "MySpec.toolbox")
        XCTAssertEqual(metadir.deletingLastPathComponent().path, "/Users/test")
    }

    func testEnsureMetadir() async throws {
        let specURL = tempDirectory.appendingPathComponent("TestSpec.tla")
        let metadir = try await CheckpointManager.shared.ensureMetadir(for: specURL)

        XCTAssertTrue(FileManager.default.fileExists(atPath: metadir.path))
        XCTAssertEqual(metadir.lastPathComponent, "TestSpec.toolbox")
    }
}

// MARK: - Graphviz Process Manager Tests

final class GraphvizProcessManagerTests: XCTestCase {

    func testGraphvizAvailabilityCheck() async {
        // This test just verifies the check doesn't crash
        let isAvailable = await GraphvizProcessManager.shared.isGraphvizAvailable
        // We can't assert true/false since it depends on the system
        print("Graphviz available: \(isAvailable)")
    }

    func testRenderDOTFormat() async throws {
        // DOT format should work even without graphviz installed
        let dotSource = """
        digraph Test {
            A -> B;
        }
        """

        let data = try await GraphvizProcessManager.shared.render(
            dotSource: dotSource,
            format: .dot
        )

        let output = String(data: data, encoding: .utf8)
        XCTAssertNotNil(output)
        XCTAssertTrue(output?.contains("digraph Test") ?? false)
    }

    func testRenderSVGRequiresGraphviz() async {
        let isAvailable = await GraphvizProcessManager.shared.isGraphvizAvailable

        let dotSource = """
        digraph Test {
            A -> B;
        }
        """

        do {
            let data = try await GraphvizProcessManager.shared.render(
                dotSource: dotSource,
                format: .svg
            )

            if isAvailable {
                // Should succeed if graphviz is installed
                XCTAssertFalse(data.isEmpty)
                let svg = String(data: data, encoding: .utf8)
                XCTAssertTrue(svg?.contains("<svg") ?? false)
            }
        } catch GraphvizError.notInstalled {
            // Expected if graphviz is not installed
            XCTAssertFalse(isAvailable)
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
    }

    func testRenderTraceToSVG() async {
        let isAvailable = await GraphvizProcessManager.shared.isGraphvizAvailable
        guard isAvailable else {
            print("Skipping test - Graphviz not installed")
            return
        }

        let trace = ErrorTrace(
            type: .invariantViolation,
            message: "Test violation",
            states: [
                TraceState(id: 0, action: nil, variables: ["x": .int(0)]),
                TraceState(id: 1, action: "Inc", variables: ["x": .int(1)])
            ]
        )

        do {
            let data = try await GraphvizProcessManager.shared.render(
                trace: trace,
                format: .svg
            )

            XCTAssertFalse(data.isEmpty)
            let svg = String(data: data, encoding: .utf8)
            XCTAssertTrue(svg?.contains("<svg") ?? false)
        } catch {
            XCTFail("Failed to render trace: \(error)")
        }
    }

    func testGraphvizVersion() async {
        let isAvailable = await GraphvizProcessManager.shared.isGraphvizAvailable
        guard isAvailable else {
            print("Skipping test - Graphviz not installed")
            return
        }

        do {
            let version = try await GraphvizProcessManager.shared.version()
            XCTAssertFalse(version.isEmpty)
            print("Graphviz version: \(version)")
        } catch {
            XCTFail("Failed to get version: \(error)")
        }
    }

    func testInstallationInstructions() {
        let instructions = GraphvizProcessManager.installationInstructions
        XCTAssertTrue(instructions.contains("brew install graphviz"))
        XCTAssertTrue(instructions.contains("graphviz.org"))
    }
}

// MARK: - Error Tests

final class GraphvizErrorTests: XCTestCase {

    func testErrorDescriptions() {
        let errors: [GraphvizError] = [
            .notInstalled,
            .failedToStart(NSError(domain: "test", code: 1)),
            .renderingFailed("test message"),
            .encodingError,
            .emptyOutput
        ]

        for error in errors {
            XCTAssertNotNil(error.errorDescription)
            XCTAssertFalse(error.errorDescription?.isEmpty ?? true)
        }
    }
}

final class CheckpointErrorTests: XCTestCase {

    func testErrorDescriptions() {
        let errors: [CheckpointError] = [
            .notFound("test-id"),
            .invalidCheckpoint("test-id"),
            .recoveryFailed("test message"),
            .cleanupFailed("test message")
        ]

        for error in errors {
            XCTAssertNotNil(error.errorDescription)
            XCTAssertFalse(error.errorDescription?.isEmpty ?? true)
        }
    }
}
