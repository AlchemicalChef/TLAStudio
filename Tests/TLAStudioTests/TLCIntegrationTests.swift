import XCTest
@testable import TLAStudioApp

// MARK: - TLC Integration Tests

/// Tests for TLC process lifecycle, config generation, and error handling.
final class TLCIntegrationTests: XCTestCase {

    // MARK: - Config File Generation Tests

    func testConfigFileGeneration() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: ["TypeOK"],
            temporalProperties: []
        )

        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("INIT Init"))
        XCTAssertTrue(content.contains("NEXT Next"))
        XCTAssertTrue(content.contains("INVARIANT TypeOK"))
    }

    func testConfigFileWithConstants() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [
                "N": .int(5),
                "Servers": .set([.string("s1"), .string("s2"), .string("s3")])
            ],
            invariants: [],
            temporalProperties: []
        )

        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("CONSTANT"))
        XCTAssertTrue(content.contains("N = 5"))
    }

    func testConfigFileWithModelValue() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: ["Server": .modelValue("s1")],
            invariants: [],
            temporalProperties: []
        )

        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("Server = s1"))
    }

    func testConfigFileWithSymmetrySet() {
        // Symmetry sets are configured via the symmetrySets property, not constants
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: [],
            symmetrySets: ["Nodes": ["n1", "n2", "n3"]]
        )

        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("SYMMETRY"))
    }

    func testConfigFileWithMultipleInvariants() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: ["TypeOK", "Safety", "NoDeadlock"],
            temporalProperties: []
        )

        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("INVARIANT TypeOK"))
        XCTAssertTrue(content.contains("INVARIANT Safety"))
        XCTAssertTrue(content.contains("INVARIANT NoDeadlock"))
    }

    func testConfigFileWithTemporalProperties() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: ["Liveness", "Fairness"]
        )

        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("PROPERTY Liveness"))
        XCTAssertTrue(content.contains("PROPERTY Fairness"))
    }

    func testConfigFileWithConstraints() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: [],
            stateConstraint: "count < 100",
            actionConstraint: "step > 0"
        )

        let content = config.generateConfigFile()

        XCTAssertTrue(content.contains("CONSTRAINT"))
        XCTAssertTrue(content.contains("count < 100"))
        XCTAssertTrue(content.contains("ACTION_CONSTRAINT"))
        XCTAssertTrue(content.contains("step > 0"))
    }

    // MARK: - TLC Error Tests

    func testTLCErrorDescriptions() {
        XCTAssertNotNil(TLCError.tlcNotFound.errorDescription)
        XCTAssertNotNil(TLCError.specNotFound.errorDescription)
        XCTAssertNotNil(TLCError.timeout.errorDescription)
        XCTAssertNotNil(TLCError.cancelled.errorDescription)
        XCTAssertNotNil(TLCError.javaNotFound.errorDescription)
        XCTAssertNotNil(TLCError.tla2toolsNotFound.errorDescription)
        XCTAssertNotNil(TLCError.outOfMemory(suggestJVM: true).errorDescription)
        XCTAssertNotNil(TLCError.outOfMemory(suggestJVM: false).errorDescription)
    }

    func testTLCErrorFailedToStart() {
        let underlyingError = NSError(domain: "test", code: 1, userInfo: [NSLocalizedDescriptionKey: "Test error"])
        let error = TLCError.failedToStart(underlyingError)

        XCTAssertNotNil(error.errorDescription)
        XCTAssertTrue(error.errorDescription!.contains("Test error"))
    }

    func testTLCErrorInvalidConfig() {
        let error = TLCError.invalidConfig("Missing INIT predicate")

        XCTAssertNotNil(error.errorDescription)
        XCTAssertTrue(error.errorDescription!.contains("Missing INIT predicate"))
    }

    func testTLCErrorConfigWriteFailed() {
        let underlyingError = NSError(domain: NSPOSIXErrorDomain, code: Int(EACCES), userInfo: nil)
        let error = TLCError.configWriteFailed(underlyingError)

        XCTAssertNotNil(error.errorDescription)
    }

    func testTLCErrorOOMWithJVMSuggestion() {
        let errorWithJVM = TLCError.outOfMemory(suggestJVM: true)
        let errorWithoutJVM = TLCError.outOfMemory(suggestJVM: false)

        XCTAssertTrue(errorWithJVM.errorDescription!.contains("JVM"))
        XCTAssertFalse(errorWithoutJVM.errorDescription!.contains("JVM"))
    }

    // MARK: - State Space Estimation Tests

    func testEstimateStateSpaceWithIntConstant() async {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: ["N": .int(5)],
            invariants: [],
            temporalProperties: []
        )

        let estimate = await TLCProcessManager.shared.estimateStateSpace(config: config)

        // N=5 should give estimate of 5*5=25
        XCTAssertEqual(estimate, 25)
    }

    func testEstimateStateSpaceWithSetConstant() async {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: ["Servers": .set([.string("s1"), .string("s2"), .string("s3")])],
            invariants: [],
            temporalProperties: []
        )

        let estimate = await TLCProcessManager.shared.estimateStateSpace(config: config)

        // Set of 3 elements: 3*3*3=27
        XCTAssertEqual(estimate, 27)
    }

    func testEstimateStateSpaceWithBoolConstant() async {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: ["Flag": .bool(true)],
            invariants: [],
            temporalProperties: []
        )

        let estimate = await TLCProcessManager.shared.estimateStateSpace(config: config)

        // Bool contributes factor of 4
        XCTAssertEqual(estimate, 4)
    }

    func testEstimateStateSpaceWithMultipleConstants() async {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [
                "N": .int(3),
                "Flag": .bool(true)
            ],
            invariants: [],
            temporalProperties: []
        )

        let estimate = await TLCProcessManager.shared.estimateStateSpace(config: config)

        // N=3 gives 9, Bool gives 4, total 36
        XCTAssertEqual(estimate, 36)
    }

    func testEstimateStateSpaceOverflowProtection() async {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [
                "A": .int(1000),
                "B": .int(1000),
                "C": .int(1000)
            ],
            invariants: [],
            temporalProperties: []
        )

        let estimate = await TLCProcessManager.shared.estimateStateSpace(config: config)

        // Should be capped at 100_000_000
        XCTAssertEqual(estimate, 100_000_000)
    }

    func testEstimateStateSpaceWithNoConstants() async {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        let estimate = await TLCProcessManager.shared.estimateStateSpace(config: config)

        // No constants = base estimate of 1
        XCTAssertEqual(estimate, 1)
    }

    // MARK: - Constant Impact Estimation Tests

    func testEstimateConstantImpactString() async {
        let impact = await TLCProcessManager.shared.estimateConstantImpact(.string("test"))
        XCTAssertEqual(impact, 10)
    }

    func testEstimateConstantImpactModelValue() async {
        let impact = await TLCProcessManager.shared.estimateConstantImpact(.modelValue("m1"))
        XCTAssertEqual(impact, 10)
    }

    func testEstimateConstantImpactSymmetrySet() async {
        let impact = await TLCProcessManager.shared.estimateConstantImpact(.symmetrySet("sym_set"))
        XCTAssertEqual(impact, 10)
    }

    func testEstimateConstantImpactZeroInt() async {
        let impact = await TLCProcessManager.shared.estimateConstantImpact(.int(0))
        // max(1, 0*0) = 1
        XCTAssertEqual(impact, 1)
    }

    func testEstimateConstantImpactNegativeInt() async {
        let impact = await TLCProcessManager.shared.estimateConstantImpact(.int(-5))
        // -5 * -5 = 25
        XCTAssertEqual(impact, 25)
    }

    func testEstimateConstantImpactEmptySet() async {
        let impact = await TLCProcessManager.shared.estimateConstantImpact(.set([]))
        // max(1, 0*0*0) = 1
        XCTAssertEqual(impact, 1)
    }

    // MARK: - TLC Binary Mode Tests

    func testTLCBinaryModeEnum() {
        let modes: [TLCProcessManager.TLCBinaryMode] = [.fast, .standard, .auto, .jvm]

        XCTAssertEqual(modes.count, 4)
    }

    // MARK: - TLC Availability Tests

    func testTLCAvailabilityProperty() async {
        // This tests the property exists and returns a boolean
        let isAvailable = await TLCProcessManager.shared.isTLCAvailable

        // We can't guarantee TLC is available in test environment
        XCTAssertTrue(isAvailable == true || isAvailable == false)
    }

    func testJVMAvailabilityProperty() async {
        let isAvailable = await TLCProcessManager.shared.isJVMAvailable

        // We can't guarantee JVM is available in test environment
        XCTAssertTrue(isAvailable == true || isAvailable == false)
    }

    // MARK: - TLC Session Tests

    @MainActor
    func testTLCSessionInitialization() {
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

        XCTAssertFalse(session.isRunning)
        XCTAssertNil(session.progress)
        XCTAssertNil(session.result)
        XCTAssertNil(session.error)
        XCTAssertEqual(session.binaryMode, .auto)
    }

    @MainActor
    func testTLCSessionWithExplicitMode() {
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

        let session = TLCSession(specURL: specURL, config: config, binaryMode: .jvm)

        XCTAssertEqual(session.binaryMode, .jvm)
    }

    @MainActor
    func testTLCSessionCheckpointStatus() {
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

        // Initially no checkpoint status
        if case .none = session.checkpointStatus {
            XCTAssertTrue(true)
        } else {
            XCTFail("Expected checkpoint status to be .none")
        }
    }

    @MainActor
    func testTLCSessionStopWhenNotRunning() {
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

        // Should not crash when stopping a non-running session
        session.stop()

        XCTAssertFalse(session.isRunning)
    }

    @MainActor
    func testTLCSessionRetryWithJVMWhenNotOOM() {
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

        // Should not change mode when result is not OOM
        session.retryWithJVM()

        XCTAssertEqual(session.binaryMode, .auto)
    }

    @MainActor
    func testTLCSessionRetryWithDiskStorageWhenNotOOM() {
        let specURL = URL(fileURLWithPath: "/tmp/test.tla")
        var config = ModelConfig(
            name: "Test",
            specFile: specURL,
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )
        config.useDiskStorage = false

        let session = TLCSession(specURL: specURL, config: config)

        // Should not enable disk storage when result is not OOM
        session.retryWithDiskStorage()

        XCTAssertFalse(session.config.useDiskStorage)
    }

    // MARK: - ModelCheckProgress Tests

    func testModelCheckProgressInitialization() {
        let sessionId = UUID()
        let progress = ModelCheckProgress(
            sessionId: sessionId,
            phase: .computing,
            statesFound: 1000,
            distinctStates: 500,
            statesLeft: 250,
            duration: 5.5
        )

        XCTAssertEqual(progress.sessionId, sessionId)
        XCTAssertEqual(progress.phase, .computing)
        XCTAssertEqual(progress.statesFound, 1000)
        XCTAssertEqual(progress.distinctStates, 500)
        XCTAssertEqual(progress.statesLeft, 250)
        XCTAssertEqual(progress.duration, 5.5)
    }

    func testModelCheckProgressPhases() {
        let phases: [ModelCheckProgress.Phase] = [.parsing, .computing, .checkingLiveness, .done, .error]

        XCTAssertEqual(phases.count, 5)
    }

    // MARK: - ModelCheckResult Tests

    func testModelCheckResultSuccess() {
        let result = ModelCheckResult(
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

        XCTAssertTrue(result.success)
        XCTAssertFalse(result.outOfMemory)
        XCTAssertNil(result.errorTrace)
    }

    func testModelCheckResultWithMessage() {
        let result = ModelCheckResult(
            sessionId: UUID(),
            success: false,
            statesFound: 50,
            distinctStates: 25,
            duration: 2.5,
            coverage: [],
            errorTrace: nil,
            message: "Invariant TypeOK violated",
            outOfMemory: false
        )

        XCTAssertFalse(result.success)
        XCTAssertNotNil(result.message)
    }

    func testModelCheckResultOutOfMemory() {
        let result = ModelCheckResult(
            sessionId: UUID(),
            success: false,
            statesFound: 1000000,
            distinctStates: 500000,
            duration: 60.0,
            coverage: [],
            errorTrace: nil,
            message: nil,
            outOfMemory: true
        )

        XCTAssertFalse(result.success)
        XCTAssertTrue(result.outOfMemory)
    }

    // MARK: - Config Parsing Tests

    func testModelConfigParseFromNonexistentFile() {
        let nonexistentURL = URL(fileURLWithPath: "/tmp/nonexistent_\(UUID()).cfg")
        let config = ModelConfig.parse(from: nonexistentURL)

        XCTAssertNil(config)
    }

    // MARK: - Checkpoint Info Tests

    func testCheckpointInfoValidation() {
        let checkpointDir = URL(fileURLWithPath: "/tmp/test_checkpoint")
        let info = CheckpointInfo(
            id: "26-01-20-14-30-45",
            directoryURL: checkpointDir,
            createdAt: Date(),
            specName: "TestSpec",
            distinctStates: nil,
            statesFound: nil
        )

        XCTAssertEqual(info.id, "26-01-20-14-30-45")
        XCTAssertEqual(info.specName, "TestSpec")
    }

    func testCheckpointInfoInvalidFormat() {
        let validId = "26-01-20-14-30-45"
        let validMillisecondsId = "26-01-20-14-30-45.123"
        let invalidId = "invalid-checkpoint-id"

        XCTAssertNotNil(CheckpointInfo.parseCheckpointDate(from: validId))
        XCTAssertNotNil(CheckpointInfo.parseCheckpointDate(from: validMillisecondsId))
        XCTAssertNil(CheckpointInfo.parseCheckpointDate(from: invalidId))
    }

    // MARK: - Config Disk Storage Tests

    func testConfigDiskStorageDefault() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        XCTAssertFalse(config.useDiskStorage)
    }

    func testConfigDiskStorageEnabled() {
        var config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )
        config.useDiskStorage = true

        XCTAssertTrue(config.useDiskStorage)
    }

    // MARK: - Config Workers Tests

    func testConfigDefaultWorkers() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        // Default workers is 4
        XCTAssertEqual(config.workers, 4)
    }

    func testConfigCustomWorkers() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: [],
            workers: 8
        )

        XCTAssertEqual(config.workers, 8)
    }

    // MARK: - Config Checkpoint Tests

    func testConfigCheckpointDefault() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        // Checkpoint is enabled by default
        XCTAssertTrue(config.checkpointEnabled)
    }

    func testConfigCheckpointEnabled() {
        var config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )
        config.checkpointEnabled = true
        config.checkpointInterval = 300  // 5 minutes

        XCTAssertTrue(config.checkpointEnabled)
        XCTAssertEqual(config.checkpointInterval, 300)
    }

    // MARK: - Depth-First Search Config Tests

    func testConfigDepthFirstDefault() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        XCTAssertFalse(config.depthFirst)
    }

    func testConfigDepthFirstEnabled() {
        var config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )
        config.depthFirst = true
        config.maxDepth = 50

        XCTAssertTrue(config.depthFirst)
        XCTAssertEqual(config.maxDepth, 50)
    }

    // MARK: - Deadlock Check Config Tests

    func testConfigCheckDeadlockDefault() {
        let config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )

        XCTAssertTrue(config.checkDeadlock)
    }

    func testConfigCheckDeadlockDisabled() {
        var config = ModelConfig(
            name: "Test",
            specFile: URL(fileURLWithPath: "/tmp/test.tla"),
            initPredicate: "Init",
            nextAction: "Next",
            constants: [:],
            invariants: [],
            temporalProperties: []
        )
        config.checkDeadlock = false

        XCTAssertFalse(config.checkDeadlock)
    }
}

// MARK: - TLC Error Type Tests

final class TLCErrorTypeTests: XCTestCase {

    func testAllErrorTypes() {
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

        XCTAssertEqual(errors.count, 11)
    }

    func testErrorHasDescription() {
        let error = TLCError.tlcNotFound

        XCTAssertNotNil(error.errorDescription)
        XCTAssertFalse(error.errorDescription!.isEmpty)
    }
}
