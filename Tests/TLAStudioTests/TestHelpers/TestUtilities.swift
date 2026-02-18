import XCTest
@testable import TLAStudioApp

// MARK: - Temp Directory Test Case

/// Base class for tests that need a temporary directory.
/// Provides automatic setUp/tearDown for temp directory lifecycle.
class TempDirectoryTestCase: XCTestCase {

    var tempDirectory: URL!

    override func setUp() async throws {
        try await super.setUp()
        tempDirectory = FileManager.default.temporaryDirectory
            .appendingPathComponent("TLAStudioTests-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: tempDirectory, withIntermediateDirectories: true)
    }

    override func tearDown() async throws {
        if let tempDirectory = tempDirectory {
            try? FileManager.default.removeItem(at: tempDirectory)
        }
        try await super.tearDown()
    }
}

// MARK: - Test Factories

/// Centralized factory methods for creating test data objects.
enum TestFactories {

    /// Create a ProofObligation with sensible defaults for testing.
    static func makeProofObligation(
        id: UUID = UUID(),
        startLine: Int = 1,
        endLine: Int? = nil,
        startColumn: Int = 1,
        endColumn: Int = 50,
        status: ProofStatus = .pending,
        kind: ObligationKind = .step,
        backend: ProverBackend? = nil,
        duration: TimeInterval? = nil,
        errorMessage: String? = nil,
        fileURL: URL = URL(fileURLWithPath: "/tmp/test.tla")
    ) -> ProofObligation {
        ProofObligation(
            id: id,
            fingerprint: "fp_\(startLine)",
            location: ProofSourceLocation(
                fileURL: fileURL,
                startLine: startLine,
                startColumn: startColumn,
                endLine: endLine ?? startLine,
                endColumn: endColumn
            ),
            kind: kind,
            status: status,
            backend: backend,
            duration: duration,
            errorMessage: errorMessage,
            obligationText: "obligation at line \(startLine)"
        )
    }

    /// Create a ModelConfig with sensible defaults for testing.
    static func makeModelConfig(
        name: String = "Test",
        specFile: URL = URL(fileURLWithPath: "/tmp/test.tla"),
        initPredicate: String = "Init",
        nextAction: String = "Next",
        constants: [String: ConstantValue] = [:],
        invariants: [String] = [],
        temporalProperties: [String] = [],
        stateConstraint: String? = nil,
        actionConstraint: String? = nil
    ) -> ModelConfig {
        ModelConfig(
            specFile: specFile,
            initPredicate: initPredicate,
            nextAction: nextAction,
            constants: constants,
            invariants: invariants,
            temporalProperties: temporalProperties,
            stateConstraint: stateConstraint,
            actionConstraint: actionConstraint
        )
    }
}
