import XCTest
@testable import TLAStudioApp

@MainActor
final class DocumentModelConfigTests: TempDirectoryTestCase {

    func testResolvedModelConfigDoesNotBackfillEmptySavedSections() throws {
        let specURL = tempDirectory.appendingPathComponent("Spec.tla")
        let cfgURL = specURL.deletingPathExtension().appendingPathExtension("cfg")
        FileManager.default.createFile(atPath: specURL.path, contents: Data())

        try """
        SPECIFICATION ExistingSpec
        CONSTANT N = 3
        INVARIANT TypeOK
        PROPERTY Live
        CONSTRAINT x < 10
        ACTION_CONSTRAINT x' > x
        """.write(to: cfgURL, atomically: true, encoding: .utf8)

        let document = TLADocument()
        let saved = TestFactories.makeModelConfig(name: "Saved", specFile: specURL)

        let resolved = document.resolvedModelConfig(for: specURL, override: saved)

        XCTAssertNil(resolved.specification)
        XCTAssertTrue(resolved.constants.isEmpty)
        XCTAssertTrue(resolved.invariants.isEmpty)
        XCTAssertTrue(resolved.temporalProperties.isEmpty)
        XCTAssertNil(resolved.stateConstraint)
        XCTAssertNil(resolved.actionConstraint)
    }

    func testResolvedModelConfigUsesTLCDefaultsFromUserSettingsForNewModels() throws {
        let specURL = tempDirectory.appendingPathComponent("Spec.tla")
        FileManager.default.createFile(atPath: specURL.path, contents: Data())

        let settings = UserSettings.shared
        let originalWorkers = settings.tlcWorkers
        let originalCheckpointEnabled = settings.tlcCheckpointEnabled
        let originalCheckpointInterval = settings.tlcCheckpointInterval
        defer {
            settings.tlcWorkers = originalWorkers
            settings.tlcCheckpointEnabled = originalCheckpointEnabled
            settings.tlcCheckpointInterval = originalCheckpointInterval
        }

        settings.tlcWorkers = 7
        settings.tlcCheckpointEnabled = false
        settings.tlcCheckpointInterval = 42

        let document = TLADocument()
        let resolved = document.resolvedModelConfig(for: specURL)

        XCTAssertEqual(resolved.workers, 7)
        XCTAssertFalse(resolved.checkpointEnabled)
        XCTAssertEqual(resolved.checkpointInterval, 42 * 60)
    }
}
