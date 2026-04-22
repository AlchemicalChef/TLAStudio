import XCTest
@testable import TLAStudioApp

@MainActor
final class ModelConfigStoreTests: TempDirectoryTestCase {

    private struct StoredConfigsPayload: Codable {
        var version: Int
        var selectedConfigID: UUID?
        var configs: [NamedModelConfig]
    }

    func testSaveAndReloadPersistsSelectedModelAndComment() throws {
        let specURL = tempDirectory.appendingPathComponent("Spec.tla")
        FileManager.default.createFile(atPath: specURL.path, contents: Data())

        let store = ModelConfigStore()
        store.load(for: specURL)

        var alpha = TestFactories.makeModelConfig(name: "Alpha", specFile: specURL)
        alpha.comment = "Alpha comment"
        _ = store.save(config: alpha)

        var beta = TestFactories.makeModelConfig(name: "Beta", specFile: specURL)
        beta.comment = "Beta comment"
        let savedBeta = store.save(config: beta)

        XCTAssertEqual(store.selectedConfig?.id, savedBeta.id)

        let reloadedStore = ModelConfigStore()
        reloadedStore.load(for: specURL)

        XCTAssertEqual(reloadedStore.configs.count, 2)
        XCTAssertEqual(reloadedStore.selectedConfig?.name, "Beta")
        XCTAssertEqual(reloadedStore.selectedConfig?.comment, "Beta comment")
        XCTAssertEqual(reloadedStore.selectedConfig?.config.comment, "Beta comment")
    }

    func testDuplicateCreatesUniqueNameAndDeleteFallsBackToFirstModel() throws {
        let specURL = tempDirectory.appendingPathComponent("Spec.tla")
        FileManager.default.createFile(atPath: specURL.path, contents: Data())

        let store = ModelConfigStore()
        store.load(for: specURL)

        let alpha = store.save(config: TestFactories.makeModelConfig(name: "Alpha", specFile: specURL))
        let duplicate = store.duplicate(config: alpha.config)

        XCTAssertEqual(duplicate.name, "Alpha 2")
        XCTAssertEqual(store.selectedConfig?.id, duplicate.id)

        store.delete(id: duplicate.id)

        XCTAssertEqual(store.selectedConfig?.id, alpha.id)
        XCTAssertEqual(store.configs.count, 1)
    }

    func testLoadsLegacyArrayFormat() throws {
        let specURL = tempDirectory.appendingPathComponent("Spec.tla")
        FileManager.default.createFile(atPath: specURL.path, contents: Data())

        let configsDirectory = tempDirectory.appendingPathComponent(".tlastudio")
        try FileManager.default.createDirectory(at: configsDirectory, withIntermediateDirectories: true)
        let configsFile = configsDirectory.appendingPathComponent("configs.json")

        var legacyConfig = TestFactories.makeModelConfig(name: "Legacy", specFile: specURL)
        legacyConfig.comment = "Legacy comment"
        let legacyPayload = [
            NamedModelConfig(name: "Legacy", comment: "Legacy comment", config: legacyConfig)
        ]

        let data = try JSONEncoder().encode(legacyPayload)
        try data.write(to: configsFile)

        let store = ModelConfigStore()
        store.load(for: specURL)

        XCTAssertEqual(store.configs.count, 1)
        XCTAssertEqual(store.selectedConfig?.name, "Legacy")
        XCTAssertEqual(store.selectedConfig?.comment, "Legacy comment")
    }

    func testSavingNewConfigWithCollidingNameCreatesDistinctModel() throws {
        let specURL = tempDirectory.appendingPathComponent("Spec.tla")
        FileManager.default.createFile(atPath: specURL.path, contents: Data())

        let store = ModelConfigStore()
        store.load(for: specURL)

        let original = store.save(config: TestFactories.makeModelConfig(name: "Alpha", specFile: specURL))

        var draft = TestFactories.makeModelConfig(name: "Alpha", specFile: specURL)
        draft.id = UUID()
        draft.comment = "draft"

        let savedDraft = store.save(config: draft)

        XCTAssertEqual(store.configs.count, 2)
        XCTAssertEqual(original.name, "Alpha")
        XCTAssertEqual(savedDraft.name, "Alpha 2")
        XCTAssertEqual(store.config(id: original.id)?.comment, "")
        XCTAssertEqual(store.config(id: savedDraft.id)?.comment, "draft")
    }

    func testLoadFallsBackToFirstConfigWhenSelectedIDIsMissing() throws {
        let specURL = tempDirectory.appendingPathComponent("Spec.tla")
        FileManager.default.createFile(atPath: specURL.path, contents: Data())

        let configsDirectory = tempDirectory.appendingPathComponent(".tlastudio")
        try FileManager.default.createDirectory(at: configsDirectory, withIntermediateDirectories: true)
        let configsFile = configsDirectory.appendingPathComponent("configs.json")

        let alpha = NamedModelConfig(
            name: "Alpha",
            config: TestFactories.makeModelConfig(name: "Alpha", specFile: specURL)
        )
        let beta = NamedModelConfig(
            name: "Beta",
            config: TestFactories.makeModelConfig(name: "Beta", specFile: specURL)
        )
        let payload = StoredConfigsPayload(
            version: 1,
            selectedConfigID: UUID(),
            configs: [alpha, beta]
        )

        let data = try JSONEncoder().encode(payload)
        try data.write(to: configsFile)

        let store = ModelConfigStore()
        store.load(for: specURL)

        XCTAssertEqual(store.selectedConfig?.id, alpha.id)
        XCTAssertEqual(store.selectedConfig?.name, "Alpha")
    }
}
