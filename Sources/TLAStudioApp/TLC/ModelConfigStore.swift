import Foundation
import os

// MARK: - Named Configuration

/// A named model configuration for persistence.
struct NamedModelConfig: Codable, Identifiable {
    var id: UUID
    var name: String
    var comment: String
    var config: ModelConfig

    init(id: UUID? = nil, name: String, comment: String = "", config: ModelConfig) {
        let resolvedID = id ?? config.id
        var normalizedConfig = config
        normalizedConfig.id = resolvedID
        normalizedConfig.name = Self.normalizedName(name)
        normalizedConfig.comment = comment

        self.id = resolvedID
        self.name = normalizedConfig.name
        self.comment = comment
        self.config = normalizedConfig
    }

    mutating func apply(name: String? = nil, comment: String? = nil, config: ModelConfig? = nil) {
        if let name {
            self.name = Self.normalizedName(name)
        }
        if let comment {
            self.comment = comment
        }
        if let config {
            self.config = config
        }
        self.config.id = id
        self.config.name = self.name
        self.config.comment = self.comment
    }

    private static func normalizedName(_ name: String) -> String {
        let trimmed = name.trimmingCharacters(in: .whitespacesAndNewlines)
        return trimmed.isEmpty ? "Default" : trimmed
    }
}

private struct StoredModelConfigs: Codable {
    var version: Int
    var selectedConfigID: UUID?
    var configs: [NamedModelConfig]

    init(version: Int = 1, selectedConfigID: UUID? = nil, configs: [NamedModelConfig]) {
        self.version = version
        self.selectedConfigID = selectedConfigID
        self.configs = configs
    }
}

// MARK: - Model Configuration Store

/// Manages saving and loading named model configurations as sidecar JSON files.
/// Configs are stored at `<spec-directory>/.tlastudio/configs.json`.
@MainActor
final class ModelConfigStore: ObservableObject {

    private let logger = Log.logger(category: "ModelConfigStore")

    /// All saved named configurations.
    @Published private(set) var configs: [NamedModelConfig] = []

    /// The current model selection for this spec.
    @Published private(set) var selectedConfigID: UUID?

    /// The spec file URL this store is associated with.
    private var specFileURL: URL?

    init() {}

    func load(for specFileURL: URL) {
        self.specFileURL = specFileURL
        let loaded = loadFromDisk()
        configs = loaded.configs
        selectedConfigID = resolvedSelectedConfigID(loaded.selectedConfigID, in: loaded.configs)
    }

    // MARK: - Public API

    var selectedConfig: NamedModelConfig? {
        guard let selectedConfigID else { return nil }
        return configs.first { $0.id == selectedConfigID }
    }

    var selectedConfigName: String? {
        selectedConfig?.name
    }

    var configNames: [String] {
        configs.map(\.name)
    }

    func config(id: UUID) -> NamedModelConfig? {
        configs.first { $0.id == id }
    }

    func config(named name: String) -> ModelConfig? {
        configs.first { $0.name == name }?.config
    }

    @discardableResult
    func save(config: ModelConfig, selecting: Bool = true, comment: String? = nil) -> NamedModelConfig {
        let normalizedName = normalizedUniqueName(config.name, preferredID: config.id)

        if let index = indexForExistingConfig(matching: config) {
            var existing = configs[index]
            existing.apply(name: normalizedName, comment: comment ?? config.comment, config: config)
            configs[index] = existing
            if selecting {
                selectedConfigID = existing.id
            }
            saveToDisk()
            return existing
        }

        let named = NamedModelConfig(name: normalizedName, comment: comment ?? config.comment, config: config)
        configs.append(named)
        if selecting {
            selectedConfigID = named.id
        }
        saveToDisk()
        return named
    }

    @discardableResult
    func duplicate(config: ModelConfig, comment: String? = nil, selecting: Bool = true) -> NamedModelConfig {
        var duplicatedConfig = config
        duplicatedConfig.id = UUID()
        duplicatedConfig.name = uniqueName(basedOn: duplicatedConfig.name)
        duplicatedConfig.comment = comment ?? config.comment

        let duplicate = NamedModelConfig(
            name: duplicatedConfig.name,
            comment: duplicatedConfig.comment,
            config: duplicatedConfig
        )
        configs.append(duplicate)
        if selecting {
            selectedConfigID = duplicate.id
        }
        saveToDisk()
        return duplicate
    }

    func rename(id: UUID, to name: String) {
        guard let index = configs.firstIndex(where: { $0.id == id }) else { return }
        let normalizedName = normalizedUniqueName(name, preferredID: id)
        configs[index].apply(name: normalizedName)
        saveToDisk()
    }

    func updateComment(id: UUID, comment: String) {
        guard let index = configs.firstIndex(where: { $0.id == id }) else { return }
        configs[index].apply(comment: comment)
        saveToDisk()
    }

    func selectConfig(id: UUID?) {
        if let id, configs.contains(where: { $0.id == id }) {
            selectedConfigID = id
        } else {
            selectedConfigID = nil
        }
        saveToDisk()
    }

    func delete(id: UUID) {
        let removedSelectedConfig = selectedConfigID == id
        configs.removeAll { $0.id == id }

        if removedSelectedConfig {
            selectedConfigID = configs.first?.id
        } else if let selectedConfigID, !configs.contains(where: { $0.id == selectedConfigID }) {
            self.selectedConfigID = configs.first?.id
        }

        saveToDisk()
    }

    // MARK: - Persistence

    private var configsDirectoryURL: URL? {
        guard let specURL = specFileURL else { return nil }
        return specURL.deletingLastPathComponent().appendingPathComponent(".tlastudio")
    }

    private var configsFileURL: URL? {
        configsDirectoryURL?.appendingPathComponent("configs.json")
    }

    private func loadFromDisk() -> StoredModelConfigs {
        guard let fileURL = configsFileURL else {
            return StoredModelConfigs(configs: [])
        }

        guard FileManager.default.fileExists(atPath: fileURL.path) else {
            return StoredModelConfigs(configs: [])
        }

        do {
            let data = try Data(contentsOf: fileURL)
            let decoder = JSONDecoder()

            if let stored = try? decoder.decode(StoredModelConfigs.self, from: data) {
                let normalizedConfigs = normalize(configs: stored.configs)
                logger.info("Loaded \(normalizedConfigs.count) saved configurations")
                return StoredModelConfigs(
                    selectedConfigID: stored.selectedConfigID,
                    configs: normalizedConfigs
                )
            }

            let legacyConfigs = try decoder.decode([NamedModelConfig].self, from: data)
            let normalizedConfigs = normalize(configs: legacyConfigs)
            logger.info("Loaded \(normalizedConfigs.count) legacy configurations")
            return StoredModelConfigs(
                selectedConfigID: normalizedConfigs.first?.id,
                configs: normalizedConfigs
            )
        } catch {
            logger.error("Failed to load configs: \(error.localizedDescription)")
            return StoredModelConfigs(configs: [])
        }
    }

    private func saveToDisk() {
        guard let dirURL = configsDirectoryURL,
              let fileURL = configsFileURL else {
            logger.warning("No spec file URL set, cannot save configs")
            return
        }

        do {
            try FileManager.default.createDirectory(at: dirURL, withIntermediateDirectories: true)

            let encoder = JSONEncoder()
            encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
            let normalizedConfigs = normalize(configs: configs)
            let payload = StoredModelConfigs(
                selectedConfigID: resolvedSelectedConfigID(selectedConfigID, in: normalizedConfigs),
                configs: normalizedConfigs
            )
            let data = try encoder.encode(payload)
            try data.write(to: fileURL, options: .atomic)
            logger.info("Saved \(payload.configs.count) configurations to \(fileURL.path)")
        } catch {
            logger.error("Failed to save configs: \(error.localizedDescription)")
        }
    }

    // MARK: - Helpers

    private func indexForExistingConfig(matching config: ModelConfig) -> Int? {
        configs.firstIndex(where: { $0.id == config.id })
    }

    private func uniqueName(basedOn name: String) -> String {
        let baseName = normalizedName(name)
        var candidate = baseName
        var counter = 2

        while configs.contains(where: { $0.name == candidate }) {
            candidate = "\(baseName) \(counter)"
            counter += 1
        }

        return candidate
    }

    private func normalizedUniqueName(_ name: String, preferredID: UUID?) -> String {
        let baseName = normalizedName(name)
        var candidate = baseName
        var counter = 2

        while configs.contains(where: { $0.name == candidate && $0.id != preferredID }) {
            candidate = "\(baseName) \(counter)"
            counter += 1
        }

        return candidate
    }

    private func normalizedName(_ name: String) -> String {
        let trimmed = name.trimmingCharacters(in: .whitespacesAndNewlines)
        return trimmed.isEmpty ? "Default" : trimmed
    }

    private func resolvedSelectedConfigID(_ preferredID: UUID?, in configs: [NamedModelConfig]) -> UUID? {
        guard let preferredID else {
            return configs.first?.id
        }

        if configs.contains(where: { $0.id == preferredID }) {
            return preferredID
        }

        return configs.first?.id
    }

    private func normalize(configs: [NamedModelConfig]) -> [NamedModelConfig] {
        configs.map { stored in
            var normalized = stored
            normalized.apply()
            return normalized
        }
    }
}
