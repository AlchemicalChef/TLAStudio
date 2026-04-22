import SwiftUI

// MARK: - Model Configuration Editor

/// UI for editing TLC model configuration
struct ModelConfigEditor: View {
    @Binding var config: ModelConfig
    let symbols: [TLASymbol]
    @ObservedObject var configStore: ModelConfigStore
    var onActivateModel: ((ModelConfig) -> Void)?

    @State private var newConstantName = ""
    @State private var newConstantValue = ""
    @State private var newInvariant = ""
    @State private var newProperty = ""
    @State private var selectedConfigID: UUID?

    var body: some View {
        Form {
            Section("Saved Models") {
                VStack(alignment: .leading, spacing: 12) {
                    Picker("Current Model", selection: $selectedConfigID) {
                        Text("Unsaved Draft").tag(Optional<UUID>.none)
                        ForEach(configStore.configs) { namedConfig in
                            Text(namedConfig.name).tag(Optional(namedConfig.id))
                        }
                    }
                    .onChange(of: selectedConfigID) { _, newID in
                        guard let newID else {
                            detachCurrentConfigToDraft()
                            return
                        }
                        loadSavedModel(id: newID)
                    }

                    HStack(spacing: 8) {
                        if hasUnsavedChanges || selectedModel == nil {
                            Button {
                                saveCurrentModel()
                            } label: {
                                Label(saveButtonTitle, systemImage: "square.and.arrow.down")
                            }
                            .buttonStyle(.borderedProminent)
                            .help("Save the current model and make it the active model")
                        } else {
                            Button {
                                saveCurrentModel()
                            } label: {
                                Label(saveButtonTitle, systemImage: "square.and.arrow.down")
                            }
                            .buttonStyle(.bordered)
                            .help("Save the current model and make it the active model")
                        }

                        Button {
                            duplicateCurrentModel()
                        } label: {
                            Label("Duplicate", systemImage: "plus.square.on.square")
                        }
                        .buttonStyle(.bordered)
                        .help("Clone the current model as a new named model")

                        Button {
                            createUnsavedModel()
                        } label: {
                            Label("New Draft", systemImage: "plus")
                        }
                        .buttonStyle(.bordered)
                        .help("Start a new unsaved model draft")

                        if selectedConfigID != nil {
                            Button(role: .destructive) {
                                deleteSelectedModel()
                            } label: {
                                Label("Delete", systemImage: "trash")
                            }
                            .buttonStyle(.bordered)
                            .help("Delete the selected model")
                        }
                    }

                    HStack(spacing: 8) {
                        ModelStatusBadge(
                            title: selectedModel == nil ? "Draft" : "Saved",
                            color: selectedModel == nil ? .secondary : .accentColor
                        )

                        if hasUnsavedChanges {
                            ModelStatusBadge(title: "Unsaved Changes", color: .orange)
                        }

                        Text("\(configStore.configs.count) saved")
                            .font(.caption)
                            .foregroundColor(.secondary)
                    }

                    if let selectedModel {
                        VStack(alignment: .leading, spacing: 4) {
                            Text("Run TLC uses the selected model.")
                                .font(.caption)
                                .foregroundColor(.secondary)

                            if !selectedModel.comment.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
                                Text(selectedModel.comment)
                                    .font(.caption)
                                    .foregroundColor(.secondary)
                                    .lineLimit(2)
                            }
                        }
                    } else {
                        Text("Drafts run directly, but they are only persisted after you save them as a named model.")
                            .font(.caption)
                            .foregroundColor(.secondary)
                    }
                }
            }

            // Basic Settings
            Section("Model") {
                TextField("Name", text: $config.name)
                    .textFieldStyle(.roundedBorder)

                LabeledContent("Specification") {
                    Text(config.specFile.lastPathComponent)
                        .foregroundColor(.secondary)
                }

                VStack(alignment: .leading, spacing: 6) {
                    Text("Comment")
                        .font(.subheadline)
                        .foregroundColor(.secondary)

                    ZStack(alignment: .topLeading) {
                        RoundedRectangle(cornerRadius: 8)
                            .fill(Color(NSColor.textBackgroundColor))
                            .overlay(
                                RoundedRectangle(cornerRadius: 8)
                                    .stroke(Color.secondary.opacity(0.15))
                            )

                        if config.comment.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
                            Text("Notes about what this model checks, assumptions, or how to reproduce a trace.")
                                .font(.system(.body, design: .monospaced))
                                .foregroundColor(.secondary)
                                .padding(.horizontal, 9)
                                .padding(.vertical, 12)
                        }

                        TextEditor(text: $config.comment)
                            .font(.system(.body, design: .monospaced))
                            .scrollContentBackground(.hidden)
                            .padding(.horizontal, 4)
                            .padding(.vertical, 4)
                    }
                    .frame(minHeight: 84)
                }
            }

            Section("Quick Setup") {
                QuickModelConfig(config: $config, symbols: symbols)
            }

            // Constants
            Section("Constants") {
                ForEach(Array(config.constants.keys.sorted()), id: \.self) { key in
                    HStack {
                        Text(key)
                            .font(.system(.body, design: .monospaced))
                        Spacer()
                        if let value = config.constants[key] {
                            Text(value.tlcFormat)
                                .foregroundColor(.secondary)
                                .font(.system(.body, design: .monospaced))
                        }
                        Button(action: {
                            config.constants.removeValue(forKey: key)
                        }) {
                            Image(systemName: "minus.circle.fill")
                                .foregroundColor(.red)
                        }
                        .buttonStyle(.plain)
                    }
                }

                HStack {
                    TextField("Name", text: $newConstantName)
                        .textFieldStyle(.roundedBorder)
                        .frame(width: 100)
                    TextField("Value", text: $newConstantValue)
                        .textFieldStyle(.roundedBorder)
                    Button("Add") {
                        addConstant()
                    }
                    .disabled(newConstantName.isEmpty || newConstantValue.isEmpty)
                }
            }

            // What to Check
            Section("Invariants") {
                ForEach(config.invariants.indices, id: \.self) { index in
                    HStack {
                        Text(config.invariants[index])
                            .font(.system(.body, design: .monospaced))
                        Spacer()
                        Button(action: {
                            config.invariants.remove(at: index)
                        }) {
                            Image(systemName: "minus.circle.fill")
                                .foregroundColor(.red)
                        }
                        .buttonStyle(.plain)
                    }
                }

                HStack {
                    InvariantPicker(
                        text: $newInvariant,
                        symbols: symbols.filter { $0.kind == .operator || $0.kind == .definition }
                    )
                    Button("Add") {
                        if !newInvariant.isEmpty {
                            config.invariants.append(newInvariant)
                            newInvariant = ""
                        }
                    }
                    .disabled(newInvariant.isEmpty)
                }
            }

            Section("Temporal Properties") {
                ForEach(config.temporalProperties.indices, id: \.self) { index in
                    HStack {
                        Text(config.temporalProperties[index])
                            .font(.system(.body, design: .monospaced))
                        Spacer()
                        Button(action: {
                            config.temporalProperties.remove(at: index)
                        }) {
                            Image(systemName: "minus.circle.fill")
                                .foregroundColor(.red)
                        }
                        .buttonStyle(.plain)
                    }
                }

                HStack {
                    TextField("Property", text: $newProperty)
                        .textFieldStyle(.roundedBorder)
                        .font(.system(.body, design: .monospaced))
                    Button("Add") {
                        if !newProperty.isEmpty {
                            config.temporalProperties.append(newProperty)
                            newProperty = ""
                        }
                    }
                    .disabled(newProperty.isEmpty)
                }
            }

            // Constraints
            Section("Constraints") {
                TextField("State Constraint", text: Binding(
                    get: { config.stateConstraint ?? "" },
                    set: { config.stateConstraint = $0.isEmpty ? nil : $0 }
                ))
                .textFieldStyle(.roundedBorder)
                .font(.system(.body, design: .monospaced))

                TextField("Action Constraint", text: Binding(
                    get: { config.actionConstraint ?? "" },
                    set: { config.actionConstraint = $0.isEmpty ? nil : $0 }
                ))
                .textFieldStyle(.roundedBorder)
                .font(.system(.body, design: .monospaced))
            }

            // Execution Settings
            Section("Execution") {
                Stepper("Workers: \(config.workers)", value: $config.workers, in: 1...32)

                Toggle("Check Deadlock", isOn: $config.checkDeadlock)

                Toggle("Depth-First Search", isOn: $config.depthFirst)

                if config.depthFirst {
                    Stepper("Max Depth: \(config.maxDepth ?? 100)", value: Binding(
                        get: { config.maxDepth ?? 100 },
                        set: { config.maxDepth = $0 }
                    ), in: 1...1000)
                }

                Stepper("Checkpoint: \(Int(config.checkpointInterval / 60)) min",
                        value: Binding(
                            get: { Int(config.checkpointInterval / 60) },
                            set: { config.checkpointInterval = TimeInterval($0 * 60) }
                        ), in: 1...60)
            }

            // Large State Space Settings
            Section("Large State Space") {
                Toggle("Disk-Based Fingerprint Storage", isOn: $config.useDiskStorage)
                    .help("Store fingerprints on disk instead of memory. Slower (~3-5x) but handles unlimited state spaces.")

                if config.useDiskStorage {
                    Text("Fingerprints will spill to disk when memory is 90% full")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                Toggle("Allow JVM Fallback", isOn: $config.useJVMFallback)
                    .help("Automatically retry with JVM-based TLC if native image runs out of memory. JVM has no 32GB limit but 2-3s startup.")

                if config.useJVMFallback {
                    Text("Will offer to retry with full JVM if native TLC hits memory limit")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
            }
        }
        .formStyle(.grouped)
        .onAppear {
            syncSelectionFromCurrentConfig()
        }
    }

    private var selectedModel: NamedModelConfig? {
        guard let selectedConfigID else { return nil }
        return configStore.config(id: selectedConfigID)
    }

    private var hasUnsavedChanges: Bool {
        guard let selectedModel else { return true }
        return selectedModel.config != config
    }

    private var saveButtonTitle: String {
        if selectedModel == nil {
            return "Save Model"
        }
        return hasUnsavedChanges ? "Save Changes" : "Save"
    }

    private func addConstant() {
        guard !newConstantName.isEmpty, !newConstantValue.isEmpty else { return }

        config.constants[newConstantName] = ModelConfig.parseConstantValue(newConstantValue)
        newConstantName = ""
        newConstantValue = ""
    }

    private func syncSelectionFromCurrentConfig() {
        if let matchingModel = configStore.configs.first(where: { $0.id == config.id }) {
            selectedConfigID = matchingModel.id
            config = matchingModel.config
            return
        }
        selectedConfigID = nil
    }

    private func loadSavedModel(id: UUID) {
        guard let namedConfig = configStore.config(id: id) else { return }
        configStore.selectConfig(id: id)
        config = namedConfig.config
        onActivateModel?(namedConfig.config)
    }

    private func saveCurrentModel() {
        let saved = configStore.save(config: config, selecting: true)
        config = saved.config
        selectedConfigID = saved.id
        onActivateModel?(saved.config)
    }

    private func duplicateCurrentModel() {
        let duplicated = configStore.duplicate(config: config, selecting: true)
        config = duplicated.config
        selectedConfigID = duplicated.id
        onActivateModel?(duplicated.config)
    }

    private func createUnsavedModel() {
        detachCurrentConfigToDraft(resetName: true)
        config.comment = ""
        onActivateModel?(config)
    }

    private func detachCurrentConfigToDraft(resetName: Bool = false) {
        config.id = UUID()
        if resetName {
            config.name = configStore.configNames.contains("Default") ? "Model \(configStore.configs.count + 1)" : "Default"
        }
        configStore.selectConfig(id: nil)
        selectedConfigID = nil
    }

    private func deleteSelectedModel() {
        guard let selectedConfigID else { return }
        configStore.delete(id: selectedConfigID)

        if let fallback = configStore.selectedConfig {
            config = fallback.config
            self.selectedConfigID = fallback.id
            onActivateModel?(fallback.config)
        } else {
            createUnsavedModel()
        }
    }
}

// MARK: - Invariant Picker

/// Combo box for picking invariants from symbols
struct InvariantPicker: View {
    @Binding var text: String
    let symbols: [TLASymbol]

    @State private var showingSuggestions = false

    var filteredSymbols: [TLASymbol] {
        if text.isEmpty {
            return symbols
        }
        return symbols.filter { $0.name.localizedCaseInsensitiveContains(text) }
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            TextField("Invariant", text: $text)
                .textFieldStyle(.roundedBorder)
                .font(.system(.body, design: .monospaced))
                .onChange(of: text) { _, _ in
                    showingSuggestions = !text.isEmpty || !symbols.isEmpty
                }
                .onTapGesture {
                    showingSuggestions = true
                }

            if showingSuggestions && !filteredSymbols.isEmpty {
                ScrollView {
                    VStack(alignment: .leading, spacing: 2) {
                        ForEach(filteredSymbols.prefix(5), id: \.name) { symbol in
                            HStack {
                                Text(symbol.name)
                                    .font(.system(.body, design: .monospaced))
                                Spacer()
                                Text(symbol.kind.displayName)
                                    .foregroundColor(.secondary)
                                    .font(.caption)
                            }
                            .padding(.horizontal, 8)
                            .padding(.vertical, 4)
                            .background(Color.secondary.opacity(0.1))
                            .cornerRadius(4)
                            .onTapGesture {
                                text = symbol.name
                                showingSuggestions = false
                            }
                        }
                    }
                }
                .frame(maxHeight: 150)
                .background(Color(NSColor.controlBackgroundColor))
                .cornerRadius(4)
                .shadow(radius: 2)
            }
        }
    }
}

// MARK: - Quick Config

/// Quick configuration panel for common model checking scenarios
struct QuickModelConfig: View {
    @Binding var config: ModelConfig
    let symbols: [TLASymbol]

    var typeOKSymbol: TLASymbol? {
        symbols.first { $0.name == "TypeOK" || $0.name == "TypeInvariant" }
    }

    var initSymbol: TLASymbol? {
        symbols.first { $0.name == "Init" }
    }

    var nextSymbol: TLASymbol? {
        symbols.first { $0.name == "Next" }
    }

    var specSymbol: TLASymbol? {
        symbols.first { $0.name == "Spec" }
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            if let typeOK = typeOKSymbol {
                Button("Add TypeOK as Invariant") {
                    if !config.invariants.contains(typeOK.name) {
                        config.invariants.append(typeOK.name)
                    }
                }
                .disabled(config.invariants.contains(typeOK.name))
            }

            // Find potential invariants
            let potentialInvariants = symbols.filter { symbol in
                (symbol.name.contains("Invariant") ||
                 symbol.name.contains("Safe") ||
                 symbol.name.hasPrefix("Type")) &&
                !config.invariants.contains(symbol.name)
            }

            if !potentialInvariants.isEmpty {
                Divider()
                Text("Detected Invariants:")
                    .font(.subheadline)
                    .foregroundColor(.secondary)

                ForEach(potentialInvariants.prefix(3), id: \.name) { symbol in
                    Button("Add \(symbol.name)") {
                        config.invariants.append(symbol.name)
                    }
                }
            }

            Divider()

            // Worker count suggestions
            HStack {
                Text("Workers:")
                Spacer()
                Button("1") { config.workers = 1 }
                Button("4") { config.workers = 4 }
                Button("8") { config.workers = 8 }
                Button("Auto") { config.workers = ProcessInfo.processInfo.activeProcessorCount }
            }
        }
    }
}

// MARK: - Model Config Editor Sheet

/// Sheet wrapper for ModelConfigEditor with save/cancel buttons
struct ModelConfigEditorSheet: View {
    @Binding var config: ModelConfig
    let symbols: [TLASymbol]
    @ObservedObject var configStore: ModelConfigStore
    var onSave: ((ModelConfig) -> Void)?
    @Binding var isPresented: Bool

    var body: some View {
        VStack(spacing: 0) {
            // Header
            HStack {
                VStack(alignment: .leading, spacing: 2) {
                    Text("Model Configuration")
                        .font(.headline)
                    Text(config.name)
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
                Spacer()
                Button("Done") {
                    let saved = configStore.save(config: config, selecting: true)
                    config = saved.config
                    onSave?(saved.config)
                    isPresented = false
                }
                .keyboardShortcut(.return, modifiers: [])
            }
            .padding()
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Config editor
            ModelConfigEditor(
                config: $config,
                symbols: symbols,
                configStore: configStore,
                onActivateModel: { config in
                    onSave?(config)
                }
            )
                .frame(minWidth: 500, minHeight: 400)
        }
        .frame(width: 600, height: 550)
    }
}

// MARK: - TLASymbol Extension

extension TLASymbolKind {
    var displayName: String {
        switch self {
        case .module:
            return "Module"
        case .variable:
            return "Variable"
        case .constant:
            return "Constant"
        case .operator:
            return "Operator"
        case .definition:
            return "Definition"
        case .theorem:
            return "Theorem"
        case .assumption:
            return "Assumption"
        case .instance:
            return "Instance"
        }
    }
}

private struct ModelStatusBadge: View {
    let title: String
    let color: Color

    var body: some View {
        Text(title)
            .font(.caption2.weight(.semibold))
            .padding(.horizontal, 8)
            .padding(.vertical, 3)
            .foregroundColor(color)
            .background(color.opacity(0.12))
            .clipShape(Capsule())
    }
}
