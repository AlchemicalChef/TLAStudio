import SwiftUI

// MARK: - Model Configuration Editor

/// UI for editing TLC model configuration
struct ModelConfigEditor: View {
    @Binding var config: ModelConfig
    let symbols: [TLASymbol]

    @State private var newConstantName = ""
    @State private var newConstantValue = ""
    @State private var newInvariant = ""
    @State private var newProperty = ""

    var body: some View {
        Form {
            // Basic Settings
            Section("Model") {
                TextField("Name", text: $config.name)
                    .textFieldStyle(.roundedBorder)

                LabeledContent("Specification") {
                    Text(config.specFile.lastPathComponent)
                        .foregroundColor(.secondary)
                }
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
    }

    private func addConstant() {
        guard !newConstantName.isEmpty, !newConstantValue.isEmpty else { return }

        // Parse the value
        let value: ConstantValue
        if let intVal = Int(newConstantValue) {
            value = .int(intVal)
        } else if newConstantValue == "TRUE" {
            value = .bool(true)
        } else if newConstantValue == "FALSE" {
            value = .bool(false)
        } else if newConstantValue.hasPrefix("{") && newConstantValue.hasSuffix("}") {
            // Model value set
            value = .modelValue(newConstantValue)
        } else {
            value = .string(newConstantValue)
        }

        config.constants[newConstantName] = value
        newConstantName = ""
        newConstantValue = ""
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
            Text("Quick Setup")
                .font(.headline)

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
        .padding()
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(8)
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
