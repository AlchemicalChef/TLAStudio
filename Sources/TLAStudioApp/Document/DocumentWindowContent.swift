import SwiftUI

// MARK: - Document Window Content

/// Main SwiftUI content for the document window
struct DocumentWindowContent: View {
    @ObservedObject var document: TLADocument
    @State private var showNavigator = true
    @State private var showInspector = false
    @State private var showConfigEditor = false
    @State private var modelConfig: ModelConfig?

    var body: some View {
        NavigationSplitView(columnVisibility: .constant(
            showNavigator ? .all : .detailOnly
        )) {
            // Navigator sidebar
            NavigatorSidebar(document: document)
                .frame(minWidth: 200, idealWidth: 250, maxWidth: 300)
        } detail: {
            // Main editor + optional inspector
            HSplitView {
                // Editor
                EditorArea(document: document)

                // Inspector (conditional)
                if showInspector {
                    InspectorSidebar(document: document)
                        .frame(minWidth: 200, idealWidth: 280, maxWidth: 350)
                }
            }
        }
        .toolbar {
            ToolbarItem(placement: .navigation) {
                Button(action: { showNavigator.toggle() }) {
                    Image(systemName: "sidebar.leading")
                }
                .help("Toggle Navigator")
            }

            ToolbarItem(placement: .primaryAction) {
                Button(action: { showInspector.toggle() }) {
                    Image(systemName: "sidebar.trailing")
                }
                .help("Toggle Inspector")
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .toggleNavigatorSidebar)) { _ in
            showNavigator.toggle()
        }
        .onReceive(NotificationCenter.default.publisher(for: .toggleInspectorSidebar)) { _ in
            showInspector.toggle()
        }
        .onReceive(NotificationCenter.default.publisher(for: .editModelConfig)) { _ in
            // Initialize config from document if not already set
            if modelConfig == nil {
                let specURL = document.fileURL ?? URL(fileURLWithPath: "/tmp/untitled.tla")

                // Try to load existing .cfg file
                let configURL = specURL.deletingPathExtension().appendingPathExtension("cfg")
                let existingConfig = ModelConfig.parse(from: configURL)

                // Merge existing config with detected invariants
                let constants = existingConfig?.constants ?? [:]
                var invariants = existingConfig?.invariants ?? []

                // Add detected invariants that aren't already in the config
                let detectedInvariants = detectInvariants(in: document.symbols)
                for inv in detectedInvariants {
                    if !invariants.contains(inv) {
                        invariants.append(inv)
                    }
                }

                modelConfig = ModelConfig(
                    name: "Default",
                    specFile: specURL,
                    initPredicate: existingConfig?.initPredicate ?? "Init",
                    nextAction: existingConfig?.nextAction ?? "Next",
                    constants: constants,
                    invariants: invariants,
                    temporalProperties: existingConfig?.temporalProperties ?? [],
                    stateConstraint: existingConfig?.stateConstraint,
                    actionConstraint: existingConfig?.actionConstraint,
                    workers: ProcessInfo.processInfo.activeProcessorCount
                )
            }
            showConfigEditor = true
        }
        .sheet(isPresented: $showConfigEditor) {
            if let binding = Binding($modelConfig) {
                ModelConfigEditorSheet(
                    config: binding,
                    symbols: document.symbols,
                    isPresented: $showConfigEditor
                )
            }
        }
    }

    private func detectInvariants(in symbols: [TLASymbol]) -> [String] {
        symbols.compactMap { symbol in
            if symbol.name.contains("Invariant") ||
               symbol.name.contains("Safety") ||
               symbol.name == "TypeOK" ||
               symbol.name.hasPrefix("Type") {
                return symbol.name
            }
            return nil
        }
    }
}
