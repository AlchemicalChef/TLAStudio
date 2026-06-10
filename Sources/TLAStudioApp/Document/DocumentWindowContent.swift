import SwiftUI

// MARK: - Document Window Content

/// Main SwiftUI content for the document window
struct DocumentWindowContent: View {
    @ObservedObject var document: TLADocument
    @State private var showNavigator = true
    @State private var showInspector = false
    /// Seed config for the edit sheet. Presence of a value drives the sheet; using
    /// `.sheet(item:)` instead of `(isPresented: + Binding($optional))` avoids a
    /// SwiftUI race where the sheet content was evaluated before the @State that
    /// feeds it settled, producing a blank grey box on the first open.
    @State private var editingConfig: ModelConfig?

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
        .onReceiveDocumentNotification(.toggleNavigatorSidebar, for: document) {
            showNavigator.toggle()
        }
        .onReceiveDocumentNotification(.toggleSymbolOutline, for: document) {
            showNavigator = true
        }
        .onReceiveDocumentNotification(.toggleInspectorSidebar, for: document) {
            showInspector.toggle()
        }
        .onReceiveDocumentNotification(.editModelConfig, for: document) {
            editingConfig = document.resolvedModelConfig()
        }
        .sheet(item: $editingConfig) { seed in
            ModelConfigEditorSheetContainer(
                initial: seed,
                symbols: document.symbols,
                configStore: document.modelConfigStore,
                onSave: { savedConfig in
                    document.activeModelConfig = savedConfig
                },
                onDismiss: { editingConfig = nil }
            )
        }
    }
}

// MARK: - Model Config Editor Sheet Container

/// Owns the mutable ModelConfig for the editor sheet. Splitting this out lets us
/// seed the @State from the `.sheet(item:)` value exactly once per presentation
/// without fighting SwiftUI's view-identity rules.
private struct ModelConfigEditorSheetContainer: View {
    let symbols: [TLASymbol]
    @ObservedObject var configStore: ModelConfigStore
    let onSave: (ModelConfig) -> Void
    let onDismiss: () -> Void

    @State private var config: ModelConfig

    init(
        initial: ModelConfig,
        symbols: [TLASymbol],
        configStore: ModelConfigStore,
        onSave: @escaping (ModelConfig) -> Void,
        onDismiss: @escaping () -> Void
    ) {
        self.symbols = symbols
        self.configStore = configStore
        self.onSave = onSave
        self.onDismiss = onDismiss
        _config = State(initialValue: initial)
    }

    var body: some View {
        ModelConfigEditorSheet(
            config: $config,
            symbols: symbols,
            configStore: configStore,
            onSave: onSave,
            isPresented: Binding(
                get: { true },
                set: { newValue in
                    if !newValue { onDismiss() }
                }
            )
        )
    }
}
