import AppKit
import SwiftUI
import SourceEditor

// MARK: - TLAWindowController

/// Main window controller for TLA+ documents.
/// Manages toolbar, sidebar toggles, and coordinates document with views.
final class TLAWindowController: NSWindowController, NSWindowDelegate {

    // MARK: - Properties

    private(set) var tlaDocument: TLADocument?
    private var hostingController: NSHostingController<AnyView>?

    // MARK: - Initialization

    convenience init(document: TLADocument) {
        // Create SwiftUI content view
        let contentView = DocumentWindowContent(document: document)
        let hostingController = NSHostingController(rootView: AnyView(contentView))

        // Create window
        let window = NSWindow(contentViewController: hostingController)
        window.setContentSize(NSSize(width: 1200, height: 800))
        window.minSize = NSSize(width: 800, height: 600)
        window.styleMask = [
            .titled,
            .closable,
            .miniaturizable,
            .resizable,
            .fullSizeContentView
        ]
        window.titlebarAppearsTransparent = false
        window.toolbarStyle = .unified

        self.init(window: window)
        self.tlaDocument = document
        self.hostingController = hostingController

        // Configure window
        setupToolbar()
        setupBindings()

        // Set window delegate for activation handling
        window.delegate = self

        // CRITICAL: Activate the app and make window key
        NSApp.activate(ignoringOtherApps: true)
        window.makeKeyAndOrderFront(nil)

        // Ensure window accepts mouse events and can become key
        window.acceptsMouseMovedEvents = true
        window.isReleasedWhenClosed = false
    }

    // MARK: - NSWindowDelegate

    func windowDidBecomeMain(_ notification: Notification) {
        // Force this window to also become key when it becomes main
        window?.makeKey()
    }

    func windowShouldClose(_ sender: NSWindow) -> Bool {
        true
    }

    // MARK: - Setup

    private func setupToolbar() {
        let toolbar = NSToolbar(identifier: "TLADocumentToolbar")
        toolbar.delegate = self
        toolbar.displayMode = .iconOnly
        toolbar.allowsUserCustomization = true
        toolbar.autosavesConfiguration = true
        window?.toolbar = toolbar
    }

    private func setupBindings() {
        guard let window = window, let document = tlaDocument else { return }

        // Window title shows document name
        window.bind(.title, to: document, withKeyPath: "displayName")

        // Dirty indicator (dot in title)
        window.bind(.documentEdited, to: document, withKeyPath: "hasUnautosavedChanges")

        // Represented file (enables proxy icon)
        if let fileURL = document.fileURL {
            window.representedURL = fileURL
        }
    }

    // MARK: - Window Lifecycle

    override func windowDidLoad() {
        super.windowDidLoad()

        // Restore window frame
        window?.setFrameAutosaveName("TLADocumentWindow")
    }

    // MARK: - Actions

    @objc func runModelCheck(_ sender: Any?) {
        guard let doc = tlaDocument else {
            return
        }
        doc.runModelCheck()
    }

    @objc func stopModelCheck(_ sender: Any?) {
        guard let doc = tlaDocument else { return }
        doc.stopModelCheck()
    }

    @objc func checkProof(_ sender: Any?) {
        guard let doc = tlaDocument else { return }
        NotificationCenter.default.post(name: .checkAllProofs, object: doc, userInfo: nil)
    }

    @objc func translatePlusCal(_ sender: Any?) {
        guard let doc = tlaDocument else { return }
        NotificationCenter.default.post(name: .translatePlusCal, object: doc, userInfo: nil)
    }

    @objc func toggleNavigator(_ sender: Any?) {
        NotificationCenter.default.post(name: .toggleNavigatorSidebar, object: nil)
    }

    @objc func toggleInspector(_ sender: Any?) {
        NotificationCenter.default.post(name: .toggleInspectorSidebar, object: nil)
    }
}

// MARK: - NSToolbarDelegate

extension TLAWindowController: NSToolbarDelegate {

    func toolbarDefaultItemIdentifiers(_ toolbar: NSToolbar) -> [NSToolbarItem.Identifier] {
        [
            .toggleSidebar,
            .sidebarTrackingSeparator,
            .flexibleSpace,
            .runModelCheck,
            .stopModelCheck,
            .space,
            .checkProof,
            .flexibleSpace,
            .translatePlusCal,
        ]
    }

    func toolbarAllowedItemIdentifiers(_ toolbar: NSToolbar) -> [NSToolbarItem.Identifier] {
        [
            .toggleSidebar,
            .sidebarTrackingSeparator,
            .runModelCheck,
            .stopModelCheck,
            .checkProof,
            .translatePlusCal,
            .flexibleSpace,
            .space,
        ]
    }

    func toolbar(
        _ toolbar: NSToolbar,
        itemForItemIdentifier itemIdentifier: NSToolbarItem.Identifier,
        willBeInsertedIntoToolbar flag: Bool
    ) -> NSToolbarItem? {

        switch itemIdentifier {
        case .runModelCheck:
            let item = NSToolbarItem(itemIdentifier: itemIdentifier)
            item.label = "Run TLC"
            item.paletteLabel = "Run Model Check"
            item.toolTip = "Run TLC model checker (Cmd+R)"
            item.image = NSImage(systemSymbolName: "play.fill", accessibilityDescription: "Run")
            item.action = #selector(runModelCheck(_:))
            item.target = self
            return item

        case .stopModelCheck:
            let item = NSToolbarItem(itemIdentifier: itemIdentifier)
            item.label = "Stop"
            item.paletteLabel = "Stop Model Check"
            item.toolTip = "Stop model checking (Cmd+.)"
            item.image = NSImage(systemSymbolName: "stop.fill", accessibilityDescription: "Stop")
            item.action = #selector(stopModelCheck(_:))
            item.target = self
            return item

        case .checkProof:
            let item = NSToolbarItem(itemIdentifier: itemIdentifier)
            item.label = "Prove"
            item.paletteLabel = "Check Proofs"
            item.toolTip = "Check all proofs (Shift+Cmd+P)"
            item.image = NSImage(systemSymbolName: "checkmark.seal", accessibilityDescription: "Prove")
            item.action = #selector(checkProof(_:))
            item.target = self
            return item

        case .translatePlusCal:
            let item = NSToolbarItem(itemIdentifier: itemIdentifier)
            item.label = "Translate"
            item.paletteLabel = "Translate PlusCal"
            item.toolTip = "Translate PlusCal to TLA+ (Shift+Cmd+T)"
            item.image = NSImage(systemSymbolName: "arrow.triangle.2.circlepath", accessibilityDescription: "Translate")
            item.action = #selector(translatePlusCal(_:))
            item.target = self
            return item

        default:
            return nil
        }
    }
}

// MARK: - Toolbar Identifiers

extension NSToolbarItem.Identifier {
    static let runModelCheck = NSToolbarItem.Identifier("runModelCheck")
    static let stopModelCheck = NSToolbarItem.Identifier("stopModelCheck")
    static let checkProof = NSToolbarItem.Identifier("checkProof")
    static let translatePlusCal = NSToolbarItem.Identifier("translatePlusCal")
}

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

// MARK: - Model Config Editor Sheet

/// Sheet wrapper for ModelConfigEditor with save/cancel buttons
struct ModelConfigEditorSheet: View {
    @Binding var config: ModelConfig
    let symbols: [TLASymbol]
    @Binding var isPresented: Bool

    var body: some View {
        VStack(spacing: 0) {
            // Header
            HStack {
                Text("Model Configuration")
                    .font(.headline)
                Spacer()
                Button("Done") {
                    isPresented = false
                }
                .keyboardShortcut(.return, modifiers: [])
            }
            .padding()
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Config editor
            ModelConfigEditor(config: $config, symbols: symbols)
                .frame(minWidth: 500, minHeight: 400)
        }
        .frame(width: 600, height: 550)
    }
}

// MARK: - Navigator Sidebar

struct NavigatorSidebar: View {
    @ObservedObject var document: TLADocument
    @State private var selectedTab = 1 // Default to symbols

    private var symbolCount: Int {
        countSymbols(document.symbols)
    }

    private var problemCount: Int {
        document.diagnostics.count
    }

    var body: some View {
        VStack(spacing: 0) {
            // Custom tab bar with badges
            HStack(spacing: 4) {
                // File navigator tab with dirty indicator
                NavigatorTabButton(
                    icon: "folder",
                    isSelected: selectedTab == 0,
                    badge: document.hasUnautosavedChanges ? ("•", .orange) : nil,
                    action: { selectedTab = 0 }
                )
                .help("Files")

                // Symbols tab with count
                NavigatorTabButton(
                    icon: "list.bullet.indent",
                    isSelected: selectedTab == 1,
                    badge: symbolCount > 0 ? ("\(symbolCount)", .secondary) : nil,
                    action: { selectedTab = 1 }
                )
                .help("Symbols")

                // Search tab
                NavigatorTabButton(
                    icon: "magnifyingglass",
                    isSelected: selectedTab == 2,
                    badge: nil,
                    action: { selectedTab = 2 }
                )
                .help("Search (⇧⌘F)")
            }
            .padding(8)

            Divider()

            // Tab content
            switch selectedTab {
            case 0:
                FileNavigatorView(document: document)
            case 1:
                EnhancedSymbolOutline(document: document)
            case 2:
                SearchView(document: document)
            default:
                EmptyView()
            }
        }
    }

    private func countSymbols(_ symbols: [TLASymbol]) -> Int {
        symbols.reduce(0) { count, symbol in
            count + 1 + countSymbols(symbol.children)
        }
    }
}

// MARK: - Navigator Tab Button

private struct NavigatorTabButton: View {
    let icon: String
    let isSelected: Bool
    var badge: (String, Color)?
    let action: () -> Void

    var body: some View {
        Button(action: action) {
            HStack(spacing: 2) {
                Image(systemName: icon)
                    .font(.system(size: 12))

                if let badge = badge {
                    Text(badge.0)
                        .font(.system(size: 9, weight: .medium))
                        .foregroundColor(badge.1 == .secondary ? .secondary : .white)
                        .padding(.horizontal, badge.0 == "•" ? 0 : 4)
                        .padding(.vertical, 1)
                        .background(badge.1 == .secondary ? Color.clear : badge.1)
                        .clipShape(Capsule())
                }
            }
            .frame(minWidth: 36, minHeight: 24)
            .background(isSelected ? Color.accentColor.opacity(0.2) : Color.clear)
            .cornerRadius(6)
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Editor Area

struct EditorArea: View {
    @ObservedObject var document: TLADocument
    @StateObject private var findReplaceManager = FindReplaceManager()
    @State private var hoverInfo: HoverInfo?
    @State private var hoverPosition: NSPoint = .zero
    @State private var showHover = false
    @State private var showGoToLineSheet = false
    @State private var currentSymbol: TLASymbol?
    @State private var bottomPanelHeight: CGFloat = 150
    @State private var isDraggingDivider = false

    /// Total line count for Go to Line dialog
    private var lineCount: Int {
        document.content.components(separatedBy: "\n").count
    }

    /// Current line number based on selection
    private var currentLine: Int {
        let location = document.selectedRange.location
        let prefix = String(document.content.prefix(location))
        return prefix.components(separatedBy: "\n").count
    }

    /// Current column number based on selection
    private var currentColumn: Int {
        let location = document.selectedRange.location
        let prefix = String(document.content.prefix(location))
        let lines = prefix.components(separatedBy: "\n")
        return (lines.last?.count ?? 0) + 1
    }

    var body: some View {
        VStack(spacing: 0) {
            // Breadcrumb bar
            BreadcrumbBar(
                moduleName: document.moduleName,
                currentSymbol: currentSymbol,
                symbols: document.symbols,
                onNavigateToModule: {
                    // Navigate to top of document
                    document.selectedRange = NSRange(location: 0, length: 0)
                },
                onNavigateToSymbol: { symbol in
                    navigateToSymbol(symbol)
                }
            )

            Divider()

            // Find/Replace panel (shown conditionally)
            if findReplaceManager.isVisible {
                FindReplacePanel(manager: findReplaceManager)
                    .transition(.move(edge: .top).combined(with: .opacity))
            }

            // Editor with syntax highlighting and optional minimap
            HStack(spacing: 0) {
                ZStack(alignment: .topLeading) {
                    TLAEditorViewWithFindReplace(
                        text: $document.content,
                        selectedRange: $document.selectedRange,
                        findReplaceManager: findReplaceManager,
                        diagnostics: document.diagnostics,
                        onGoToDefinition: { characterOffset in
                            document.goToDefinition(at: characterOffset)
                        },
                        onHover: { characterOffset, screenPoint in
                            handleHover(at: characterOffset, screenPoint: screenPoint)
                        },
                        onHoverEnd: {
                            showHover = false
                        },
                        completionProvider: { offset in
                            TLACoreWrapper.shared.getContextCompletions(
                                at: offset,
                                in: document.content,
                                symbols: document.symbols
                            )
                        }
                    )
                    .editorFont(.monospacedSystemFont(ofSize: 13, weight: .regular))
                    .tabWidth(4)
                }
                .overlay(alignment: .topLeading) {
                    if showHover, let info = hoverInfo {
                        HoverPopover(info: info)
                            .offset(x: hoverPosition.x, y: hoverPosition.y + 20)
                    }
                }

                // Minimap (shown based on setting)
                MinimapContainer(
                    content: document.content,
                    visibleRange: document.selectedRange,
                    diagnostics: document.diagnostics,
                    onNavigate: { offset in
                        document.selectedRange = NSRange(location: offset, length: 0)
                    }
                )
            }

            Divider()

            // Status bar
            StatusBar(
                document: document,
                cursorLine: currentLine,
                cursorColumn: currentColumn
            )

            // Resizable divider for bottom panel
            ResizableDivider(
                isDragging: $isDraggingDivider,
                onDrag: { delta in
                    bottomPanelHeight = max(80, min(500, bottomPanelHeight - delta))
                }
            )

            // Bottom panel (model check progress, errors)
            BottomPanel(document: document)
                .frame(height: bottomPanelHeight)
        }
        .animation(.easeInOut(duration: 0.15), value: findReplaceManager.isVisible)
        .sheet(isPresented: $showGoToLineSheet) {
            GoToLineSheet(
                isPresented: $showGoToLineSheet,
                totalLines: lineCount
            ) { lineNumber in
                navigateToLine(lineNumber)
            }
        }
        .onChange(of: document.selectedRange) { _, newRange in
            updateCurrentSymbol(at: newRange.location)
        }
        .onReceive(NotificationCenter.default.publisher(for: .goToLine)) { _ in
            showGoToLineSheet = true
        }
        .onReceive(NotificationCenter.default.publisher(for: .showFindReplace)) { notification in
            let showReplace = (notification.userInfo?["showReplace"] as? Bool) ?? false
            findReplaceManager.showReplace = showReplace
            findReplaceManager.isVisible = true
        }
        .onReceive(NotificationCenter.default.publisher(for: .hideFindReplace)) { _ in
            findReplaceManager.isVisible = false
        }
        .onReceive(NotificationCenter.default.publisher(for: .toggleFindReplace)) { _ in
            findReplaceManager.isVisible.toggle()
        }
        .onReceive(NotificationCenter.default.publisher(for: .findNext)) { _ in
            findReplaceManager.findNext()
        }
        .onReceive(NotificationCenter.default.publisher(for: .findPrevious)) { _ in
            findReplaceManager.findPrevious()
        }
        .onReceive(NotificationCenter.default.publisher(for: .useSelectionForFind)) { _ in
            // Get selected text from document and use it for find
            let content = document.content as NSString
            let range = document.selectedRange
            if range.length > 0 && range.location + range.length <= content.length {
                let selectedText = content.substring(with: range)
                findReplaceManager.searchQuery = selectedText
                findReplaceManager.isVisible = true
            }
        }
    }

    // MARK: - Navigation Helpers

    private func navigateToLine(_ lineNumber: Int) {
        let lines = document.content.components(separatedBy: "\n")
        guard lineNumber >= 1 && lineNumber <= lines.count else { return }

        // Calculate character offset for the start of the target line
        var offset = 0
        for i in 0..<(lineNumber - 1) {
            offset += lines[i].count + 1 // +1 for newline
        }

        document.selectedRange = NSRange(location: offset, length: 0)
    }

    private func navigateToSymbol(_ symbol: TLASymbol) {
        // Calculate character offset from line/column
        let lines = document.content.components(separatedBy: "\n")
        let targetLine = Int(symbol.range.start.line)

        guard targetLine < lines.count else { return }

        var offset = 0
        for i in 0..<targetLine {
            offset += lines[i].count + 1
        }
        offset += Int(symbol.range.start.column)

        document.selectedRange = NSRange(location: offset, length: 0)
    }

    private func updateCurrentSymbol(at characterOffset: Int) {
        // Calculate current line from character offset
        let prefix = String(document.content.prefix(characterOffset))
        let line = prefix.components(separatedBy: "\n").count - 1

        currentSymbol = BreadcrumbBar.findSymbolAtLine(line, in: document.symbols)
    }

    private func handleHover(at characterOffset: Int, screenPoint: NSPoint) {
        let (line, column) = document.lineAndColumn(for: characterOffset)
        let position = TLAPosition(line: UInt32(line), column: UInt32(column))

        if let info = TLACoreWrapper.shared.getHoverDocumentation(
            at: position,
            in: document.content,
            symbols: document.symbols
        ) {
            hoverInfo = info
            // Convert screen point to view coordinates (approximate)
            hoverPosition = NSPoint(x: 50, y: CGFloat(line) * 18)
            showHover = true
        } else {
            showHover = false
        }
    }
}

// MARK: - TLAEditorView with FindReplace Integration

/// Wrapper for TLAEditorView that integrates with FindReplaceManager
struct TLAEditorViewWithFindReplace: NSViewRepresentable {

    @Binding var text: String
    @Binding var selectedRange: NSRange
    @ObservedObject var findReplaceManager: FindReplaceManager

    var configuration: TLASourceEditor.Configuration
    var diagnostics: [TLADiagnostic]
    var onTextChange: ((String) -> Void)?
    var onSelectionChange: ((NSRange) -> Void)?
    var onGoToDefinition: ((Int) -> Bool)?
    var onHover: ((Int, NSPoint) -> Void)?
    var onHoverEnd: (() -> Void)?
    var completionProvider: ((Int) -> [String])?
    var showFoldingGutter: Bool

    init(
        text: Binding<String>,
        selectedRange: Binding<NSRange> = .constant(NSRange(location: 0, length: 0)),
        findReplaceManager: FindReplaceManager,
        configuration: TLASourceEditor.Configuration = .init(),
        diagnostics: [TLADiagnostic] = [],
        onTextChange: ((String) -> Void)? = nil,
        onSelectionChange: ((NSRange) -> Void)? = nil,
        onGoToDefinition: ((Int) -> Bool)? = nil,
        onHover: ((Int, NSPoint) -> Void)? = nil,
        onHoverEnd: (() -> Void)? = nil,
        completionProvider: ((Int) -> [String])? = nil,
        showFoldingGutter: Bool = true
    ) {
        self._text = text
        self._selectedRange = selectedRange
        self.findReplaceManager = findReplaceManager
        self.configuration = configuration
        self.diagnostics = diagnostics
        self.onTextChange = onTextChange
        self.onSelectionChange = onSelectionChange
        self.onGoToDefinition = onGoToDefinition
        self.onHover = onHover
        self.onHoverEnd = onHoverEnd
        self.completionProvider = completionProvider
        self.showFoldingGutter = showFoldingGutter
    }

    func makeNSView(context: Context) -> EditorContainerView {
        // Create scroll view
        let scrollView = NSScrollView()
        scrollView.hasVerticalScroller = true
        scrollView.autohidesScrollers = true
        scrollView.borderType = .noBorder

        // Check word wrap setting
        let wordWrap = UserDefaults.standard.bool(forKey: "wordWrap")

        // Create custom text view
        let contentSize = scrollView.contentSize
        let containerWidth = wordWrap ? contentSize.width : CGFloat.greatestFiniteMagnitude
        let textContainer = NSTextContainer(containerSize: NSSize(width: containerWidth, height: CGFloat.greatestFiniteMagnitude))
        textContainer.widthTracksTextView = wordWrap

        let layoutManager = NSLayoutManager()
        layoutManager.addTextContainer(textContainer)

        let textStorage = NSTextStorage()
        textStorage.addLayoutManager(layoutManager)

        let textView = GoToDefinitionTextView(frame: NSRect(origin: .zero, size: contentSize), textContainer: textContainer)

        // Configure the text view for code editing
        textView.isEditable = true
        textView.isSelectable = true
        textView.isRichText = false
        textView.allowsUndo = true
        textView.font = configuration.font
        textView.backgroundColor = .textBackgroundColor
        textView.insertionPointColor = .textColor
        textView.isAutomaticQuoteSubstitutionEnabled = false
        textView.isAutomaticDashSubstitutionEnabled = false
        textView.isAutomaticTextReplacementEnabled = false
        textView.isAutomaticSpellingCorrectionEnabled = false
        textView.isVerticallyResizable = true
        textView.isHorizontallyResizable = !wordWrap
        textView.autoresizingMask = wordWrap ? [.width] : []
        textView.minSize = NSSize(width: 0, height: contentSize.height)
        textView.maxSize = NSSize(width: wordWrap ? CGFloat.greatestFiniteMagnitude : CGFloat.greatestFiniteMagnitude, height: CGFloat.greatestFiniteMagnitude)

        // Enable/disable horizontal scrolling based on word wrap
        scrollView.hasHorizontalScroller = !wordWrap

        // Wire up callbacks
        textView.onGoToDefinition = onGoToDefinition
        textView.onHover = onHover
        textView.onHoverEnd = onHoverEnd
        textView.completionProvider = completionProvider

        // Set up IntelliSense
        textView.setupIntelliSense()
        textView.detailedCompletionProvider = context.coordinator.getDetailedCompletions
        textView.signatureHelpProvider = context.coordinator.getSignatureHelp

        // Set text
        textView.string = text

        // Add to scroll view
        scrollView.documentView = textView

        // Add small top padding
        textView.textContainerInset = NSSize(width: 0, height: 4)

        // Store reference and initial text
        context.coordinator.textView = textView
        context.coordinator.lastKnownText = text

        // Connect FindReplaceManager to the text view
        Task { @MainActor in
            findReplaceManager.textView = textView
        }

        // Create highlighter for this text view with saved color scheme
        let savedColorScheme = UserDefaults.standard.string(forKey: "editorColorScheme") ?? "Default"
        let theme = EditorColorScheme(rawValue: savedColorScheme)?.syntaxTheme ?? .default
        context.coordinator.highlighter = TLASyntaxHighlighter(textView: textView, theme: theme)
        context.coordinator.highlighter?.highlightImmediately()

        // Apply theme colors to text view
        textView.backgroundColor = theme.background
        textView.insertionPointColor = theme.cursor

        // Create diagnostic highlighter
        context.coordinator.diagnosticHighlighter = DiagnosticHighlighter(textView: textView)
        if !diagnostics.isEmpty {
            context.coordinator.diagnosticHighlighter?.updateDiagnostics(diagnostics, in: text)
            context.coordinator.lastKnownDiagnostics = diagnostics
        }

        // Set up editor enhancements (current line highlight, bracket matching)
        let highlightCurrentLine = UserDefaults.standard.bool(forKey: "highlightCurrentLine")
        let matchBrackets = UserDefaults.standard.bool(forKey: "settings.editor.matchBrackets")
        context.coordinator.editorEnhancements = EditorEnhancements(
            textView: textView,
            enableCurrentLineHighlight: highlightCurrentLine,
            enableBracketMatching: matchBrackets
        )

        // Set up folding if enabled
        var foldingManager: CodeFoldingManager? = nil
        if showFoldingGutter {
            let manager = CodeFoldingManager(textView: textView)
            textView.foldingManager = manager
            context.coordinator.foldingManager = manager
            foldingManager = manager

            Task { @MainActor in
                manager.updateFoldingRanges(from: text)
            }
        }

        // Listen for text changes
        NotificationCenter.default.addObserver(
            context.coordinator,
            selector: #selector(Coordinator.textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )

        // Create container with line numbers, folding gutter, and editor
        let containerView = EditorContainerView(
            scrollView: scrollView,
            textView: textView,
            showLineNumbers: configuration.showLineNumbers,
            foldingManager: foldingManager
        )

        // Make first responder
        DispatchQueue.main.async {
            textView.window?.makeFirstResponder(textView)
        }

        return containerView
    }

    func updateNSView(_ containerView: EditorContainerView, context: Context) {
        guard let textView = containerView.scrollView.documentView as? NSTextView else { return }

        // Update font if changed
        if textView.font != configuration.font {
            textView.font = configuration.font
        }

        // Update FindReplaceManager reference if needed
        if findReplaceManager.textView !== textView {
            Task { @MainActor in
                findReplaceManager.textView = textView
            }
        }

        // Only update if the binding changed from OUTSIDE
        if context.coordinator.lastKnownText != text {
            context.coordinator.lastKnownText = text

            NotificationCenter.default.removeObserver(
                context.coordinator,
                name: NSText.didChangeNotification,
                object: textView
            )

            textView.string = text

            NotificationCenter.default.addObserver(
                context.coordinator,
                selector: #selector(Coordinator.textDidChange(_:)),
                name: NSText.didChangeNotification,
                object: textView
            )

            context.coordinator.highlighter?.highlightImmediately()

            // Re-apply diagnostics after text change
            if !context.coordinator.lastKnownDiagnostics.isEmpty {
                context.coordinator.diagnosticHighlighter?.updateDiagnostics(
                    context.coordinator.lastKnownDiagnostics,
                    in: text
                )
            }
        }

        // Update diagnostics if changed
        if !diagnosticsEqual(context.coordinator.lastKnownDiagnostics, diagnostics) {
            context.coordinator.lastKnownDiagnostics = diagnostics
            context.coordinator.diagnosticHighlighter?.updateDiagnostics(diagnostics, in: textView.string)
        }

        // Handle selection changes from external sources (e.g., symbol outline navigation)
        if context.coordinator.lastKnownSelection != selectedRange {
            context.coordinator.lastKnownSelection = selectedRange

            // Ensure the range is valid
            let maxLocation = textView.string.count
            let validLocation = min(selectedRange.location, maxLocation)
            let validLength = min(selectedRange.length, maxLocation - validLocation)
            let validRange = NSRange(location: validLocation, length: validLength)

            // Set selection and scroll to it
            textView.setSelectedRange(validRange)
            textView.scrollRangeToVisible(validRange)
        }
    }

    private func diagnosticsEqual(_ lhs: [TLADiagnostic], _ rhs: [TLADiagnostic]) -> Bool {
        guard lhs.count == rhs.count else { return false }
        for (l, r) in zip(lhs, rhs) {
            if l.id != r.id { return false }
        }
        return true
    }

    func makeCoordinator() -> Coordinator {
        Coordinator(self)
    }

    class Coordinator: NSObject, NSTextViewDelegate {
        var parent: TLAEditorViewWithFindReplace
        weak var textView: NSTextView?
        var highlighter: TLASyntaxHighlighter?
        var diagnosticHighlighter: DiagnosticHighlighter?
        var editorEnhancements: EditorEnhancements?
        var foldingManager: CodeFoldingManager?
        weak var gutterView: FoldingGutterView?
        var isUpdating = false
        var lastKnownText: String = ""
        var lastKnownSelection: NSRange = NSRange(location: 0, length: 0)
        var lastKnownDiagnostics: [TLADiagnostic] = []
        private var notificationObservers: [NSObjectProtocol] = []
        private var diagnosticsTask: Task<Void, Never>?
        private var foldingTask: Task<Void, Never>?

        init(_ parent: TLAEditorViewWithFindReplace) {
            self.parent = parent
            super.init()
            setupFoldNotifications()
            setupColorSchemeNotification()
        }

        private func setupColorSchemeNotification() {
            let observer = NotificationCenter.default.addObserver(
                forName: .editorColorSchemeDidChange,
                object: nil,
                queue: .main
            ) { [weak self] notification in
                guard let self = self,
                      let textView = self.textView else { return }
                if let colorSchemeName = notification.userInfo?["colorScheme"] as? String,
                   let scheme = EditorColorScheme(rawValue: colorSchemeName) {
                    let theme = scheme.syntaxTheme
                    self.highlighter?.applyTheme(theme)

                    // Update text view colors
                    textView.backgroundColor = theme.background
                    textView.insertionPointColor = theme.cursor
                }
            }
            notificationObservers.append(observer)
        }

        deinit {
            // Cancel any pending tasks
            diagnosticsTask?.cancel()
            foldingTask?.cancel()
            // Remove notification observers
            for observer in notificationObservers {
                NotificationCenter.default.removeObserver(observer)
            }
        }

        private func setupFoldNotifications() {
            let foldAllObserver = NotificationCenter.default.addObserver(
                forName: .foldAll,
                object: nil,
                queue: .main
            ) { [weak self] _ in
                self?.foldingManager?.foldAll()
                self?.highlighter?.highlightImmediately()
            }
            notificationObservers.append(foldAllObserver)

            let unfoldAllObserver = NotificationCenter.default.addObserver(
                forName: .unfoldAll,
                object: nil,
                queue: .main
            ) { [weak self] _ in
                self?.foldingManager?.unfoldAll()
                self?.highlighter?.highlightImmediately()
            }
            notificationObservers.append(unfoldAllObserver)

            let toggleFoldObserver = NotificationCenter.default.addObserver(
                forName: .toggleFold,
                object: nil,
                queue: .main
            ) { [weak self] _ in
                self?.toggleFoldAtCursor()
            }
            notificationObservers.append(toggleFoldObserver)
        }

        private func toggleFoldAtCursor() {
            guard let textView = textView,
                  let foldingManager = foldingManager else { return }

            let cursorLocation = textView.selectedRange().location
            let text = textView.string
            let lines = text.prefix(cursorLocation).components(separatedBy: "\n")
            let currentLine = lines.count - 1

            if let range = foldingManager.foldingRange(at: currentLine) {
                foldingManager.toggleFold(at: range.startLine)
            } else {
                for range in foldingManager.foldingRanges {
                    if currentLine >= range.startLine && currentLine <= range.endLine {
                        foldingManager.toggleFold(at: range.startLine)
                        break
                    }
                }
            }
            highlighter?.highlightImmediately()
        }

        @objc public func textDidChange(_ notification: Notification) {
            guard let textView = textView else { return }

            let newText = textView.string
            lastKnownText = newText

            isUpdating = true
            parent.text = newText
            parent.onTextChange?(newText)
            isUpdating = false

            highlighter?.scheduleHighlighting()

            // Cancel any pending tasks before starting new ones
            diagnosticsTask?.cancel()
            foldingTask?.cancel()

            // Re-apply diagnostics after a short delay to let highlighting finish
            diagnosticsTask = Task { @MainActor in
                try? await Task.sleep(nanoseconds: 50_000_000) // 50ms
                guard !Task.isCancelled else { return }
                if !self.lastKnownDiagnostics.isEmpty {
                    self.diagnosticHighlighter?.updateDiagnostics(self.lastKnownDiagnostics, in: newText)
                }
            }

            foldingTask = Task { @MainActor in
                guard !Task.isCancelled else { return }
                self.foldingManager?.updateFoldingRanges(from: newText)
            }
        }

        @objc func scrollViewDidScroll(_ notification: Notification) {
            gutterView?.needsDisplay = true
        }

        // MARK: - IntelliSense Support

        /// Provide detailed completions for the current position
        @MainActor
        func getDetailedCompletions(at position: Int) async -> [TLADetailedCompletionItem] {
            guard let textView = textView else { return [] }
            let text = textView.string

            // Calculate position as TLAPosition
            let lines = text.prefix(position).components(separatedBy: "\n")
            let lineNumber = UInt32(lines.count - 1)
            let columnNumber = UInt32(lines.last?.count ?? 0)
            let tlaPosition = TLAPosition(line: lineNumber, column: columnNumber)

            // Get parse result and completions from TLACore
            do {
                let parseResult = try await TLACoreWrapper.shared.parse(text)
                let completions = await TLACoreWrapper.shared.getDetailedCompletions(
                    from: parseResult,
                    at: tlaPosition
                )
                return completions
            } catch {
                return []
            }
        }

        /// Provide signature help for operator calls
        @MainActor
        func getSignatureHelp(at position: Int) async -> TLASignatureHelp? {
            guard let textView = textView else { return nil }
            let text = textView.string

            // Calculate position as TLAPosition
            let lines = text.prefix(position).components(separatedBy: "\n")
            let lineNumber = UInt32(lines.count - 1)
            let columnNumber = UInt32(lines.last?.count ?? 0)
            let tlaPosition = TLAPosition(line: lineNumber, column: columnNumber)

            // Get parse result and signature help from TLACore
            do {
                let parseResult = try await TLACoreWrapper.shared.parse(text)
                let signatureHelp = await TLACoreWrapper.shared.getSignatureHelp(
                    from: parseResult,
                    at: tlaPosition
                )
                return signatureHelp
            } catch {
                return nil
            }
        }
    }
}

// MARK: - Line Number Gutter View

class LineNumberGutterView: NSView {
    private weak var textView: NSTextView?
    let gutterWidth: CGFloat = 44

    override var isFlipped: Bool { true }

    init(textView: NSTextView) {
        self.textView = textView
        super.init(frame: NSRect(x: 0, y: 0, width: gutterWidth, height: 100))

        // Observe text changes
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    deinit {
        NotificationCenter.default.removeObserver(self)
    }

    func scrollViewBoundsDidChange() {
        needsDisplay = true
    }

    @objc private func textDidChange(_ notification: Notification) {
        needsDisplay = true
    }

    override func draw(_ dirtyRect: NSRect) {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let scrollView = textView.enclosingScrollView else {
            return
        }

        // Background
        NSColor.textBackgroundColor.setFill()
        bounds.fill()

        // Separator line
        NSColor.separatorColor.setStroke()
        let separatorPath = NSBezierPath()
        separatorPath.move(to: NSPoint(x: bounds.width - 0.5, y: 0))
        separatorPath.line(to: NSPoint(x: bounds.width - 0.5, y: bounds.height))
        separatorPath.stroke()

        let text = textView.string
        guard !text.isEmpty else { return }

        let font = NSFont.monospacedDigitSystemFont(ofSize: 11, weight: .regular)
        let attrs: [NSAttributedString.Key: Any] = [
            .font: font,
            .foregroundColor: NSColor.secondaryLabelColor
        ]

        // Get visible rect in document coordinates
        let visibleRect = scrollView.documentVisibleRect
        let containerOrigin = textView.textContainerOrigin

        // Get all line ranges
        var lineRanges: [NSRange] = []
        var searchStart = 0
        let nsText = text as NSString
        while searchStart < nsText.length {
            let lineRange = nsText.lineRange(for: NSRange(location: searchStart, length: 0))
            lineRanges.append(lineRange)
            searchStart = NSMaxRange(lineRange)
        }

        // Draw each visible line number
        for (index, lineRange) in lineRanges.enumerated() {
            let lineNumber = index + 1

            // Get the glyph range for this line
            let glyphRange = layoutManager.glyphRange(forCharacterRange: lineRange, actualCharacterRange: nil)
            guard glyphRange.location != NSNotFound else { continue }

            // Get the line rect in layout manager coordinates
            let lineRect = layoutManager.lineFragmentRect(forGlyphAt: glyphRange.location, effectiveRange: nil)

            // Calculate Y position in document coordinates
            let docY = lineRect.minY + containerOrigin.y

            // Skip if above visible area
            if docY + lineRect.height < visibleRect.minY { continue }
            // Stop if below visible area
            if docY > visibleRect.maxY { break }

            // Convert to gutter view coordinates (relative to visible area)
            let gutterY = docY - visibleRect.minY

            let lineNumberString = "\(lineNumber)"
            let attrString = NSAttributedString(string: lineNumberString, attributes: attrs)
            let stringSize = attrString.size()

            let x = bounds.width - stringSize.width - 6
            let y = gutterY + (lineRect.height - stringSize.height) / 2

            attrString.draw(at: NSPoint(x: x, y: y))
        }
    }
}

// MARK: - Editor Container View (Line Numbers + Editor)

class EditorContainerView: NSView {
    let gutterView: LineNumberGutterView
    var foldingGutterView: FoldingGutterOverlay?
    let scrollView: NSScrollView
    private var scrollObserver: NSObjectProtocol?

    private let foldingGutterWidth: CGFloat = 14

    override var isFlipped: Bool { true }

    init(scrollView: NSScrollView, textView: NSTextView, showLineNumbers: Bool, foldingManager: CodeFoldingManager? = nil) {
        self.scrollView = scrollView
        self.gutterView = LineNumberGutterView(textView: textView)
        super.init(frame: .zero)

        if showLineNumbers {
            addSubview(gutterView)
        }

        // Add folding gutter if manager provided
        if let manager = foldingManager {
            let foldingView = FoldingGutterOverlay(textView: textView, foldingManager: manager)
            self.foldingGutterView = foldingView
            addSubview(foldingView)
        }

        addSubview(scrollView)

        // Observe scroll changes
        scrollObserver = NotificationCenter.default.addObserver(
            forName: NSView.boundsDidChangeNotification,
            object: scrollView.contentView,
            queue: .main
        ) { [weak self] _ in
            self?.gutterView.scrollViewBoundsDidChange()
            self?.foldingGutterView?.needsDisplay = true
        }
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    deinit {
        if let observer = scrollObserver {
            NotificationCenter.default.removeObserver(observer)
        }
    }

    override func layout() {
        super.layout()

        let lineNumberWidth = gutterView.gutterWidth
        let showLineNumbers = gutterView.superview != nil
        let showFolding = foldingGutterView?.superview != nil
        let foldWidth = showFolding ? foldingGutterWidth : 0
        let totalGutterWidth = (showLineNumbers ? lineNumberWidth : 0) + foldWidth

        if showLineNumbers {
            gutterView.frame = NSRect(x: 0, y: 0, width: lineNumberWidth, height: bounds.height)
        }

        if showFolding, let foldingView = foldingGutterView {
            let foldX = showLineNumbers ? lineNumberWidth : 0
            foldingView.frame = NSRect(x: foldX, y: 0, width: foldingGutterWidth, height: bounds.height)
        }

        scrollView.frame = NSRect(x: totalGutterWidth, y: 0, width: bounds.width - totalGutterWidth, height: bounds.height)
    }
}

// MARK: - View Modifiers for TLAEditorViewWithFindReplace

extension TLAEditorViewWithFindReplace {
    func theme(_ theme: SyntaxTheme) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.configuration.theme = theme
        return copy
    }

    func editorFont(_ font: NSFont) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.configuration.font = font
        return copy
    }

    func tabWidth(_ width: Int) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.configuration.tabWidth = width
        return copy
    }

    func showLineNumbers(_ show: Bool) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.configuration.showLineNumbers = show
        return copy
    }

    func lineHeight(_ multiplier: CGFloat) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.configuration.lineHeight = multiplier
        return copy
    }

    func onTextChange(_ handler: @escaping (String) -> Void) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.onTextChange = handler
        return copy
    }

    func onSelectionChange(_ handler: @escaping (NSRange) -> Void) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.onSelectionChange = handler
        return copy
    }

    func showFoldingGutter(_ show: Bool) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.showFoldingGutter = show
        return copy
    }

    func diagnostics(_ diagnostics: [TLADiagnostic]) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.diagnostics = diagnostics
        return copy
    }
}

// MARK: - Hover Popover

struct HoverPopover: View {
    let info: HoverInfo

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            HStack(spacing: 6) {
                kindIcon
                Text(info.title)
                    .font(.system(.body, design: .monospaced).bold())
            }

            if let signature = info.signature {
                Text(signature)
                    .font(.system(.caption, design: .monospaced))
                    .foregroundColor(.secondary)
            }

            Text(info.description)
                .font(.caption)
                .foregroundColor(.primary)
        }
        .padding(8)
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(6)
        .shadow(color: .black.opacity(0.2), radius: 4, x: 0, y: 2)
        .fixedSize()
    }

    @ViewBuilder
    private var kindIcon: some View {
        switch info.kind {
        case .keyword:
            Image(systemName: "k.square.fill").foregroundColor(.blue)
        case .operator:
            Image(systemName: "function").foregroundColor(.purple)
        case .variable:
            Image(systemName: "v.square").foregroundColor(.green)
        case .constant:
            Image(systemName: "c.square").foregroundColor(.orange)
        case .module:
            Image(systemName: "cube").foregroundColor(.blue)
        case .theorem:
            Image(systemName: "checkmark.seal").foregroundColor(.teal)
        case .definition:
            Image(systemName: "equal.square").foregroundColor(.indigo)
        }
    }
}

// MARK: - Resizable Divider

/// A draggable divider for resizing panels
struct ResizableDivider: View {
    @Binding var isDragging: Bool
    let onDrag: (CGFloat) -> Void

    var body: some View {
        Rectangle()
            .fill(isDragging ? Color.accentColor : Color(NSColor.separatorColor))
            .frame(height: isDragging ? 3 : 1)
            .frame(maxWidth: .infinity)
            .contentShape(Rectangle().size(width: .infinity, height: 8))
            .onHover { hovering in
                if hovering {
                    NSCursor.resizeUpDown.push()
                } else {
                    NSCursor.pop()
                }
            }
            .gesture(
                DragGesture(minimumDistance: 1)
                    .onChanged { value in
                        isDragging = true
                        onDrag(value.translation.height)
                    }
                    .onEnded { _ in
                        isDragging = false
                    }
            )
    }
}

struct BottomPanel: View {
    @ObservedObject var document: TLADocument
    @State private var selectedTab = 0

    private var errorCount: Int {
        document.diagnostics.filter { $0.severity == .error }.count
    }

    private var warningCount: Int {
        document.diagnostics.filter { $0.severity == .warning }.count
    }

    var body: some View {
        VStack(spacing: 0) {
            // Tab bar
            HStack {
                // Problems tab with badge
                Button {
                    selectedTab = 0
                } label: {
                    HStack(spacing: 4) {
                        Text("Problems")
                        if errorCount > 0 || warningCount > 0 {
                            BadgeView(
                                count: errorCount + warningCount,
                                color: errorCount > 0 ? .red : .orange
                            )
                        }
                    }
                }
                .buttonStyle(.plain)
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(selectedTab == 0 ? Color.accentColor.opacity(0.2) : Color.clear)
                .cornerRadius(4)

                Button("Output") { selectedTab = 1 }
                    .buttonStyle(.plain)
                    .padding(.horizontal, 8)
                    .padding(.vertical, 4)
                    .background(selectedTab == 1 ? Color.accentColor.opacity(0.2) : Color.clear)
                    .cornerRadius(4)

                // Model Check tab with status indicator
                Button {
                    selectedTab = 2
                } label: {
                    HStack(spacing: 4) {
                        Text("Model Check")
                        if let session = document.tlcSession, session.isRunning {
                            ProgressView()
                                .controlSize(.mini)
                                .scaleEffect(0.7)
                        } else if let result = document.lastTLCResult {
                            Image(systemName: result.success ? "checkmark.circle.fill" : "xmark.circle.fill")
                                .font(.caption2)
                                .foregroundColor(result.success ? .green : .red)
                        }
                    }
                }
                .buttonStyle(.plain)
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(selectedTab == 2 ? Color.accentColor.opacity(0.2) : Color.clear)
                .cornerRadius(4)

                Spacer()
            }
            .padding(4)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Content
            switch selectedTab {
            case 0:
                ProblemsPanelContent(diagnostics: document.diagnostics)
            case 1:
                OutputPanelContent()
            case 2:
                ModelCheckPanelContent(document: document)
            default:
                EmptyView()
            }
        }
    }
}

struct ProblemsPanelContent: View {
    let diagnostics: [TLADiagnostic]

    var body: some View {
        List {
            if diagnostics.isEmpty {
                Text("No problems")
                    .foregroundColor(.secondary)
            } else {
                ForEach(diagnostics) { diagnostic in
                    HStack {
                        diagnosticIcon(for: diagnostic.severity)
                        Text(diagnostic.message)
                            .font(.system(.body, design: .monospaced))
                            .textSelection(.enabled)
                        Spacer()
                        Text("Ln \(diagnostic.range.start.line + 1)")
                            .font(.caption)
                            .foregroundColor(.secondary)
                    }
                }
            }
        }
    }

    @ViewBuilder
    private func diagnosticIcon(for severity: TLADiagnosticSeverity) -> some View {
        switch severity {
        case .error:
            Image(systemName: "xmark.circle.fill").foregroundColor(.red)
        case .warning:
            Image(systemName: "exclamationmark.triangle.fill").foregroundColor(.yellow)
        case .information:
            Image(systemName: "info.circle.fill").foregroundColor(.blue)
        case .hint:
            Image(systemName: "lightbulb.fill").foregroundColor(.green)
        }
    }
}

struct OutputPanelContent: View {
    @ObservedObject private var outputManager = OutputManager.shared
    @State private var autoScroll = true

    var body: some View {
        VStack(spacing: 0) {
            // Toolbar
            HStack(spacing: 8) {
                // Source filter
                Picker("Source", selection: $outputManager.selectedSource) {
                    Text("All").tag(Optional<OutputManager.OutputSource>.none)
                    ForEach(OutputManager.OutputSource.allCases, id: \.self) { source in
                        Text(source.rawValue).tag(Optional(source))
                    }
                }
                .pickerStyle(.menu)
                .frame(width: 100)

                Toggle("Errors Only", isOn: $outputManager.showErrorsOnly)
                    .toggleStyle(.checkbox)

                Spacer()

                Toggle("Auto-scroll", isOn: $autoScroll)
                    .toggleStyle(.checkbox)

                Button(action: { outputManager.clear() }) {
                    Image(systemName: "trash")
                }
                .buttonStyle(.borderless)
                .help("Clear Output")
            }
            .padding(.horizontal, 8)
            .padding(.vertical, 4)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Output content
            if outputManager.filteredEntries.isEmpty {
                VStack {
                    Spacer()
                    Text("No output")
                        .foregroundColor(.secondary)
                    Spacer()
                }
            } else {
                SelectableOutputView(
                    entries: outputManager.filteredEntries,
                    autoScroll: autoScroll
                )
            }
        }
    }
}

// MARK: - Selectable Output View

/// A text view that allows selecting text across multiple lines
struct SelectableOutputView: NSViewRepresentable {
    let entries: [OutputManager.OutputEntry]
    let autoScroll: Bool

    func makeNSView(context: Context) -> NSScrollView {
        let scrollView = NSScrollView()
        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = false
        scrollView.autohidesScrollers = true

        let textView = NSTextView()
        textView.isEditable = false
        textView.isSelectable = true
        textView.backgroundColor = .clear
        textView.drawsBackground = false
        textView.font = NSFont.monospacedSystemFont(ofSize: 11, weight: .regular)
        textView.textContainerInset = NSSize(width: 8, height: 4)
        textView.autoresizingMask = [.width]
        textView.isVerticallyResizable = true
        textView.isHorizontallyResizable = false
        textView.textContainer?.widthTracksTextView = true
        textView.textContainer?.containerSize = NSSize(width: CGFloat.greatestFiniteMagnitude, height: CGFloat.greatestFiniteMagnitude)

        scrollView.documentView = textView
        return scrollView
    }

    func updateNSView(_ scrollView: NSScrollView, context: Context) {
        guard let textView = scrollView.documentView as? NSTextView else { return }

        let attributedString = NSMutableAttributedString()
        let defaultAttrs: [NSAttributedString.Key: Any] = [
            .font: NSFont.monospacedSystemFont(ofSize: 11, weight: .regular),
            .foregroundColor: NSColor.textColor
        ]

        for entry in entries {
            // Timestamp
            let timestamp = NSAttributedString(
                string: entry.formattedTimestamp + "  ",
                attributes: [
                    .font: NSFont.monospacedSystemFont(ofSize: 10, weight: .regular),
                    .foregroundColor: NSColor.secondaryLabelColor
                ]
            )
            attributedString.append(timestamp)

            // Source
            let sourceColor: NSColor = {
                switch entry.source {
                case .tlc: return .systemBlue
                case .tlapm: return .systemPurple
                case .parser: return .systemGreen
                case .system: return .systemGray
                }
            }()
            let source = NSAttributedString(
                string: "[\(entry.source.rawValue)]  ",
                attributes: [
                    .font: NSFont.monospacedSystemFont(ofSize: 10, weight: .medium),
                    .foregroundColor: sourceColor
                ]
            )
            attributedString.append(source)

            // Message
            let message = NSAttributedString(
                string: entry.message + "\n",
                attributes: [
                    .font: NSFont.monospacedSystemFont(ofSize: 11, weight: .regular),
                    .foregroundColor: entry.isError ? NSColor.systemRed : NSColor.textColor
                ]
            )
            attributedString.append(message)
        }

        textView.textStorage?.setAttributedString(attributedString)

        // Auto-scroll to bottom
        if autoScroll && !entries.isEmpty {
            textView.scrollToEndOfDocument(nil)
        }
    }
}

struct OutputEntryRow: View {
    let entry: OutputManager.OutputEntry

    var body: some View {
        HStack(alignment: .top, spacing: 8) {
            Text(entry.formattedTimestamp)
                .font(.system(size: 10, design: .monospaced))
                .foregroundColor(.secondary)
                .frame(width: 60, alignment: .leading)

            Text("[\(entry.source.rawValue)]")
                .font(.system(size: 10, weight: .medium, design: .monospaced))
                .foregroundColor(sourceColor(entry.source))
                .frame(width: 50, alignment: .leading)

            Text(entry.message)
                .font(.system(size: 11, design: .monospaced))
                .foregroundColor(entry.isError ? .red : .primary)
                .textSelection(.enabled)

            Spacer()
        }
        .padding(.vertical, 1)
    }

    private func sourceColor(_ source: OutputManager.OutputSource) -> Color {
        switch source {
        case .tlc: return .blue
        case .tlapm: return .purple
        case .parser: return .orange
        case .system: return .gray
        }
    }
}

struct ModelCheckPanelContent: View {
    @ObservedObject var document: TLADocument

    var body: some View {
        ModelCheckPanelCompact(document: document)
    }
}

// MARK: - Badge View

/// A small badge showing a count, typically for notifications/errors
struct BadgeView: View {
    let count: Int
    let color: Color

    var body: some View {
        Text("\(count)")
            .font(.system(size: 10, weight: .bold))
            .foregroundColor(.white)
            .padding(.horizontal, 5)
            .padding(.vertical, 1)
            .background(color)
            .clipShape(Capsule())
    }
}

// MARK: - Inspector Sidebar

// InspectorSidebar is now defined in Views/Sidebar/InspectorViews.swift as EnhancedInspectorSidebar
typealias InspectorSidebar = EnhancedInspectorSidebar

