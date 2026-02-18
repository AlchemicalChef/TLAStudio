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

// DocumentWindowContent is defined in Document/DocumentWindowContent.swift
// ModelConfigEditorSheet is defined in TLC/ModelConfigEditor.swift
// NavigatorSidebar and NavigatorTabButton are defined in Views/Sidebar/NavigatorSidebar.swift

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
        let wordWrap = UserDefaults.standard.bool(forKey: UserSettings.Keys.wordWrap)

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
        let savedColorScheme = UserDefaults.standard.string(forKey: UserSettings.Keys.colorScheme) ?? "Default"
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
        let highlightCurrentLine = UserDefaults.standard.bool(forKey: UserSettings.Keys.highlightCurrentLine)
        let matchBrackets = UserDefaults.standard.bool(forKey: UserSettings.Keys.matchBrackets)
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

// LineNumberGutterView, EditorContainerView, ResizableDivider are defined in Views/EditorComponents.swift

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

// HoverPopover is defined in Document/HoverPopover.swift
// ResizableDivider is defined in Views/EditorComponents.swift

// MARK: - Inspector Sidebar

// InspectorSidebar is now defined in Views/Sidebar/InspectorViews.swift as EnhancedInspectorSidebar
typealias InspectorSidebar = EnhancedInspectorSidebar

