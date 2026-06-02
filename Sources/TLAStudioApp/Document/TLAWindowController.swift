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
        NotificationCenter.default.post(name: .toggleNavigatorSidebar, object: tlaDocument)
    }

    @objc func toggleInspector(_ sender: Any?) {
        NotificationCenter.default.post(name: .toggleInspectorSidebar, object: tlaDocument)
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

    var notificationTarget: AnyObject?
    var configuration: TLASourceEditor.Configuration
    var diagnostics: [TLADiagnostic]
    var proofAnnotations: [ProofAnnotation]
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
        notificationTarget: AnyObject? = nil,
        configuration: TLASourceEditor.Configuration = .init(),
        diagnostics: [TLADiagnostic] = [],
        proofAnnotations: [ProofAnnotation] = [],
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
        self.notificationTarget = notificationTarget
        self.configuration = configuration
        self.diagnostics = diagnostics
        self.proofAnnotations = proofAnnotations
        self.onTextChange = onTextChange
        self.onSelectionChange = onSelectionChange
        self.onGoToDefinition = onGoToDefinition
        self.onHover = onHover
        self.onHoverEnd = onHoverEnd
        self.completionProvider = completionProvider
        self.showFoldingGutter = showFoldingGutter
    }

    private func makeEditorScrollView() -> NSScrollView {
        let scrollView = NSScrollView()
        scrollView.hasVerticalScroller = true
        scrollView.autohidesScrollers = true
        scrollView.borderType = .noBorder
        return scrollView
    }

    private func makeEditorTextView(in scrollView: NSScrollView) -> GoToDefinitionTextView {
        let wordWrap = UserSettings.shared.wordWrap
        let contentSize = scrollView.contentSize
        let containerWidth = wordWrap ? contentSize.width : CGFloat.greatestFiniteMagnitude
        let textContainer = NSTextContainer(
            containerSize: NSSize(width: containerWidth, height: CGFloat.greatestFiniteMagnitude)
        )
        textContainer.widthTracksTextView = wordWrap

        let layoutManager = NSLayoutManager()
        layoutManager.addTextContainer(textContainer)

        let textStorage = NSTextStorage()
        textStorage.addLayoutManager(layoutManager)

        let textView = GoToDefinitionTextView(
            frame: NSRect(origin: .zero, size: contentSize),
            textContainer: textContainer
        )
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
        textView.editorConfiguration = configuration
        textView.isVerticallyResizable = true
        textView.isHorizontallyResizable = !wordWrap
        textView.autoresizingMask = wordWrap ? [.width] : []
        textView.minSize = NSSize(width: 0, height: contentSize.height)
        textView.maxSize = NSSize(
            width: CGFloat.greatestFiniteMagnitude,
            height: CGFloat.greatestFiniteMagnitude
        )
        textView.textContainerInset = NSSize(width: 0, height: 4)
        textView.string = text

        scrollView.hasHorizontalScroller = !wordWrap
        scrollView.documentView = textView

        return textView
    }

    private func configureEditorCallbacks(
        for textView: GoToDefinitionTextView,
        coordinator: Coordinator
    ) {
        textView.onGoToDefinition = onGoToDefinition
        textView.onHover = onHover
        textView.onHoverEnd = onHoverEnd
        textView.completionProvider = completionProvider
        textView.setupIntelliSense()
        textView.detailedCompletionProvider = coordinator.getDetailedCompletions
        textView.signatureHelpProvider = coordinator.getSignatureHelp
    }

    private func configureCoordinator(for textView: GoToDefinitionTextView, context: Context) {
        context.coordinator.textView = textView
        context.coordinator.lastKnownText = text
    }

    private func applyInitialTheme(
        to textView: GoToDefinitionTextView,
        coordinator: Coordinator
    ) {
        let savedColorScheme = UserSettings.shared.colorScheme
        let theme = EditorColorScheme(rawValue: savedColorScheme)?.syntaxTheme ?? .default

        coordinator.highlighter = TLASyntaxHighlighter(textView: textView, theme: theme)
        coordinator.highlighter?.treeSitterHighlightProvider = { [weak coordinator] source in
            guard let coordinator,
                  source == coordinator.cachedHighlightText else {
                return []
            }
            return coordinator.cachedHighlightTokens
        }
        coordinator.updateTreeSitterHighlights(for: textView.string)
        coordinator.highlighter?.highlightImmediately()
        textView.backgroundColor = theme.background
        textView.insertionPointColor = theme.cursor
    }

    private func configureDiagnostics(
        for textView: GoToDefinitionTextView,
        coordinator: Coordinator
    ) {
        coordinator.diagnosticHighlighter = DiagnosticHighlighter(textView: textView)
        if !diagnostics.isEmpty {
            coordinator.diagnosticHighlighter?.updateDiagnostics(diagnostics, in: text)
            coordinator.lastKnownDiagnostics = diagnostics
        }
    }

    private func configureEditorEnhancements(
        for textView: GoToDefinitionTextView,
        coordinator: Coordinator
    ) {
        let highlightCurrentLine = UserSettings.shared.highlightCurrentLine
        let matchBrackets = UserSettings.shared.matchBrackets
        coordinator.editorEnhancements = EditorEnhancements(
            textView: textView,
            enableCurrentLineHighlight: highlightCurrentLine,
            enableBracketMatching: matchBrackets
        )
    }

    private func configureFolding(
        for textView: GoToDefinitionTextView,
        coordinator: Coordinator
    ) -> CodeFoldingManager? {
        guard showFoldingGutter else {
            return nil
        }

        let manager = CodeFoldingManager(textView: textView)
        textView.foldingManager = manager
        coordinator.foldingManager = manager

        Task { @MainActor in
            manager.updateFoldingRanges(from: text)
        }

        return manager
    }

    private func connectFindReplace(to textView: GoToDefinitionTextView) {
        Task { @MainActor in
            findReplaceManager.textView = textView
        }
    }

    private func installEditorObservers(for textView: NSTextView, coordinator: Coordinator) {
        NotificationCenter.default.addObserver(
            coordinator,
            selector: #selector(Coordinator.textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )
        NotificationCenter.default.addObserver(
            coordinator,
            selector: #selector(Coordinator.textViewDidChangeSelection(_:)),
            name: NSTextView.didChangeSelectionNotification,
            object: textView
        )

        if let contentView = textView.enclosingScrollView?.contentView {
            contentView.postsBoundsChangedNotifications = true
            NotificationCenter.default.addObserver(
                coordinator,
                selector: #selector(Coordinator.scrollViewDidScroll(_:)),
                name: NSView.boundsDidChangeNotification,
                object: contentView
            )
        }
    }

    private func focus(_ textView: NSTextView) {
        DispatchQueue.main.async {
            textView.window?.makeFirstResponder(textView)
        }
    }

    func makeNSView(context: Context) -> EditorContainerView {
        let scrollView = makeEditorScrollView()
        let textView = makeEditorTextView(in: scrollView)

        configureEditorCallbacks(for: textView, coordinator: context.coordinator)
        configureCoordinator(for: textView, context: context)
        connectFindReplace(to: textView)
        applyInitialTheme(to: textView, coordinator: context.coordinator)
        configureDiagnostics(for: textView, coordinator: context.coordinator)
        configureEditorEnhancements(for: textView, coordinator: context.coordinator)
        let foldingManager = configureFolding(for: textView, coordinator: context.coordinator)
        installEditorObservers(for: textView, coordinator: context.coordinator)

        // Create container with line numbers, folding gutter, and editor
        let containerView = EditorContainerView(
            scrollView: scrollView,
            textView: textView,
            showLineNumbers: configuration.showLineNumbers,
            foldingManager: foldingManager
        )

        focus(textView)
        return containerView
    }

    private func syncEditorConfiguration(for textView: NSTextView) {
        if let textView = textView as? GoToDefinitionTextView {
            textView.editorConfiguration = configuration
        } else if textView.font != configuration.font {
            textView.font = configuration.font
        }

        if findReplaceManager.textView !== textView {
            Task { @MainActor in
                findReplaceManager.textView = textView
            }
        }
    }

    private func syncTextIfNeeded(
        for textView: NSTextView,
        in containerView: EditorContainerView,
        coordinator: Coordinator
    ) {
        guard coordinator.lastKnownText != text else {
            return
        }

        coordinator.lastKnownText = text

        NotificationCenter.default.removeObserver(
            coordinator,
            name: NSText.didChangeNotification,
            object: textView
        )

        textView.string = text
        (textView as? GoToDefinitionTextView)?.applyEditorConfiguration()
        containerView.refreshTextDependentGutters()

        NotificationCenter.default.addObserver(
            coordinator,
            selector: #selector(Coordinator.textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )

        coordinator.updateTreeSitterHighlights(for: text)
        coordinator.highlighter?.highlightImmediately()

        if !coordinator.lastKnownDiagnostics.isEmpty {
            coordinator.diagnosticHighlighter?.updateDiagnostics(
                coordinator.lastKnownDiagnostics,
                in: text
            )
        }
    }

    private func syncDiagnostics(
        for textView: NSTextView,
        coordinator: Coordinator
    ) {
        guard !diagnosticsEqual(coordinator.lastKnownDiagnostics, diagnostics) else {
            return
        }

        coordinator.lastKnownDiagnostics = diagnostics
        coordinator.diagnosticHighlighter?.updateDiagnostics(diagnostics, in: textView.string)
    }

    private func syncProofAnnotations(for containerView: EditorContainerView) {
        guard let proofGutter = containerView.proofGutterView,
              proofGutter.annotations != proofAnnotations else {
            return
        }

        proofGutter.annotations = proofAnnotations
        containerView.needsLayout = true
    }

    private func syncSelectionIfNeeded(for textView: NSTextView, coordinator: Coordinator) {
        guard coordinator.lastKnownSelection != selectedRange else {
            return
        }

        coordinator.lastKnownSelection = selectedRange

        let maxLocation = (textView.string as NSString).length
        let validLocation = min(selectedRange.location, maxLocation)
        let validLength = min(selectedRange.length, maxLocation - validLocation)
        let validRange = NSRange(location: validLocation, length: validLength)

        textView.setSelectedRange(validRange)
        textView.scrollRangeToVisible(validRange)
    }

    func updateNSView(_ containerView: EditorContainerView, context: Context) {
        guard let textView = containerView.scrollView.documentView as? NSTextView else { return }

        syncEditorConfiguration(for: textView)
        containerView.setLineNumbersVisible(configuration.showLineNumbers)
        syncTextIfNeeded(for: textView, in: containerView, coordinator: context.coordinator)
        syncDiagnostics(for: textView, coordinator: context.coordinator)
        syncProofAnnotations(for: containerView)
        syncSelectionIfNeeded(for: textView, coordinator: context.coordinator)
    }

    private func diagnosticsEqual(_ lhs: [TLADiagnostic], _ rhs: [TLADiagnostic]) -> Bool {
        lhs == rhs
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
        private var highlightTask: Task<Void, Never>?

        /// Cached tree-sitter highlight tokens as absolute NSRange values.
        var cachedHighlightTokens: [(NSRange, String)] = []
        var cachedHighlightText: String = ""
        var cachedParseResult: TLAParseResult?

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
            highlightTask?.cancel()
            NotificationCenter.default.removeObserver(self)
            // Remove notification observers
            for observer in notificationObservers {
                NotificationCenter.default.removeObserver(observer)
            }
        }

        private func handles(_ notification: Notification) -> Bool {
            guard let target = parent.notificationTarget else {
                return notification.object == nil
            }
            guard let object = notification.object as AnyObject? else {
                return false
            }
            return object === target
        }

        private func setupFoldNotifications() {
            let foldAllObserver = NotificationCenter.default.addObserver(
                forName: .foldAll,
                object: nil,
                queue: .main
            ) { [weak self] notification in
                guard let self, self.handles(notification) else { return }
                self.foldingManager?.foldAll()
                self.highlighter?.highlightImmediately()
            }
            notificationObservers.append(foldAllObserver)

            let unfoldAllObserver = NotificationCenter.default.addObserver(
                forName: .unfoldAll,
                object: nil,
                queue: .main
            ) { [weak self] notification in
                guard let self, self.handles(notification) else { return }
                self.foldingManager?.unfoldAll()
                self.highlighter?.highlightImmediately()
            }
            notificationObservers.append(unfoldAllObserver)

            let toggleFoldObserver = NotificationCenter.default.addObserver(
                forName: .toggleFold,
                object: nil,
                queue: .main
            ) { [weak self] notification in
                guard let self, self.handles(notification) else { return }
                self.toggleFoldAtCursor()
            }
            notificationObservers.append(toggleFoldObserver)
        }

        private func toggleFoldAtCursor() {
            guard let textView = textView,
                  let foldingManager = foldingManager else { return }

            let cursorLocation = textView.selectedRange().location
            let text = textView.string
            let currentLine = TextCoordinateMapper.lineAndColumn(
                forUTF16Offset: cursorLocation,
                in: text
            ).line

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

        @objc public func textViewDidChangeSelection(_ notification: Notification) {
            guard let textView = textView, !isUpdating else { return }

            let newSelection = textView.selectedRange()
            guard newSelection != lastKnownSelection else { return }

            lastKnownSelection = newSelection
            parent.selectedRange = newSelection
            parent.onSelectionChange?(newSelection)
        }

        @objc public func textDidChange(_ notification: Notification) {
            guard let textView = textView else { return }

            let newText = textView.string
            lastKnownText = newText
            lastKnownSelection = textView.selectedRange()

            isUpdating = true
            parent.text = newText
            parent.selectedRange = lastKnownSelection
            parent.onSelectionChange?(lastKnownSelection)
            parent.onTextChange?(newText)
            isUpdating = false

            updateTreeSitterHighlights(for: newText)
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
                try? await Task.sleep(nanoseconds: 50_000_000) // 50ms
                guard !Task.isCancelled else { return }
                self.foldingManager?.updateFoldingRanges(from: newText)
            }
        }

        @objc func scrollViewDidScroll(_ notification: Notification) {
            gutterView?.needsDisplay = true
            highlighter?.scrollPositionChanged()
        }

        /// Asynchronously compute tree-sitter highlights and cache absolute AppKit ranges.
        func updateTreeSitterHighlights(for text: String) {
            highlightTask?.cancel()
            highlightTask = Task { @MainActor [weak self] in
                guard let self, !Task.isCancelled else { return }

                do {
                    let parseResult = try await TLACoreWrapper.shared.parse(text, previous: self.cachedParseResult)
                    guard !Task.isCancelled else { return }

                    let tokens = await TLACoreWrapper.shared.getAllHighlights(from: parseResult)
                    guard !Task.isCancelled else { return }

                    self.cachedParseResult = parseResult
                    self.cachedHighlightTokens = Self.convertHighlightTokens(tokens, in: text)
                    self.cachedHighlightText = text
                    self.highlighter?.highlightImmediately()
                } catch {
                    self.cachedHighlightTokens = []
                    self.cachedHighlightText = ""
                }
            }
        }

        private static func convertHighlightTokens(
            _ tokens: [TLAHighlightToken],
            in text: String
        ) -> [(NSRange, String)] {
            let utf8 = text.utf8
            let nsText = text as NSString

            var lineStartsUTF8: [Int] = [0]
            var lineStartsUTF16: [Int] = [0]
            var utf16Offset = 0

            for (byteIndex, byte) in utf8.enumerated() {
                if byte == 0x0A {
                    utf16Offset += 1
                    lineStartsUTF8.append(byteIndex + 1)
                    lineStartsUTF16.append(utf16Offset)
                } else if byte & 0xC0 != 0x80 {
                    utf16Offset += byte < 0xF0 ? 1 : 2
                }
            }

            func utf16OffsetForTreeSitterPoint(line: Int, byteColumn: Int) -> Int? {
                guard line >= 0,
                      line < lineStartsUTF8.count,
                      line < lineStartsUTF16.count else {
                    return nil
                }

                let lineByteStart = lineStartsUTF8[line]
                let lineUTF16Start = lineStartsUTF16[line]
                guard let startIndex = utf8.index(
                    utf8.startIndex,
                    offsetBy: lineByteStart,
                    limitedBy: utf8.endIndex
                ) else {
                    return nil
                }

                var bytesConsumed = 0
                var utf16Count = 0
                var index = startIndex

                while bytesConsumed < byteColumn && index < utf8.endIndex {
                    let byte = utf8[index]
                    if byte == 0x0A { break }

                    let characterByteLength: Int
                    let characterUTF16Length: Int
                    if byte < 0x80 {
                        characterByteLength = 1
                        characterUTF16Length = 1
                    } else if byte < 0xE0 {
                        characterByteLength = 2
                        characterUTF16Length = 1
                    } else if byte < 0xF0 {
                        characterByteLength = 3
                        characterUTF16Length = 1
                    } else {
                        characterByteLength = 4
                        characterUTF16Length = 2
                    }

                    bytesConsumed += characterByteLength
                    utf16Count += characterUTF16Length
                    index = utf8.index(index, offsetBy: characterByteLength, limitedBy: utf8.endIndex) ?? utf8.endIndex
                }

                return lineUTF16Start + utf16Count
            }

            var converted: [(NSRange, String)] = []
            converted.reserveCapacity(tokens.count)

            for token in tokens {
                let startLine = Int(token.range.start.line)
                let startColumn = Int(token.range.start.column)
                let endLine = Int(token.range.end.line)
                let endColumn = Int(token.range.end.column)

                guard let start = utf16OffsetForTreeSitterPoint(line: startLine, byteColumn: startColumn),
                      let end = utf16OffsetForTreeSitterPoint(line: endLine, byteColumn: endColumn),
                      start <= nsText.length,
                      end <= nsText.length,
                      end > start else {
                    continue
                }

                converted.append((
                    NSRange(location: start, length: end - start),
                    token.tokenType
                ))
            }

            return converted
        }

        // MARK: - IntelliSense Support

        /// Provide detailed completions for the current position
        @MainActor
        func getDetailedCompletions(at position: Int) async -> [TLADetailedCompletionItem] {
            guard let textView = textView else { return [] }
            let text = textView.string
            let tlaPosition = TextCoordinateMapper.position(forUTF16Offset: position, in: text)

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
            let tlaPosition = TextCoordinateMapper.position(forUTF16Offset: position, in: text)

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

    func insertSpacesForTabs(_ insertSpaces: Bool) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.configuration.insertSpacesForTabs = insertSpaces
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

    func proofAnnotations(_ annotations: [ProofAnnotation]) -> TLAEditorViewWithFindReplace {
        var copy = self
        copy.proofAnnotations = annotations
        return copy
    }
}

// HoverPopover is defined in Document/HoverPopover.swift
// ResizableDivider is defined in Views/EditorComponents.swift

// MARK: - Inspector Sidebar

// InspectorSidebar is now defined in Views/Sidebar/InspectorViews.swift as EnhancedInspectorSidebar
typealias InspectorSidebar = EnhancedInspectorSidebar
