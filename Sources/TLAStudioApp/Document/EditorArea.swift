import SwiftUI

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

    // Editor settings from UserSettings (live-updating)
    @AppStorage(UserSettings.Keys.fontName) private var fontName = "SF Mono"
    @AppStorage(UserSettings.Keys.fontSize) private var fontSize: Double = 13
    @AppStorage(UserSettings.Keys.tabWidth) private var tabWidth = 4
    @AppStorage(UserSettings.Keys.lineHeight) private var lineHeightMultiplier: Double = 1.4
    @AppStorage(UserSettings.Keys.showLineNumbers) private var showLineNumbers = true
    @AppStorage(UserSettings.Keys.showMinimap) private var showMinimap = false
    @AppStorage(UserSettings.Keys.insertSpacesForTabs) private var insertSpacesForTabs = true

    /// Resolved font from settings with fallback
    private var resolvedFont: NSFont {
        if let font = NSFont(name: fontName, size: CGFloat(fontSize)) {
            return font
        }
        return NSFont(name: "Menlo", size: CGFloat(fontSize))
            ?? .monospacedSystemFont(ofSize: CGFloat(fontSize), weight: .regular)
    }

    /// Total line count for Go to Line dialog
    private var lineCount: Int {
        document.totalLineCount
    }

    /// Current cursor position based on selection.
    private var cursorPosition: (line: Int, column: Int) {
        let position = document.lineAndColumn(for: document.selectedRange.location)
        return (position.line + 1, position.column + 1)
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

            if PlusCalSourceMapping.ranges(in: document.content) != nil {
                PlusCalNavigationBar(document: document)
            }

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
                        notificationTarget: document,
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
                    .editorFont(resolvedFont)
                    .tabWidth(tabWidth)
                    .insertSpacesForTabs(insertSpacesForTabs)
                    .lineHeight(CGFloat(lineHeightMultiplier))
                    .showLineNumbers(showLineNumbers)
                    .proofAnnotations(document.proofAnnotationManager.annotations)
                }
                .overlay(alignment: .topLeading) {
                    if showHover, let info = hoverInfo {
                        HoverPopover(info: info)
                            .offset(x: hoverPosition.x, y: hoverPosition.y + 20)
                    }
                }

                // Minimap (shown based on setting)
                if showMinimap {
                    MinimapContainer(
                        content: document.content,
                        visibleRange: document.selectedRange,
                        diagnostics: document.diagnostics,
                        onNavigate: { offset in
                            document.selectedRange = NSRange(location: offset, length: 0)
                        }
                    )
                }
            }

            Divider()

            // Status bar
            StatusBar(
                document: document,
                cursorLine: cursorPosition.line,
                cursorColumn: cursorPosition.column
            )

            // Bottom panel grows when the divider is dragged up (negative translation),
            // so subtract translation from the anchor. All drag state lives inside
            // `ResizableDivider`'s @GestureState, which auto-resets between drags —
            // previous iterations got stuck after the first adjustment because
            // parent-owned state didn't always get reset on gesture interruption.
            ResizableDivider(
                current: bottomPanelHeight,
                resolveTarget: { anchor, translation in
                    min(500, max(80, anchor - translation))
                },
                apply: { target in
                    guard target != bottomPanelHeight else { return }
                    var transaction = Transaction()
                    transaction.disablesAnimations = true
                    withTransaction(transaction) {
                        bottomPanelHeight = target
                    }
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
        .onReceive(NotificationCenter.default.publisher(for: .goToLine)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            showGoToLineSheet = true
        }
        .onReceive(NotificationCenter.default.publisher(for: .showFindReplace)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            let showReplace = (notification.userInfo?["showReplace"] as? Bool) ?? false
            findReplaceManager.showReplace = showReplace
            findReplaceManager.isVisible = true
        }
        .onReceive(NotificationCenter.default.publisher(for: .hideFindReplace)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            findReplaceManager.isVisible = false
        }
        .onReceive(NotificationCenter.default.publisher(for: .toggleFindReplace)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            findReplaceManager.isVisible.toggle()
        }
        .onReceive(NotificationCenter.default.publisher(for: .findNext)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            findReplaceManager.findNext()
        }
        .onReceive(NotificationCenter.default.publisher(for: .findPrevious)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            findReplaceManager.findPrevious()
        }
        .onReceive(NotificationCenter.default.publisher(for: .useSelectionForFind)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            // Get selected text from document and use it for find
            let content = document.content as NSString
            let range = document.selectedRange
            if range.length > 0 && range.location + range.length <= content.length {
                let selectedText = content.substring(with: range)
                findReplaceManager.searchQuery = selectedText
                findReplaceManager.isVisible = true
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .translatePlusCal)) { notification in
            if notification.object == nil || (notification.object as? TLADocument) === document {
                document.translatePlusCal()
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .goToPlusCalAlgorithm)) { notification in
            if notification.object == nil || (notification.object as? TLADocument) === document {
                _ = document.goToPlusCalAlgorithm()
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .goToPlusCalTranslation)) { notification in
            if notification.object == nil || (notification.object as? TLADocument) === document {
                _ = document.goToPlusCalTranslation()
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .goToDefinition)) { notification in
            if notification.object == nil || (notification.object as? TLADocument) === document {
                _ = document.goToDefinition(at: document.selectedRange.location)
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .findReferences)) { notification in
            guard notification.object == nil || (notification.object as? TLADocument) === document else { return }
            findReferences()
        }
    }

    // MARK: - Navigation Helpers

    private func navigateToLine(_ lineNumber: Int) {
        guard lineNumber >= 1 && lineNumber <= document.totalLineCount else { return }
        let offset = document.offset(forLine: lineNumber - 1, column: 0)
        document.selectedRange = NSRange(location: offset, length: 0)
    }

    private func navigateToSymbol(_ symbol: TLASymbol) {
        let offset = document.offset(
            forLine: Int(symbol.range.start.line),
            column: Int(symbol.range.start.column)
        )
        document.selectedRange = NSRange(location: offset, length: 0)
    }

    private func updateCurrentSymbol(at characterOffset: Int) {
        let line = document.lineAndColumn(for: characterOffset).line
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
            // Use the scroll-adjusted visible-area point passed from the text view
            hoverPosition = screenPoint
            showHover = true
        } else {
            showHover = false
        }
    }

    private func findReferences() {
        let (line, column) = document.lineAndColumn(for: document.selectedRange.location)
        let position = TLAPosition(line: UInt32(line), column: UInt32(column))

        guard let word = TLACoreWrapper.shared.wordAt(position: position, in: document.content),
              !word.isEmpty else {
            return
        }

        findReplaceManager.searchQuery = word
        findReplaceManager.isWholeWord = true
        findReplaceManager.showReplace = false
        findReplaceManager.isVisible = true
        findReplaceManager.findAll()
    }
}

private struct PlusCalNavigationBar: View {
    @ObservedObject var document: TLADocument

    var body: some View {
        HStack(spacing: 10) {
            Label("PlusCal", systemImage: "arrow.triangle.branch")
                .font(.system(size: 12, weight: .medium))

            if let currentRegionTitle {
                Text(currentRegionTitle)
                    .font(.caption)
                    .foregroundColor(.secondary)
            } else {
                Text("Jump between the algorithm and generated translation.")
                    .font(.caption)
                    .foregroundColor(.secondary)
            }

            Spacer()

            Button("Algorithm") {
                _ = document.goToPlusCalAlgorithm()
            }
            .buttonStyle(.bordered)

            Button("Translation") {
                _ = document.goToPlusCalTranslation()
            }
            .buttonStyle(.bordered)
            .disabled(PlusCalSourceMapping.range(for: .translation, in: document.content) == nil)

            Button {
                document.translatePlusCal()
            } label: {
                Label(
                    document.isTranslatingPlusCal ? "Translating…" : "Translate",
                    systemImage: "arrow.triangle.2.circlepath"
                )
            }
            .buttonStyle(.borderedProminent)
            .disabled(document.isTranslatingPlusCal)
        }
        .padding(.horizontal, 10)
        .padding(.vertical, 6)
        .background(Color(NSColor.controlBackgroundColor))
    }

    private var currentRegionTitle: String? {
        guard let ranges = PlusCalSourceMapping.ranges(in: document.content) else {
            return nil
        }

        let location = document.selectedRange.location
        if ranges.algorithm.contains(location) {
            return "In algorithm"
        }
        if let translationRange = ranges.translation, translationRange.contains(location) {
            return "In translation"
        }
        return nil
    }
}
