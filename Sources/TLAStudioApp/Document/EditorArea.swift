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
            // Use the scroll-adjusted visible-area point passed from the text view
            hoverPosition = screenPoint
            showHover = true
        } else {
            showHover = false
        }
    }
}
