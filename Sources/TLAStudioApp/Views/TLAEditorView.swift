import SwiftUI
import SourceEditor

// MARK: - TLAEditorView

/// SwiftUI wrapper for TLASourceEditor (NSTextView-based)
public struct TLAEditorView: NSViewRepresentable {

    // MARK: - Bindings

    @Binding var text: String
    @Binding var selectedRange: NSRange

    // MARK: - Configuration

    var configuration: TLASourceEditor.Configuration
    var onTextChange: ((String) -> Void)?
    var onSelectionChange: ((NSRange) -> Void)?
    var onGoToDefinition: ((Int) -> Bool)?
    var onHover: ((Int, NSPoint) -> Void)?
    var onHoverEnd: (() -> Void)?
    var completionProvider: ((Int) -> [String])?
    var showFoldingGutter: Bool

    // MARK: - Initialization

    public init(
        text: Binding<String>,
        selectedRange: Binding<NSRange> = .constant(NSRange(location: 0, length: 0)),
        configuration: TLASourceEditor.Configuration = .init(),
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
        self.configuration = configuration
        self.onTextChange = onTextChange
        self.onSelectionChange = onSelectionChange
        self.onGoToDefinition = onGoToDefinition
        self.onHover = onHover
        self.onHoverEnd = onHoverEnd
        self.completionProvider = completionProvider
        self.showFoldingGutter = showFoldingGutter
    }

    // MARK: - NSViewRepresentable

    public func makeNSView(context: Context) -> NSScrollView {
        // Create scroll view
        let scrollView = NSScrollView()
        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = false
        scrollView.autohidesScrollers = true
        scrollView.borderType = .noBorder

        // Create custom text view with go-to-definition support
        let contentSize = scrollView.contentSize

        // Use full width - ruler view manages its own space separately
        let textContainer = NSTextContainer(containerSize: NSSize(width: contentSize.width, height: CGFloat.greatestFiniteMagnitude))
        textContainer.widthTracksTextView = true

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
        textView.isHorizontallyResizable = false
        textView.autoresizingMask = [.width]
        textView.minSize = NSSize(width: 0, height: contentSize.height)
        textView.maxSize = NSSize(width: CGFloat.greatestFiniteMagnitude, height: CGFloat.greatestFiniteMagnitude)

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

        // Set up line numbers
        if configuration.showLineNumbers {
            scrollView.hasVerticalRuler = true
            let rulerView = LineNumberRulerView(textView: textView, scrollView: scrollView)
            scrollView.verticalRulerView = rulerView
            scrollView.rulersVisible = true
        }

        // Store reference and initial text
        context.coordinator.textView = textView
        context.coordinator.lastKnownText = text

        // Create highlighter for this text view
        context.coordinator.highlighter = TLASyntaxHighlighter(textView: textView, theme: configuration.theme)

        // Wire tree-sitter highlight provider
        let coordinator = context.coordinator
        coordinator.highlighter?.treeSitterHighlightProvider = { [weak coordinator] text in
            guard let coordinator = coordinator else { return [] }
            // Return cached tokens if text matches
            if text == coordinator.cachedHighlightText {
                return coordinator.cachedHighlightTokens
            }
            return []
        }

        // Kick off initial tree-sitter parse
        context.coordinator.updateTreeSitterHighlights(for: text)

        context.coordinator.highlighter?.highlightImmediately()

        // Set up folding if enabled
        if showFoldingGutter {
            let foldingManager = CodeFoldingManager(textView: textView)
            textView.foldingManager = foldingManager
            context.coordinator.foldingManager = foldingManager

            // Update folding ranges
            Task { @MainActor in
                foldingManager.updateFoldingRanges(from: text)
            }

            // Note: Folding gutter UI disabled for now - folding still works via menu/keyboard
            // The NSRulerView approach was causing text rendering issues
        }

        // Listen for text changes
        NotificationCenter.default.addObserver(
            context.coordinator,
            selector: #selector(Coordinator.textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )

        // Make first responder
        DispatchQueue.main.async {
            textView.window?.makeFirstResponder(textView)
        }

        return scrollView
    }

    public func updateNSView(_ scrollView: NSScrollView, context: Context) {
        guard let textView = scrollView.documentView as? NSTextView else { return }

        // Update font if changed
        if textView.font != configuration.font {
            textView.font = configuration.font
        }

        // Only update if the binding changed from OUTSIDE (not from our own editing)
        // If lastKnownText matches text, the change came from the user typing
        if context.coordinator.lastKnownText != text {
            // External change - update the text view
            context.coordinator.lastKnownText = text

            // Disable notifications temporarily to prevent loop
            NotificationCenter.default.removeObserver(
                context.coordinator,
                name: NSText.didChangeNotification,
                object: textView
            )

            textView.string = text

            // Re-add notification observer
            NotificationCenter.default.addObserver(
                context.coordinator,
                selector: #selector(Coordinator.textDidChange(_:)),
                name: NSText.didChangeNotification,
                object: textView
            )

            // Highlight the external change immediately (no debounce needed)
            context.coordinator.highlighter?.highlightImmediately()
        }

        // Handle selection changes from external sources (e.g., symbol outline navigation)
        if context.coordinator.lastKnownSelection != selectedRange {
            context.coordinator.lastKnownSelection = selectedRange

            // Ensure the range is valid (clamp negative values and bounds check)
            let maxLocation = textView.string.count
            let clampedLocation = max(0, selectedRange.location)  // Clamp negative to 0
            let validLocation = min(clampedLocation, maxLocation)
            let validLength = max(0, min(selectedRange.length, maxLocation - validLocation))
            let validRange = NSRange(location: validLocation, length: validLength)

            // Set selection and scroll to it
            textView.setSelectedRange(validRange)
            textView.scrollRangeToVisible(validRange)
        }
    }

    public func makeCoordinator() -> Coordinator {
        Coordinator(self)
    }

    // MARK: - Coordinator

    public class Coordinator: NSObject, NSTextViewDelegate {
        var parent: TLAEditorView
        weak var textView: NSTextView?
        var highlighter: TLASyntaxHighlighter?
        var foldingManager: CodeFoldingManager?
        weak var gutterView: FoldingGutterView?
        var isUpdating = false
        var lastKnownText: String = ""
        var lastKnownSelection: NSRange = NSRange(location: 0, length: 0)
        private var notificationObservers: [NSObjectProtocol] = []

        /// Cached tree-sitter highlight tokens as (NSRange, captureName) tuples
        var cachedHighlightTokens: [(NSRange, String)] = []
        /// Text that was used to compute the cached tokens
        var cachedHighlightText: String = ""
        /// Task for async highlight computation
        private var highlightTask: Task<Void, Never>?

        init(_ parent: TLAEditorView) {
            self.parent = parent
            super.init()
            setupFoldNotifications()
        }

        deinit {
            // Remove block-based observers
            for observer in notificationObservers {
                NotificationCenter.default.removeObserver(observer)
            }
            // Remove selector-based observer (self was registered in makeNSView)
            NotificationCenter.default.removeObserver(self)
        }

        private func setupFoldNotifications() {
            // Fold All
            let foldAllObserver = NotificationCenter.default.addObserver(
                forName: .foldAll,
                object: nil,
                queue: .main
            ) { [weak self] _ in
                self?.foldingManager?.foldAll()
                self?.highlighter?.highlightImmediately()
            }
            notificationObservers.append(foldAllObserver)

            // Unfold All
            let unfoldAllObserver = NotificationCenter.default.addObserver(
                forName: .unfoldAll,
                object: nil,
                queue: .main
            ) { [weak self] _ in
                self?.foldingManager?.unfoldAll()
                self?.highlighter?.highlightImmediately()
            }
            notificationObservers.append(unfoldAllObserver)

            // Toggle Fold at cursor
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

            // Get current cursor line
            let cursorLocation = textView.selectedRange().location
            let text = textView.string
            let lines = text.prefix(cursorLocation).components(separatedBy: "\n")
            let currentLine = lines.count - 1

            // Find if there's a foldable region at or containing this line
            if let range = foldingManager.foldingRange(at: currentLine) {
                foldingManager.toggleFold(at: range.startLine)
            } else {
                // Check if we're inside a foldable region
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
            if newSelection != lastKnownSelection {
                lastKnownSelection = newSelection
                parent.selectedRange = newSelection
            }
        }

        @objc public func textDidChange(_ notification: Notification) {
            guard let textView = textView else { return }

            let newText = textView.string

            // Update our tracking
            lastKnownText = newText
            lastKnownSelection = textView.selectedRange()

            // Update parent binding
            isUpdating = true
            parent.text = newText
            parent.selectedRange = lastKnownSelection
            parent.onTextChange?(newText)
            isUpdating = false

            // Update tree-sitter highlights asynchronously.
            // The completion callback in updateTreeSitterHighlights will schedule highlighting.
            // If tree-sitter tokens are already cached for this text, schedule immediately.
            updateTreeSitterHighlights(for: newText)

            // Only schedule immediate regex highlighting if no tree-sitter parse is in-flight
            // (i.e., we already have cached tokens for this exact text, or tree-sitter is unavailable).
            // Otherwise, wait for the async parse to complete to avoid double-highlight flicker.
            if cachedHighlightText == newText {
                highlighter?.scheduleHighlighting()
            }

            // Update folding ranges
            Task { @MainActor in
                self.foldingManager?.updateFoldingRanges(from: newText)
            }
        }

        /// Asynchronously compute tree-sitter highlights and cache them
        func updateTreeSitterHighlights(for text: String) {
            highlightTask?.cancel()
            highlightTask = Task { @MainActor [weak self] in
                guard let self = self, !Task.isCancelled else { return }

                do {
                    let parseResult = try await TLACoreWrapper.shared.parse(text)
                    guard !Task.isCancelled else { return }

                    let tokens = await TLACoreWrapper.shared.getAllHighlights(from: parseResult)
                    guard !Task.isCancelled else { return }

                    // Build line offset indices for both UTF-8 (for tree-sitter) and UTF-16 (for NSString/NSRange).
                    // Tree-sitter columns are byte offsets within the line (UTF-8), but NSRange uses UTF-16 code units.
                    let utf8 = text.utf8
                    let nsText = text as NSString

                    // lineStartsUTF8[i] = byte offset of the start of line i in the UTF-8 view
                    // lineStartsUTF16[i] = UTF-16 offset of the start of line i in the NSString
                    var lineStartsUTF8: [Int] = [0]
                    var lineStartsUTF16: [Int] = [0]
                    var utf16Offset = 0
                    for (byteIdx, byte) in utf8.enumerated() {
                        if byte == 0x0A {  // newline
                            utf16Offset += 1
                            lineStartsUTF8.append(byteIdx + 1)
                            lineStartsUTF16.append(utf16Offset)
                        } else {
                            // Count UTF-16 code units for this byte:
                            // In UTF-8: leading bytes (0xxxxxxx, 110xxxxx, 1110xxxx, 11110xxx) start a character;
                            // continuation bytes (10xxxxxx) do not.
                            if byte & 0xC0 != 0x80 {
                                // This is a leading byte - determine UTF-16 size
                                if byte < 0x80 {
                                    utf16Offset += 1 // ASCII: 1 UTF-16 code unit
                                } else if byte < 0xE0 {
                                    utf16Offset += 1 // 2-byte UTF-8: 1 UTF-16 code unit
                                } else if byte < 0xF0 {
                                    utf16Offset += 1 // 3-byte UTF-8: 1 UTF-16 code unit
                                } else {
                                    utf16Offset += 2 // 4-byte UTF-8: 2 UTF-16 code units (surrogate pair)
                                }
                            }
                            // continuation bytes don't add to UTF-16 offset
                        }
                    }

                    /// Convert a tree-sitter Point (line + byte column) to a UTF-16 offset
                    func tsPointToUTF16(line: Int, byteCol: Int) -> Int? {
                        guard line < lineStartsUTF8.count, line < lineStartsUTF16.count else { return nil }
                        let lineByteStart = lineStartsUTF8[line]
                        let lineUTF16Start = lineStartsUTF16[line]

                        // Walk from line start, counting UTF-16 code units until we've consumed byteCol bytes
                        var bytesConsumed = 0
                        var utf16Count = 0
                        let startIdx = utf8.index(utf8.startIndex, offsetBy: lineByteStart, limitedBy: utf8.endIndex) ?? utf8.endIndex

                        var idx = startIdx
                        while bytesConsumed < byteCol && idx < utf8.endIndex {
                            let byte = utf8[idx]
                            if byte == 0x0A { break } // Don't cross line boundary
                            let charByteLen: Int
                            let charUTF16Len: Int
                            if byte < 0x80 {
                                charByteLen = 1; charUTF16Len = 1
                            } else if byte < 0xE0 {
                                charByteLen = 2; charUTF16Len = 1
                            } else if byte < 0xF0 {
                                charByteLen = 3; charUTF16Len = 1
                            } else {
                                charByteLen = 4; charUTF16Len = 2
                            }
                            bytesConsumed += charByteLen
                            utf16Count += charUTF16Len
                            idx = utf8.index(idx, offsetBy: charByteLen, limitedBy: utf8.endIndex) ?? utf8.endIndex
                        }
                        return lineUTF16Start + utf16Count
                    }

                    // Convert TLAHighlightTokens (line/col as byte offsets) to (NSRange, String)
                    var converted: [(NSRange, String)] = []
                    converted.reserveCapacity(tokens.count)
                    for token in tokens {
                        let startLine = Int(token.range.start.line)
                        let startCol = Int(token.range.start.column)
                        let endLine = Int(token.range.end.line)
                        let endCol = Int(token.range.end.column)

                        guard let startUTF16 = tsPointToUTF16(line: startLine, byteCol: startCol),
                              let endUTF16 = tsPointToUTF16(line: endLine, byteCol: endCol) else { continue }
                        guard startUTF16 <= nsText.length, endUTF16 <= nsText.length, endUTF16 > startUTF16 else { continue }

                        converted.append((NSRange(location: startUTF16, length: endUTF16 - startUTF16), token.tokenType))
                    }

                    self.cachedHighlightTokens = converted
                    self.cachedHighlightText = text

                    // Re-trigger highlighting now that tree-sitter tokens are available
                    self.highlighter?.scheduleHighlighting()
                } catch {
                    // Parse failed; regex highlighting will be used as fallback
                }
            }
        }

        @objc func scrollViewDidScroll(_ notification: Notification) {
            gutterView?.needsDisplay = true
        }

        // MARK: - IntelliSense

        /// Provide detailed completions for IntelliSense
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

// MARK: - Code Folding Manager

/// Manages code folding state for the editor
class CodeFoldingManager {
    private weak var textView: NSTextView?
    private weak var gutterView: FoldingGutterView?

    private(set) var foldingRanges: [TLAFoldingRange] = []
    private(set) var foldedRanges: Set<Int> = []  // Set of start lines that are folded

    var onFoldingChanged: (() -> Void)?

    init(textView: NSTextView) {
        self.textView = textView
    }

    func setGutterView(_ gutter: FoldingGutterView) {
        self.gutterView = gutter
    }

    /// Update folding ranges from source analysis
    @MainActor
    func updateFoldingRanges(from source: String) {
        foldingRanges = TLACoreWrapper.shared.getFoldingRanges(in: source)
        gutterView?.foldingRanges = foldingRanges
        gutterView?.foldedLines = foldedRanges
        gutterView?.needsDisplay = true
    }

    /// Toggle fold state for a line
    func toggleFold(at line: Int) {
        guard let range = foldingRanges.first(where: { $0.startLine == line }) else {
            return
        }

        if foldedRanges.contains(line) {
            unfold(range: range)
        } else {
            fold(range: range)
        }

        gutterView?.foldedLines = foldedRanges
        gutterView?.needsDisplay = true
        onFoldingChanged?()
    }

    /// Check if a line has a foldable region starting there
    func hasFoldableRegion(at line: Int) -> Bool {
        foldingRanges.contains { $0.startLine == line }
    }

    /// Check if a line is currently folded
    func isFolded(at line: Int) -> Bool {
        foldedRanges.contains(line)
    }

    /// Get the folding range for a line, if any
    func foldingRange(at line: Int) -> TLAFoldingRange? {
        foldingRanges.first { $0.startLine == line }
    }

    private func fold(range: TLAFoldingRange) {
        guard let textView = textView,
              let textStorage = textView.textStorage else {
            return
        }

        let lines = textView.string.components(separatedBy: "\n")

        // Calculate character range to hide (from end of first line to end of last line)
        var startOffset = 0
        for i in 0..<range.startLine {
            startOffset += lines[i].count + 1  // +1 for newline
        }
        startOffset += lines[range.startLine].count  // End of first line

        var endOffset = 0
        for i in 0...min(range.endLine, lines.count - 1) {
            endOffset += lines[i].count + 1
        }
        endOffset -= 1  // Don't include final newline if at end

        let foldRange = NSRange(location: startOffset, length: endOffset - startOffset)

        // Add folded attribute to hide the text
        textStorage.beginEditing()
        textStorage.addAttribute(.font, value: NSFont.systemFont(ofSize: 0.01), range: foldRange)
        textStorage.addAttribute(NSAttributedString.Key("TLAFolded"), value: true, range: foldRange)
        textStorage.endEditing()

        foldedRanges.insert(range.startLine)
    }

    private func unfold(range: TLAFoldingRange) {
        guard let textView = textView,
              let textStorage = textView.textStorage else {
            return
        }

        let lines = textView.string.components(separatedBy: "\n")

        // Calculate character range
        var startOffset = 0
        for i in 0..<range.startLine {
            startOffset += lines[i].count + 1
        }
        startOffset += lines[range.startLine].count

        var endOffset = 0
        for i in 0...min(range.endLine, lines.count - 1) {
            endOffset += lines[i].count + 1
        }
        endOffset -= 1

        let unfoldRange = NSRange(location: startOffset, length: endOffset - startOffset)

        // Remove folded attributes
        textStorage.beginEditing()
        textStorage.removeAttribute(NSAttributedString.Key("TLAFolded"), range: unfoldRange)
        // Restore normal font - the highlighter will re-apply proper styling
        if let font = textView.font {
            textStorage.addAttribute(.font, value: font, range: unfoldRange)
        }
        textStorage.endEditing()

        foldedRanges.remove(range.startLine)
    }

    /// Fold all foldable regions
    func foldAll() {
        for range in foldingRanges where !foldedRanges.contains(range.startLine) {
            fold(range: range)
        }
        gutterView?.foldedLines = foldedRanges
        gutterView?.needsDisplay = true
        onFoldingChanged?()
    }

    /// Unfold all folded regions
    func unfoldAll() {
        for range in foldingRanges where foldedRanges.contains(range.startLine) {
            unfold(range: range)
        }
        gutterView?.foldedLines = foldedRanges
        gutterView?.needsDisplay = true
        onFoldingChanged?()
    }
}

// MARK: - Folding Gutter View

/// A gutter view that displays fold indicators
class FoldingGutterView: NSRulerView {
    weak var editorTextView: NSTextView?

    var foldingRanges: [TLAFoldingRange] = []
    var foldedLines: Set<Int> = []

    var onToggleFold: ((Int) -> Void)?

    private let gutterWidth: CGFloat = 14
    private let indicatorSize: CGFloat = 9

    var textView: NSTextView? {
        get { editorTextView }
        set { editorTextView = newValue }
    }

    override var requiredThickness: CGFloat { gutterWidth }

    override var isFlipped: Bool { true }

    override func draw(_ dirtyRect: NSRect) {
        super.draw(dirtyRect)

        guard let textView = editorTextView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else {
            return
        }

        // Background
        NSColor.textBackgroundColor.setFill()
        dirtyRect.fill()

        // Draw separator line
        NSColor.separatorColor.setStroke()
        let separatorPath = NSBezierPath()
        separatorPath.move(to: NSPoint(x: bounds.width - 0.5, y: dirtyRect.minY))
        separatorPath.line(to: NSPoint(x: bounds.width - 0.5, y: dirtyRect.maxY))
        separatorPath.lineWidth = 1
        separatorPath.stroke()

        // Get visible range
        let visibleRect = textView.visibleRect
        let glyphRange = layoutManager.glyphRange(forBoundingRect: visibleRect, in: textContainer)
        let characterRange = layoutManager.characterRange(forGlyphRange: glyphRange, actualGlyphRange: nil)

        // Calculate visible lines
        let text = textView.string
        let lines = text.components(separatedBy: "\n")

        var charOffset = 0
        var visibleStartLine = 0
        for (i, line) in lines.enumerated() {
            if charOffset >= characterRange.location {
                visibleStartLine = i
                break
            }
            charOffset += line.count + 1
        }

        charOffset = 0
        var visibleEndLine = lines.count - 1
        for (i, line) in lines.enumerated() {
            charOffset += line.count + 1
            if charOffset >= characterRange.location + characterRange.length {
                visibleEndLine = i
                break
            }
        }

        // Draw fold indicators for visible lines
        for range in foldingRanges {
            guard range.startLine >= visibleStartLine - 1 && range.startLine <= visibleEndLine + 1 else {
                continue
            }

            // Get the line rect
            var lineCharOffset = 0
            for i in 0..<range.startLine {
                if i < lines.count {
                    lineCharOffset += lines[i].count + 1
                }
            }

            let lineGlyphRange = layoutManager.glyphRange(forCharacterRange: NSRange(location: lineCharOffset, length: 1), actualCharacterRange: nil)
            var lineRect = layoutManager.boundingRect(forGlyphRange: lineGlyphRange, in: textContainer)
            lineRect.origin.y += textView.textContainerInset.height

            // Draw the fold indicator
            let isFolded = foldedLines.contains(range.startLine)
            drawFoldIndicator(at: lineRect.origin.y, isFolded: isFolded)
        }
    }

    private func drawFoldIndicator(at y: CGFloat, isFolded: Bool) {
        let x = (gutterWidth - indicatorSize) / 2
        let indicatorRect = NSRect(
            x: x,
            y: y + 3,
            width: indicatorSize,
            height: indicatorSize
        )

        // Draw disclosure triangle
        let path = NSBezierPath()

        if isFolded {
            // Right-pointing triangle (collapsed)
            path.move(to: NSPoint(x: indicatorRect.minX + 2, y: indicatorRect.minY + 1))
            path.line(to: NSPoint(x: indicatorRect.maxX - 2, y: indicatorRect.midY))
            path.line(to: NSPoint(x: indicatorRect.minX + 2, y: indicatorRect.maxY - 1))
        } else {
            // Down-pointing triangle (expanded)
            path.move(to: NSPoint(x: indicatorRect.minX + 1, y: indicatorRect.minY + 2))
            path.line(to: NSPoint(x: indicatorRect.maxX - 1, y: indicatorRect.minY + 2))
            path.line(to: NSPoint(x: indicatorRect.midX, y: indicatorRect.maxY - 2))
        }
        path.close()

        NSColor.secondaryLabelColor.setFill()
        path.fill()
    }

    override func mouseDown(with event: NSEvent) {
        let point = convert(event.locationInWindow, from: nil)

        guard let textView = editorTextView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else {
            return
        }

        let text = textView.string
        let lines = text.components(separatedBy: "\n")

        // Find which fold indicator was clicked
        for range in foldingRanges {
            var lineCharOffset = 0
            for i in 0..<range.startLine {
                if i < lines.count {
                    lineCharOffset += lines[i].count + 1
                }
            }

            let lineGlyphRange = layoutManager.glyphRange(forCharacterRange: NSRange(location: lineCharOffset, length: 1), actualCharacterRange: nil)
            var lineRect = layoutManager.boundingRect(forGlyphRange: lineGlyphRange, in: textContainer)
            lineRect.origin.y += textView.textContainerInset.height

            let clickRect = NSRect(x: 0, y: lineRect.origin.y, width: gutterWidth, height: lineRect.height + 4)

            if clickRect.contains(point) {
                onToggleFold?(range.startLine)
                return
            }
        }
    }
}

// MARK: - Go-to-definition Text View

/// Custom NSTextView that handles Cmd+click for go-to-definition, hover, and autocompletion
class GoToDefinitionTextView: NSTextView {
    var onGoToDefinition: ((Int) -> Bool)?
    var onHover: ((Int, NSPoint) -> Void)?
    var onHoverEnd: (() -> Void)?
    var completionProvider: ((Int) -> [String])?
    var detailedCompletionProvider: ((Int) async -> [TLADetailedCompletionItem])?
    var foldingManager: CodeFoldingManager?

    /// Completion controller for IntelliSense
    private(set) var intelliSenseController: CompletionController?

    /// Signature help controller
    private(set) var signatureHelpController: SignatureHelpController?

    /// Provider for signature help
    var signatureHelpProvider: ((Int) async -> TLASignatureHelp?)?

    private var hoverTimer: Timer?
    private var lastHoverIndex: Int = NSNotFound
    private var trackingArea: NSTrackingArea?

    deinit {
        hoverTimer?.invalidate()
        if let area = trackingArea {
            removeTrackingArea(area)
        }
    }

    /// Set up the IntelliSense completion controller
    func setupIntelliSense() {
        intelliSenseController = CompletionController(textView: self)
        intelliSenseController?.completionProvider = { [weak self] position in
            guard let self = self, let provider = self.detailedCompletionProvider else {
                return []
            }
            return await provider(position)
        }

        // Set up signature help
        signatureHelpController = SignatureHelpController(textView: self)
        signatureHelpController?.signatureHelpProvider = { [weak self] position in
            guard let self = self, let provider = self.signatureHelpProvider else {
                return nil
            }
            return await provider(position)
        }
    }

    override func updateTrackingAreas() {
        super.updateTrackingAreas()

        if let existing = trackingArea {
            removeTrackingArea(existing)
        }

        trackingArea = NSTrackingArea(
            rect: bounds,
            options: [.mouseMoved, .activeInKeyWindow, .inVisibleRect],
            owner: self,
            userInfo: nil
        )
        addTrackingArea(trackingArea!)
    }

    override func mouseMoved(with event: NSEvent) {
        super.mouseMoved(with: event)

        let point = convert(event.locationInWindow, from: nil)
        let characterIndex = characterIndexForInsertion(at: point)

        // Only trigger hover if we moved to a different character
        if characterIndex != lastHoverIndex {
            lastHoverIndex = characterIndex
            hoverTimer?.invalidate()

            if characterIndex != NSNotFound {
                // Delay before showing hover
                hoverTimer = Timer.scheduledTimer(withTimeInterval: 0.5, repeats: false) { [weak self] _ in
                    guard let self = self else { return }
                    // Compute scroll-view-visible-relative point for overlay positioning
                    let localPoint = self.convert(event.locationInWindow, from: nil)
                    let scrollOffset = self.enclosingScrollView?.documentVisibleRect.origin ?? .zero
                    let visiblePoint = NSPoint(x: localPoint.x - scrollOffset.x,
                                               y: localPoint.y - scrollOffset.y)
                    self.onHover?(characterIndex, visiblePoint)
                }
            }
        }
    }

    override func mouseExited(with event: NSEvent) {
        super.mouseExited(with: event)
        hoverTimer?.invalidate()
        lastHoverIndex = NSNotFound
        onHoverEnd?()
    }

    override func mouseDown(with event: NSEvent) {
        // Cancel any pending hover
        hoverTimer?.invalidate()
        onHoverEnd?()

        // Check for Cmd+click
        if event.modifierFlags.contains(.command) {
            let point = convert(event.locationInWindow, from: nil)
            let characterIndex = characterIndexForInsertion(at: point)

            if characterIndex != NSNotFound {
                if onGoToDefinition?(characterIndex) == true {
                    return
                }
            }
        }

        super.mouseDown(with: event)
    }

    override func keyDown(with event: NSEvent) {
        // Cancel hover on any key press
        hoverTimer?.invalidate()
        onHoverEnd?()

        // Check for manual completion trigger: Ctrl+Space or Option+Escape
        let keyCode = event.keyCode
        let modifiers = event.modifierFlags.intersection(.deviceIndependentFlagsMask)

        // Ctrl+Space (keyCode 49 is Space)
        if keyCode == 49 && modifiers == .control {
            intelliSenseController?.triggerCompletion()
            return
        }

        // Option+Escape (standard macOS completion shortcut)
        if keyCode == 53 && modifiers == .option {
            intelliSenseController?.triggerCompletion()
            return
        }

        // Handle IntelliSense keyboard events
        if let controller = intelliSenseController, controller.isActive {
            switch keyCode {
            case 53:  // Escape (without modifiers)
                if modifiers.isEmpty && controller.handleEscape() {
                    return
                }
            case 36:  // Return
                if controller.handleReturn() {
                    return
                }
            case 48:  // Tab
                if controller.handleTab() {
                    return
                }
            case 126:  // Up Arrow
                if controller.handleUpArrow() {
                    return
                }
            case 125:  // Down Arrow
                if controller.handleDownArrow() {
                    return
                }
            default:
                break
            }
        }

        super.keyDown(with: event)

        // After inserting a character, check for completion trigger
        if let chars = event.characters, let char = chars.first {
            intelliSenseController?.handleCharacterTyped(char)

            // Handle signature help triggers
            switch char {
            case "(":
                signatureHelpController?.handleOpenParen()
            case ",":
                signatureHelpController?.handleComma()
            case ")":
                signatureHelpController?.handleCloseParen()
            default:
                break
            }
        }

        // Handle backspace
        if event.keyCode == 51 {  // Backspace
            intelliSenseController?.handleBackspace()
        }
    }

    // MARK: - Text Changes

    override func didChangeText() {
        super.didChangeText()
        // Notify controller of cursor changes
        intelliSenseController?.handleCursorMoved()
    }

    // MARK: - Autocompletion (disabled in favor of IntelliSense)

    override func completions(forPartialWordRange charRange: NSRange, indexOfSelectedItem index: UnsafeMutablePointer<Int>) -> [String]? {
        // Return nil to disable built-in completion - we use IntelliSense instead
        return nil
    }

    /// Manually trigger IntelliSense completion
    func triggerCompletion() {
        intelliSenseController?.triggerCompletion()
    }

    /// Dismiss IntelliSense completion
    func dismissCompletion() {
        intelliSenseController?.dismiss()
    }
}

// MARK: - Convenience Initializers

public extension TLAEditorView {

    /// Create an editor with just a text binding
    init(text: Binding<String>) {
        self.init(
            text: text,
            selectedRange: .constant(NSRange(location: 0, length: 0)),
            configuration: .init(),
            showFoldingGutter: true
        )
    }

    /// Create an editor with text binding and custom font
    init(text: Binding<String>, font: NSFont) {
        var config = TLASourceEditor.Configuration()
        config.font = font
        self.init(
            text: text,
            selectedRange: .constant(NSRange(location: 0, length: 0)),
            configuration: config,
            showFoldingGutter: true
        )
    }
}

// MARK: - View Modifiers

public extension TLAEditorView {

    /// Set the editor's theme
    func theme(_ theme: SyntaxTheme) -> TLAEditorView {
        var copy = self
        copy.configuration.theme = theme
        return copy
    }

    /// Set the editor's font
    func editorFont(_ font: NSFont) -> TLAEditorView {
        var copy = self
        copy.configuration.font = font
        return copy
    }

    /// Set the tab width
    func tabWidth(_ width: Int) -> TLAEditorView {
        var copy = self
        copy.configuration.tabWidth = width
        return copy
    }

    /// Toggle line numbers
    func showLineNumbers(_ show: Bool) -> TLAEditorView {
        var copy = self
        copy.configuration.showLineNumbers = show
        return copy
    }

    /// Set the line height multiplier
    func lineHeight(_ multiplier: CGFloat) -> TLAEditorView {
        var copy = self
        copy.configuration.lineHeight = multiplier
        return copy
    }

    /// Handle text changes
    func onTextChange(_ handler: @escaping (String) -> Void) -> TLAEditorView {
        var copy = self
        copy.onTextChange = handler
        return copy
    }

    /// Handle selection changes
    func onSelectionChange(_ handler: @escaping (NSRange) -> Void) -> TLAEditorView {
        var copy = self
        copy.onSelectionChange = handler
        return copy
    }

    /// Toggle folding gutter visibility
    func showFoldingGutter(_ show: Bool) -> TLAEditorView {
        var copy = self
        copy.showFoldingGutter = show
        return copy
    }
}
