import AppKit
import SourceEditor

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

        guard let foldRange = hiddenTextRange(for: range, in: textView.string) else { return }

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

        guard let unfoldRange = hiddenTextRange(for: range, in: textView.string) else { return }

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

    private func hiddenTextRange(for range: TLAFoldingRange, in text: String) -> NSRange? {
        let analysis = TextCoordinateMapper.analyze(text)
        let lineCount = analysis.lineStartOffsets.count
        guard range.startLine >= 0, range.startLine < lineCount else { return nil }

        let endLine = max(range.startLine, min(range.endLine, lineCount - 1))
        let startOffset = lineEndOffset(
            forLine: range.startLine,
            lineStartOffsets: analysis.lineStartOffsets,
            textLength: analysis.utf16Length
        )
        let endOffset = lineEndOffset(
            forLine: endLine,
            lineStartOffsets: analysis.lineStartOffsets,
            textLength: analysis.utf16Length
        )

        guard endOffset > startOffset else { return nil }
        return NSRange(location: startOffset, length: endOffset - startOffset)
    }

    private func lineEndOffset(
        forLine line: Int,
        lineStartOffsets: [Int],
        textLength: Int
    ) -> Int {
        if line + 1 < lineStartOffsets.count {
            return max(lineStartOffsets[line], lineStartOffsets[line + 1] - 1)
        }
        return textLength
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

        // Migrate visible-line and line-start computation onto TextCoordinateMapper
        // so we don't pay an O(N) Character-based `components(separatedBy:)` and
        // per-line `count + 1` walk on every paint. See audit F-GAP06-001.
        let text = textView.string
        let lineStartOffsets = TextCoordinateMapper.lineStartOffsets(in: text)
        guard !lineStartOffsets.isEmpty else { return }

        let nsText = text as NSString

        let visibleRect = textView.visibleRect
        let glyphRange = layoutManager.glyphRange(forBoundingRect: visibleRect, in: textContainer)
        let characterRange = layoutManager.characterRange(forGlyphRange: glyphRange, actualGlyphRange: nil)

        let visibleStartLine = TextCoordinateMapper.lineIndex(
            forUTF16Offset: characterRange.location,
            in: lineStartOffsets
        )
        let lastVisibleOffset = max(
            characterRange.location,
            min(NSMaxRange(characterRange), nsText.length) - 1
        )
        let visibleEndLine = TextCoordinateMapper.lineIndex(
            forUTF16Offset: lastVisibleOffset,
            in: lineStartOffsets
        )

        // Draw fold indicators for visible lines
        for range in foldingRanges {
            guard range.startLine >= visibleStartLine - 1 && range.startLine <= visibleEndLine + 1 else {
                continue
            }
            guard range.startLine >= 0, range.startLine < lineStartOffsets.count else {
                continue
            }

            let lineCharOffset = min(lineStartOffsets[range.startLine], nsText.length)
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

        // Use TextCoordinateMapper rather than `components(separatedBy:)` + per-line
        // `count + 1`. See audit F-GAP06-001.
        let text = textView.string
        let lineStartOffsets = TextCoordinateMapper.lineStartOffsets(in: text)
        let nsText = text as NSString

        // Find which fold indicator was clicked
        for range in foldingRanges {
            guard range.startLine >= 0, range.startLine < lineStartOffsets.count else {
                continue
            }
            let lineCharOffset = min(lineStartOffsets[range.startLine], nsText.length)

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
    var detailedCompletionProvider: ((Int) async -> [TLADetailedCompletionItem])?
    var foldingManager: CodeFoldingManager?
    var editorConfiguration = TLASourceEditor.Configuration() {
        didSet {
            applyEditorConfiguration()
        }
    }

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

    func applyEditorConfiguration() {
        font = editorConfiguration.font

        let paragraphStyle = NSMutableParagraphStyle()
        paragraphStyle.lineHeightMultiple = editorConfiguration.lineHeight
        if let font {
            let spaceWidth = " ".size(withAttributes: [.font: font]).width
            paragraphStyle.defaultTabInterval = spaceWidth * CGFloat(editorConfiguration.tabWidth)
        }

        defaultParagraphStyle = paragraphStyle
        typingAttributes[.font] = editorConfiguration.font
        typingAttributes[.paragraphStyle] = paragraphStyle

        let fullRange = NSRange(location: 0, length: (string as NSString).length)
        if fullRange.length > 0 {
            textStorage?.addAttribute(.paragraphStyle, value: paragraphStyle, range: fullRange)
        }

        needsDisplay = true
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

    override func insertTab(_ sender: Any?) {
        let text = editorConfiguration.insertSpacesForTabs
            ? String(repeating: " ", count: editorConfiguration.tabWidth)
            : "\t"
        insertText(text, replacementRange: selectedRange())
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
