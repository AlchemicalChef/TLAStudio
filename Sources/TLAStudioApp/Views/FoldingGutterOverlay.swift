import AppKit
import SourceEditor

// MARK: - Folding Gutter Overlay

/// An overlay view that displays fold indicators alongside the line number gutter
final class FoldingGutterOverlay: NSView {

    // MARK: - Properties

    private weak var textView: NSTextView?
    private weak var foldingManager: CodeFoldingManager?
    private var trackingArea: NSTrackingArea?
    private var hoveredLine: Int?
    /// Either the shared per-document line index (preferred) or a self-owned fallback.
    /// See audit F-S6-editor-perf-006.
    private let sharedLineIndex: SharedTextLineIndex?
    private var localLineStartOffsets: [Int] = [0]
    private var lineStartOffsets: [Int] {
        sharedLineIndex?.offsets ?? localLineStartOffsets
    }

    private let indicatorWidth: CGFloat = 12
    private let indicatorSize: CGFloat = 9

    // MARK: - Initialization

    init(textView: NSTextView, foldingManager: CodeFoldingManager, sharedLineIndex: SharedTextLineIndex? = nil) {
        self.textView = textView
        self.foldingManager = foldingManager
        self.sharedLineIndex = sharedLineIndex
        super.init(frame: .zero)

        wantsLayer = true
        layer?.backgroundColor = NSColor.clear.cgColor
        // Clip drawing to the overlay's own bounds. Without this, disclosure triangles
        // computed at stale Y positions (e.g. during a bottom-panel resize) can leak
        // outside the editor region and render over the bottom bar.
        layer?.masksToBounds = true
        if sharedLineIndex == nil {
            rebuildTextLineIndex()
        }

        // Observe text changes
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChange),
            name: NSText.didChangeNotification,
            object: textView
        )

        // Observe scroll changes
        if let scrollView = textView.enclosingScrollView {
            NotificationCenter.default.addObserver(
                self,
                selector: #selector(scrollDidChange),
                name: NSView.boundsDidChangeNotification,
                object: scrollView.contentView
            )
        }
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    deinit {
        NotificationCenter.default.removeObserver(self)
    }

    // MARK: - View Lifecycle

    override var isFlipped: Bool { true }

    override func updateTrackingAreas() {
        super.updateTrackingAreas()

        if let existing = trackingArea {
            removeTrackingArea(existing)
        }

        trackingArea = NSTrackingArea(
            rect: bounds,
            options: [.mouseMoved, .mouseEnteredAndExited, .activeInKeyWindow],
            owner: self,
            userInfo: nil
        )
        addTrackingArea(trackingArea!)
    }

    // MARK: - Notifications

    @objc private func textDidChange(_ notification: Notification) {
        // If a shared index owns recomputation, the owner (EditorContainerView)
        // invalidates it; we only refresh our local fallback.
        if sharedLineIndex == nil {
            rebuildTextLineIndex()
        }
        needsDisplay = true
    }

    @objc private func scrollDidChange(_ notification: Notification) {
        needsDisplay = true
    }

    func refreshTextLineIndex() {
        if sharedLineIndex == nil {
            rebuildTextLineIndex()
        }
        needsDisplay = true
    }

    // MARK: - Mouse Events

    override func mouseMoved(with event: NSEvent) {
        let point = convert(event.locationInWindow, from: nil)
        let line = lineAtPoint(point)

        if line != hoveredLine {
            hoveredLine = line
            needsDisplay = true
        }
    }

    override func mouseExited(with event: NSEvent) {
        if hoveredLine != nil {
            hoveredLine = nil
            needsDisplay = true
        }
    }

    override func mouseDown(with event: NSEvent) {
        let point = convert(event.locationInWindow, from: nil)
        let line = lineAtPoint(point)

        if let line = line, let manager = foldingManager {
            if manager.hasFoldableRegion(at: line) {
                manager.toggleFold(at: line)
                needsDisplay = true
            }
        }
    }

    private func lineAtPoint(_ point: NSPoint) -> Int? {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer,
              layoutManager.numberOfGlyphs > 0,
              !lineStartOffsets.isEmpty else {
            return nil
        }

        let scrollView = textView.enclosingScrollView
        let visibleRect = scrollView?.documentVisibleRect ?? textView.visibleRect
        let containerOrigin = textView.textContainerOrigin

        let textPoint = NSPoint(
            x: point.x + visibleRect.minX - containerOrigin.x,
            y: point.y + visibleRect.minY - containerOrigin.y
        )
        var fraction: CGFloat = 0
        let glyphIndex = layoutManager.glyphIndex(
            for: textPoint,
            in: textContainer,
            fractionOfDistanceThroughGlyph: &fraction
        )
        guard glyphIndex < layoutManager.numberOfGlyphs else { return nil }

        let charIndex = layoutManager.characterIndexForGlyph(at: glyphIndex)
        let clampedIndex = max(0, min(charIndex, (textView.string as NSString).length))
        return TextCoordinateMapper.lineIndex(forUTF16Offset: clampedIndex, in: lineStartOffsets)
    }

    // MARK: - Drawing

    override func draw(_ dirtyRect: NSRect) {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer,
              let foldingManager = foldingManager else {
            return
        }

        // Clear background
        NSColor.clear.setFill()
        dirtyRect.fill()

        let scrollView = textView.enclosingScrollView
        let visibleRect = scrollView?.documentVisibleRect ?? textView.visibleRect
        let containerOrigin = textView.textContainerOrigin

        let text = textView.string
        let nsText = text as NSString
        guard !lineStartOffsets.isEmpty, nsText.length > 0 else { return }

        let textContainerVisibleRect = NSRect(
            x: visibleRect.minX - containerOrigin.x,
            y: visibleRect.minY - containerOrigin.y,
            width: visibleRect.width,
            height: visibleRect.height
        )
        let visibleGlyphRange = layoutManager.glyphRange(forBoundingRect: textContainerVisibleRect, in: textContainer)
        guard visibleGlyphRange.location != NSNotFound else { return }

        let visibleCharacterRange = layoutManager.characterRange(
            forGlyphRange: visibleGlyphRange,
            actualGlyphRange: nil
        )
        let firstVisibleLine = TextCoordinateMapper.lineIndex(
            forUTF16Offset: visibleCharacterRange.location,
            in: lineStartOffsets
        )
        let lastVisibleOffset = max(
            visibleCharacterRange.location,
            min(NSMaxRange(visibleCharacterRange), nsText.length) - 1
        )
        let lastVisibleLine = TextCoordinateMapper.lineIndex(
            forUTF16Offset: lastVisibleOffset,
            in: lineStartOffsets
        )

        // Draw fold indicators for visible lines
        for range in foldingManager.foldingRanges {
            // Skip if not visible
            guard range.startLine >= firstVisibleLine - 1,
                  range.startLine <= lastVisibleLine + 1,
                  let lineRect = lineRect(
                    forZeroBasedLine: range.startLine,
                    nsText: nsText,
                    layoutManager: layoutManager,
                    textContainer: textContainer,
                    containerOrigin: containerOrigin,
                    visibleRect: visibleRect
                  ) else { continue }

            // Skip if outside visible area
            if lineRect.maxY < dirtyRect.minY || lineRect.minY > dirtyRect.maxY {
                continue
            }

            // Draw indicator
            let isFolded = foldingManager.isFolded(at: range.startLine)
            let isHovered = hoveredLine == range.startLine
            drawFoldIndicator(
                at: lineRect.minY + (lineRect.height - indicatorSize) / 2,
                isFolded: isFolded,
                isHovered: isHovered
            )
        }
    }

    private func drawFoldIndicator(at y: CGFloat, isFolded: Bool, isHovered: Bool) {
        let x = (bounds.width - indicatorSize) / 2
        let rect = NSRect(x: x, y: y, width: indicatorSize, height: indicatorSize)

        // Background on hover
        if isHovered {
            let bgColor = NSColor.secondaryLabelColor.withAlphaComponent(0.2)
            bgColor.setFill()
            let bgRect = rect.insetBy(dx: -2, dy: -2)
            NSBezierPath(roundedRect: bgRect, xRadius: 3, yRadius: 3).fill()
        }

        // Draw disclosure triangle
        let path = NSBezierPath()

        if isFolded {
            // Right-pointing triangle (collapsed)
            path.move(to: NSPoint(x: rect.minX + 2, y: rect.minY + 1))
            path.line(to: NSPoint(x: rect.maxX - 2, y: rect.midY))
            path.line(to: NSPoint(x: rect.minX + 2, y: rect.maxY - 1))
        } else {
            // Down-pointing triangle (expanded)
            path.move(to: NSPoint(x: rect.minX + 1, y: rect.minY + 2))
            path.line(to: NSPoint(x: rect.maxX - 1, y: rect.minY + 2))
            path.line(to: NSPoint(x: rect.midX, y: rect.maxY - 2))
        }
        path.close()

        let color = isHovered ? NSColor.labelColor : NSColor.secondaryLabelColor
        color.setFill()
        path.fill()
    }

    private func rebuildTextLineIndex() {
        guard let textView else {
            localLineStartOffsets = [0]
            return
        }
        localLineStartOffsets = TextCoordinateMapper.lineStartOffsets(in: textView.string)
    }

    private func lineRect(
        forZeroBasedLine line: Int,
        nsText: NSString,
        layoutManager: NSLayoutManager,
        textContainer: NSTextContainer,
        containerOrigin: NSPoint,
        visibleRect: NSRect
    ) -> NSRect? {
        guard line >= 0, line < lineStartOffsets.count else { return nil }

        let lineStart = min(lineStartOffsets[line], nsText.length)
        guard lineStart < nsText.length else { return nil }

        let lineRange = nsText.lineRange(for: NSRange(location: lineStart, length: 0))
        let glyphRange = layoutManager.glyphRange(
            forCharacterRange: lineRange,
            actualCharacterRange: nil
        )
        guard glyphRange.location != NSNotFound,
              glyphRange.location < layoutManager.numberOfGlyphs else { return nil }

        let rect = layoutManager.lineFragmentRect(forGlyphAt: glyphRange.location, effectiveRange: nil)
        return NSRect(
            x: rect.minX + containerOrigin.x - visibleRect.minX,
            y: rect.minY + containerOrigin.y - visibleRect.minY,
            width: rect.width,
            height: rect.height
        )
    }
}

// MARK: - Editor Container with Folding

/// Extended container that includes folding gutter
class EditorContainerWithFolding: NSView {
    let lineNumberGutter: LineNumberGutterView
    let foldingGutter: FoldingGutterOverlay?
    let scrollView: NSScrollView

    private var scrollObserver: NSObjectProtocol?

    override var isFlipped: Bool { true }

    init(scrollView: NSScrollView, textView: NSTextView, showLineNumbers: Bool, foldingManager: CodeFoldingManager?) {
        self.scrollView = scrollView
        self.lineNumberGutter = LineNumberGutterView(textView: textView)

        if let manager = foldingManager {
            self.foldingGutter = FoldingGutterOverlay(textView: textView, foldingManager: manager)
        } else {
            self.foldingGutter = nil
        }

        super.init(frame: .zero)

        if showLineNumbers {
            addSubview(lineNumberGutter)
        }

        if let foldingGutter = foldingGutter {
            addSubview(foldingGutter)
        }

        addSubview(scrollView)

        // Observe scroll changes
        scrollObserver = NotificationCenter.default.addObserver(
            forName: NSView.boundsDidChangeNotification,
            object: scrollView.contentView,
            queue: .main
        ) { [weak self] _ in
            self?.lineNumberGutter.scrollViewBoundsDidChange()
            self?.foldingGutter?.needsDisplay = true
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

        let lineNumberWidth = lineNumberGutter.gutterWidth
        let foldingWidth: CGFloat = foldingGutter != nil ? 14 : 0
        let showLineNumbers = lineNumberGutter.superview != nil
        let totalGutterWidth = (showLineNumbers ? lineNumberWidth : 0) + foldingWidth

        if showLineNumbers {
            lineNumberGutter.frame = NSRect(x: 0, y: 0, width: lineNumberWidth, height: bounds.height)
        }

        if let foldingGutter = foldingGutter {
            let foldingX = showLineNumbers ? lineNumberWidth : 0
            foldingGutter.frame = NSRect(x: foldingX, y: 0, width: foldingWidth, height: bounds.height)
        }

        scrollView.frame = NSRect(x: totalGutterWidth, y: 0, width: bounds.width - totalGutterWidth, height: bounds.height)
    }
}
