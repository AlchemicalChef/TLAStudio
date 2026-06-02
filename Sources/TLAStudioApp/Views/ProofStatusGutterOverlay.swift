import AppKit

// MARK: - Proof Status Gutter Overlay

/// An overlay view that displays proof status indicators (colored dots) alongside the editor gutter.
/// Follows the same overlay pattern as FoldingGutterOverlay.
final class ProofStatusGutterOverlay: NSView {

    // MARK: - Properties

    private weak var textView: NSTextView?
    private var trackingArea: NSTrackingArea?
    private var hoveredLine: Int?
    /// Either the shared per-document line index (preferred) or a self-owned fallback.
    /// See audit F-S6-editor-perf-006.
    private let sharedLineIndex: SharedTextLineIndex?
    private var localLineStartOffsets: [Int] = [0]
    private var lineStartOffsets: [Int] {
        sharedLineIndex?.offsets ?? localLineStartOffsets
    }

    /// Annotations indexed by line for efficient lookup during drawing
    private var annotationsByLine: [Int: ProofAnnotation] = [:]

    /// All annotations (set externally when proof results update)
    var annotations: [ProofAnnotation] = [] {
        didSet {
            rebuildLineIndex()
            needsDisplay = true
        }
    }

    private let dotSize: CGFloat = 8

    // MARK: - Initialization

    init(textView: NSTextView, sharedLineIndex: SharedTextLineIndex? = nil) {
        self.textView = textView
        self.sharedLineIndex = sharedLineIndex
        super.init(frame: .zero)

        wantsLayer = true
        layer?.backgroundColor = NSColor.clear.cgColor
        // Clip drawing to the overlay's bounds; prevents dots from rendering over the
        // bottom panel when the editor region shrinks mid-resize.
        layer?.masksToBounds = true
        if sharedLineIndex == nil {
            rebuildTextLineIndex()
        }

        // Observe text changes to update dot positions when lines shift
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChange),
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

    // MARK: - Index

    private func rebuildLineIndex() {
        annotationsByLine.removeAll()
        for annotation in annotations {
            // Use the first line of the range as the key
            annotationsByLine[annotation.lineRange.lowerBound] = annotation
        }
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

    @objc func scrollDidChange() {
        needsDisplay = true
    }

    @objc private func textDidChange(_ notification: Notification) {
        // If a shared index owns recomputation, the owner (EditorContainerView)
        // invalidates it; we only refresh our local fallback.
        if sharedLineIndex == nil {
            rebuildTextLineIndex()
        }
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
            if let line = line, let annotation = annotationsByLine[line] {
                toolTip = annotation.tooltipText
            } else {
                toolTip = nil
            }
            needsDisplay = true
        }
    }

    override func mouseExited(with event: NSEvent) {
        if hoveredLine != nil {
            hoveredLine = nil
            toolTip = nil
            needsDisplay = true
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

        // Convert point to text view coordinates
        let textPoint = NSPoint(
            x: point.x + visibleRect.minX - containerOrigin.x,
            y: point.y + visibleRect.minY - containerOrigin.y
        )

        var fraction: CGFloat = 0
        let glyphIndex = layoutManager.glyphIndex(for: textPoint, in: textContainer, fractionOfDistanceThroughGlyph: &fraction)
        guard glyphIndex < layoutManager.numberOfGlyphs else { return nil }

        let charIndex = layoutManager.characterIndexForGlyph(at: glyphIndex)
        let clampedIndex = max(0, min(charIndex, (textView.string as NSString).length))
        return TextCoordinateMapper.lineIndex(forUTF16Offset: clampedIndex, in: lineStartOffsets) + 1
    }

    // MARK: - Drawing

    override func draw(_ dirtyRect: NSRect) {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer,
              !annotationsByLine.isEmpty else {
            return
        }

        // Clear background
        NSColor.clear.setFill()
        dirtyRect.fill()

        let scrollView = textView.enclosingScrollView
        let visibleRect = scrollView?.documentVisibleRect ?? textView.visibleRect
        let containerOrigin = textView.textContainerOrigin

        let text = textView.string as NSString
        guard !lineStartOffsets.isEmpty, text.length > 0 else { return }

        // Get visible glyph range
        let textContainerVisibleRect = NSRect(
            x: visibleRect.minX - containerOrigin.x,
            y: visibleRect.minY - containerOrigin.y,
            width: visibleRect.width,
            height: visibleRect.height
        )
        let glyphRange = layoutManager.glyphRange(forBoundingRect: textContainerVisibleRect, in: textContainer)
        guard glyphRange.location != NSNotFound else { return }

        let charRange = layoutManager.characterRange(forGlyphRange: glyphRange, actualGlyphRange: nil)
        let firstVisibleLine = TextCoordinateMapper.lineIndex(
            forUTF16Offset: charRange.location,
            in: lineStartOffsets
        )
        let lastVisibleOffset = max(
            charRange.location,
            min(NSMaxRange(charRange), text.length) - 1
        )
        let lastVisibleLine = TextCoordinateMapper.lineIndex(
            forUTF16Offset: lastVisibleOffset,
            in: lineStartOffsets
        )

        // Walk visible lines
        guard firstVisibleLine <= lastVisibleLine else { return }
        for lineIndex in firstVisibleLine...lastVisibleLine {
            let lineNumber = lineIndex + 1

            // Check for annotation at this line
            if let annotation = annotationsByLine[lineNumber],
               let lineRect = lineRect(
                forZeroBasedLine: lineIndex,
                nsText: text,
                layoutManager: layoutManager,
                textContainer: textContainer,
                containerOrigin: containerOrigin,
                visibleRect: visibleRect
               ) {
                let y = lineRect.minY

                // Draw colored dot
                let dotX = (bounds.width - dotSize) / 2
                let dotY = y + (lineRect.height - dotSize) / 2
                let dotRect = NSRect(x: dotX, y: dotY, width: dotSize, height: dotSize)

                let color = annotation.iconColor
                color.setFill()
                NSBezierPath(ovalIn: dotRect).fill()

                // Hover highlight
                if hoveredLine == lineNumber {
                    color.withAlphaComponent(0.3).setFill()
                    let hoverRect = NSRect(x: 0, y: y, width: bounds.width, height: lineRect.height)
                    hoverRect.fill()
                }
            }
        }
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
