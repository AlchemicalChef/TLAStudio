import AppKit

// MARK: - Proof Status Gutter Overlay

/// An overlay view that displays proof status indicators (colored dots) alongside the editor gutter.
/// Follows the same overlay pattern as FoldingGutterOverlay.
final class ProofStatusGutterOverlay: NSView {

    // MARK: - Properties

    private weak var textView: NSTextView?
    private var trackingArea: NSTrackingArea?
    private var hoveredLine: Int?

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

    init(textView: NSTextView) {
        self.textView = textView
        super.init(frame: .zero)

        wantsLayer = true
        layer?.backgroundColor = NSColor.clear.cgColor
        // Clip drawing to the overlay's bounds; prevents dots from rendering over the
        // bottom panel when the editor region shrinks mid-resize.
        layer?.masksToBounds = true

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
              let textContainer = textView.textContainer else {
            return nil
        }

        let scrollView = textView.enclosingScrollView
        let visibleRect = scrollView?.documentVisibleRect ?? textView.visibleRect

        // Convert point to text view coordinates
        let textPoint = NSPoint(
            x: 0,
            y: point.y + visibleRect.minY - textView.textContainerInset.height
        )

        var fraction: CGFloat = 0
        let glyphIndex = layoutManager.glyphIndex(for: textPoint, in: textContainer, fractionOfDistanceThroughGlyph: &fraction)
        let charIndex = layoutManager.characterIndexForGlyph(at: glyphIndex)

        // Count lines up to charIndex (use NSString for UTF-16 consistency with NSLayoutManager)
        let text = textView.string as NSString
        guard text.length > 0 else { return nil }
        let prefix = text.substring(to: min(charIndex, text.length))
        return prefix.components(separatedBy: "\n").count
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

        let text = textView.string as NSString

        // Get visible glyph range
        let glyphRange = layoutManager.glyphRange(forBoundingRect: visibleRect, in: textContainer)
        let charRange = layoutManager.characterRange(forGlyphRange: glyphRange, actualGlyphRange: nil)

        // Walk visible lines
        var lineNumber = 1
        // Count lines before visible range
        let preText = text.substring(to: min(charRange.location, text.length))
        lineNumber = preText.components(separatedBy: "\n").count

        // Enumerate visible lines
        text.enumerateSubstrings(in: charRange, options: [.byLines, .substringNotRequired]) { [weak self] _, substringRange, _, _ in
            guard let self = self else { return }

            // Check for annotation at this line
            if let annotation = self.annotationsByLine[lineNumber] {
                let glyphIdx = layoutManager.glyphIndexForCharacter(at: substringRange.location)
                let lineRect = layoutManager.lineFragmentRect(forGlyphAt: glyphIdx, effectiveRange: nil)
                let y = lineRect.minY + textView.textContainerInset.height - visibleRect.minY

                // Draw colored dot
                let dotX = (self.bounds.width - self.dotSize) / 2
                let dotY = y + (lineRect.height - self.dotSize) / 2
                let dotRect = NSRect(x: dotX, y: dotY, width: self.dotSize, height: self.dotSize)

                let color = annotation.iconColor
                color.setFill()
                NSBezierPath(ovalIn: dotRect).fill()

                // Hover highlight
                if self.hoveredLine == lineNumber {
                    color.withAlphaComponent(0.3).setFill()
                    let hoverRect = NSRect(x: 0, y: y, width: self.bounds.width, height: lineRect.height)
                    hoverRect.fill()
                }
            }

            lineNumber += 1
        }
    }
}
