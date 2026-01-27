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

    private let indicatorWidth: CGFloat = 12
    private let indicatorSize: CGFloat = 9

    // MARK: - Initialization

    init(textView: NSTextView, foldingManager: CodeFoldingManager) {
        self.textView = textView
        self.foldingManager = foldingManager
        super.init(frame: .zero)

        wantsLayer = true
        layer?.backgroundColor = NSColor.clear.cgColor

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
        needsDisplay = true
    }

    @objc private func scrollDidChange(_ notification: Notification) {
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
              let textContainer = textView.textContainer else {
            return nil
        }

        let scrollView = textView.enclosingScrollView
        let visibleRect = scrollView?.documentVisibleRect ?? textView.visibleRect

        let text = textView.string
        let lines = text.components(separatedBy: "\n")
        var charOffset = 0

        for (lineIndex, line) in lines.enumerated() {
            let lineRange = NSRange(location: charOffset, length: max(1, line.count))
            let glyphRange = layoutManager.glyphRange(forCharacterRange: lineRange, actualCharacterRange: nil)

            if glyphRange.location != NSNotFound {
                var lineRect = layoutManager.boundingRect(forGlyphRange: glyphRange, in: textContainer)
                lineRect.origin.y += textView.textContainerInset.height - visibleRect.minY

                if point.y >= lineRect.minY && point.y < lineRect.maxY {
                    return lineIndex
                }
            }

            charOffset += line.count + 1
        }

        return nil
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

        let text = textView.string
        let lines = text.components(separatedBy: "\n")

        // Draw fold indicators for visible lines
        for range in foldingManager.foldingRanges {
            // Skip if not visible
            guard range.startLine < lines.count else { continue }

            // Calculate line position
            var charOffset = 0
            for i in 0..<range.startLine {
                charOffset += lines[i].count + 1
            }

            let lineRange = NSRange(location: charOffset, length: max(1, lines[range.startLine].count))
            let glyphRange = layoutManager.glyphRange(forCharacterRange: lineRange, actualCharacterRange: nil)

            guard glyphRange.location != NSNotFound else { continue }

            var lineRect = layoutManager.boundingRect(forGlyphRange: glyphRange, in: textContainer)
            lineRect.origin.y += textView.textContainerInset.height - visibleRect.minY

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
