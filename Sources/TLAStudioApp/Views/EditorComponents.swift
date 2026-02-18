import AppKit
import SwiftUI

// MARK: - Line Number Gutter View

class LineNumberGutterView: NSView {
    private weak var textView: NSTextView?
    let gutterWidth: CGFloat = 44

    override var isFlipped: Bool { true }

    init(textView: NSTextView) {
        self.textView = textView
        super.init(frame: NSRect(x: 0, y: 0, width: gutterWidth, height: 100))

        // Observe text changes
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChange(_:)),
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

    func scrollViewBoundsDidChange() {
        needsDisplay = true
    }

    @objc private func textDidChange(_ notification: Notification) {
        needsDisplay = true
    }

    override func draw(_ dirtyRect: NSRect) {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let scrollView = textView.enclosingScrollView else {
            return
        }

        // Background
        NSColor.textBackgroundColor.setFill()
        bounds.fill()

        // Separator line
        NSColor.separatorColor.setStroke()
        let separatorPath = NSBezierPath()
        separatorPath.move(to: NSPoint(x: bounds.width - 0.5, y: 0))
        separatorPath.line(to: NSPoint(x: bounds.width - 0.5, y: bounds.height))
        separatorPath.stroke()

        let text = textView.string
        guard !text.isEmpty else { return }

        let font = NSFont.monospacedDigitSystemFont(ofSize: 11, weight: .regular)
        let attrs: [NSAttributedString.Key: Any] = [
            .font: font,
            .foregroundColor: NSColor.secondaryLabelColor
        ]

        // Get visible rect in document coordinates
        let visibleRect = scrollView.documentVisibleRect
        let containerOrigin = textView.textContainerOrigin

        // Get all line ranges
        var lineRanges: [NSRange] = []
        var searchStart = 0
        let nsText = text as NSString
        while searchStart < nsText.length {
            let lineRange = nsText.lineRange(for: NSRange(location: searchStart, length: 0))
            lineRanges.append(lineRange)
            searchStart = NSMaxRange(lineRange)
        }

        // Draw each visible line number
        for (index, lineRange) in lineRanges.enumerated() {
            let lineNumber = index + 1

            // Get the glyph range for this line
            let glyphRange = layoutManager.glyphRange(forCharacterRange: lineRange, actualCharacterRange: nil)
            guard glyphRange.location != NSNotFound else { continue }

            // Get the line rect in layout manager coordinates
            let lineRect = layoutManager.lineFragmentRect(forGlyphAt: glyphRange.location, effectiveRange: nil)

            // Calculate Y position in document coordinates
            let docY = lineRect.minY + containerOrigin.y

            // Skip if above visible area
            if docY + lineRect.height < visibleRect.minY { continue }
            // Stop if below visible area
            if docY > visibleRect.maxY { break }

            // Convert to gutter view coordinates (relative to visible area)
            let gutterY = docY - visibleRect.minY

            let lineNumberString = "\(lineNumber)"
            let attrString = NSAttributedString(string: lineNumberString, attributes: attrs)
            let stringSize = attrString.size()

            let x = bounds.width - stringSize.width - 6
            let y = gutterY + (lineRect.height - stringSize.height) / 2

            attrString.draw(at: NSPoint(x: x, y: y))
        }
    }
}

// MARK: - Editor Container View (Line Numbers + Editor)

class EditorContainerView: NSView {
    let gutterView: LineNumberGutterView
    var foldingGutterView: FoldingGutterOverlay?
    let scrollView: NSScrollView
    private var scrollObserver: NSObjectProtocol?

    private let foldingGutterWidth: CGFloat = 14

    override var isFlipped: Bool { true }

    init(scrollView: NSScrollView, textView: NSTextView, showLineNumbers: Bool, foldingManager: CodeFoldingManager? = nil) {
        self.scrollView = scrollView
        self.gutterView = LineNumberGutterView(textView: textView)
        super.init(frame: .zero)

        if showLineNumbers {
            addSubview(gutterView)
        }

        // Add folding gutter if manager provided
        if let manager = foldingManager {
            let foldingView = FoldingGutterOverlay(textView: textView, foldingManager: manager)
            self.foldingGutterView = foldingView
            addSubview(foldingView)
        }

        addSubview(scrollView)

        // Observe scroll changes
        scrollObserver = NotificationCenter.default.addObserver(
            forName: NSView.boundsDidChangeNotification,
            object: scrollView.contentView,
            queue: .main
        ) { [weak self] _ in
            self?.gutterView.scrollViewBoundsDidChange()
            self?.foldingGutterView?.needsDisplay = true
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

        let lineNumberWidth = gutterView.gutterWidth
        let showLineNumbers = gutterView.superview != nil
        let showFolding = foldingGutterView?.superview != nil
        let foldWidth = showFolding ? foldingGutterWidth : 0
        let totalGutterWidth = (showLineNumbers ? lineNumberWidth : 0) + foldWidth

        if showLineNumbers {
            gutterView.frame = NSRect(x: 0, y: 0, width: lineNumberWidth, height: bounds.height)
        }

        if showFolding, let foldingView = foldingGutterView {
            let foldX = showLineNumbers ? lineNumberWidth : 0
            foldingView.frame = NSRect(x: foldX, y: 0, width: foldingGutterWidth, height: bounds.height)
        }

        scrollView.frame = NSRect(x: totalGutterWidth, y: 0, width: bounds.width - totalGutterWidth, height: bounds.height)
    }
}

// MARK: - Resizable Divider

/// A draggable divider for resizing panels
struct ResizableDivider: View {
    @Binding var isDragging: Bool
    let onDrag: (CGFloat) -> Void

    /// Tracks last cumulative translation to compute per-frame delta
    @State private var lastTranslation: CGFloat = 0

    var body: some View {
        Rectangle()
            .fill(isDragging ? Color.accentColor : Color(NSColor.separatorColor))
            .frame(height: isDragging ? 3 : 1)
            .frame(maxWidth: .infinity)
            .contentShape(Rectangle().size(width: .infinity, height: 8))
            .onHover { hovering in
                if hovering {
                    NSCursor.resizeUpDown.push()
                } else if !isDragging {
                    NSCursor.pop()
                }
            }
            .gesture(
                DragGesture(minimumDistance: 1)
                    .onChanged { value in
                        let currentTranslation = value.translation.height
                        let delta = currentTranslation - lastTranslation
                        lastTranslation = currentTranslation
                        isDragging = true
                        onDrag(delta)
                    }
                    .onEnded { _ in
                        isDragging = false
                        lastTranslation = 0
                    }
            )
    }
}
