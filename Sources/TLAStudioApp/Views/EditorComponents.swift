import AppKit
import SwiftUI

// MARK: - Line Number Gutter View

class LineNumberGutterView: NSView {
    private weak var textView: NSTextView?
    private var lineStartOffsets: [Int] = [0]
    let gutterWidth: CGFloat = 44

    override var isFlipped: Bool { true }

    init(textView: NSTextView) {
        self.textView = textView
        super.init(frame: NSRect(x: 0, y: 0, width: gutterWidth, height: 100))
        rebuildLineIndex()

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
        rebuildLineIndex()
        needsDisplay = true
    }

    private func rebuildLineIndex() {
        guard let textView else {
            lineStartOffsets = [0]
            return
        }
        lineStartOffsets = TextCoordinateMapper.lineStartOffsets(in: textView.string)
    }

    override func draw(_ dirtyRect: NSRect) {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer,
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

        let nsText = text as NSString
        guard !lineStartOffsets.isEmpty else { return }

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

        // Draw each visible line number
        guard firstVisibleLine <= lastVisibleLine else { return }
        for lineIndex in firstVisibleLine...lastVisibleLine {
            let lineStart = min(lineStartOffsets[lineIndex], nsText.length)
            let lineRange = nsText.lineRange(for: NSRange(location: lineStart, length: 0))
            let lineNumber = lineIndex + 1

            // Get the glyph range for this line
            let glyphRange = layoutManager.glyphRange(forCharacterRange: lineRange, actualCharacterRange: nil)
            guard glyphRange.location != NSNotFound,
                  glyphRange.location < layoutManager.numberOfGlyphs else { continue }

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
    var proofGutterView: ProofStatusGutterOverlay?
    let scrollView: NSScrollView
    private var scrollObserver: NSObjectProtocol?

    private let foldingGutterWidth: CGFloat = 14
    private let proofGutterWidth: CGFloat = 14

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

        // Add proof status gutter overlay
        let proofView = ProofStatusGutterOverlay(textView: textView)
        self.proofGutterView = proofView
        addSubview(proofView)

        addSubview(scrollView)

        // Observe scroll changes
        scrollObserver = NotificationCenter.default.addObserver(
            forName: NSView.boundsDidChangeNotification,
            object: scrollView.contentView,
            queue: .main
        ) { [weak self] _ in
            self?.gutterView.scrollViewBoundsDidChange()
            self?.foldingGutterView?.needsDisplay = true
            self?.proofGutterView?.scrollDidChange()
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
        let showProof = proofGutterView?.superview != nil && !(proofGutterView?.annotations.isEmpty ?? true)
        let foldWidth = showFolding ? foldingGutterWidth : 0
        let proofWidth = showProof ? proofGutterWidth : 0
        let totalGutterWidth = (showLineNumbers ? lineNumberWidth : 0) + foldWidth + proofWidth

        var xOffset: CGFloat = 0

        if showLineNumbers {
            gutterView.frame = NSRect(x: xOffset, y: 0, width: lineNumberWidth, height: bounds.height)
            xOffset += lineNumberWidth
        }

        if showFolding, let foldingView = foldingGutterView {
            foldingView.frame = NSRect(x: xOffset, y: 0, width: foldingGutterWidth, height: bounds.height)
            xOffset += foldingGutterWidth
        }

        if showProof, let proofView = proofGutterView {
            proofView.frame = NSRect(x: xOffset, y: 0, width: proofGutterWidth, height: bounds.height)
            xOffset += proofGutterWidth
        }

        scrollView.frame = NSRect(x: totalGutterWidth, y: 0, width: bounds.width - totalGutterWidth, height: bounds.height)
    }
}

// MARK: - Resizable Divider

/// A draggable divider for resizing panels.
///
/// Contract: the caller owns a single `CGFloat` for the panel dimension and passes
/// `resolveTarget` to compute the new value from `(anchor, totalTranslation)` —
/// typically `anchor - translation` for a "bottom" panel or `anchor + translation`
/// for a "top" panel, with clamping.
///
/// Why this shape: all drag state (active, anchor value) lives in `@GestureState`
/// which SwiftUI auto-resets the moment the gesture ends — including interruptions
/// we can't observe. Parent-owned `@Binding`s for `isDragging` tended to get stuck
/// when `onEnded` didn't fire (modal appearance, window deactivation during drag,
/// etc.), which then made subsequent drags use a stale anchor and appear to "do
/// nothing". `@GestureState` eliminates that class of bugs.
struct ResizableDivider: View {
    /// Current value of the dimension being resized (read at drag start).
    let current: CGFloat
    /// Maps `(anchor, totalTranslation)` to the new value (including clamping).
    let resolveTarget: (_ anchor: CGFloat, _ translation: CGFloat) -> CGFloat
    /// Called whenever the computed target changes.
    let apply: (CGFloat) -> Void

    /// Captured height at drag start. Automatically resets to `nil` when the
    /// gesture ends or is interrupted, so each new drag begins fresh.
    @GestureState private var dragAnchor: CGFloat?

    @State private var isHovering = false

    private var isDragging: Bool { dragAnchor != nil }

    var body: some View {
        Rectangle()
            .fill(isDragging ? Color.accentColor : Color(NSColor.separatorColor))
            .frame(height: isDragging ? 3 : 1)
            .frame(maxWidth: .infinity)
            // Bigger hit area than the visible divider so the cursor doesn't have
            // to hit a 1-pixel target.
            .contentShape(Rectangle().size(width: .infinity, height: 8))
            .onHover { hovering in
                isHovering = hovering
                if hovering {
                    NSCursor.resizeUpDown.set()
                } else if !isDragging {
                    NSCursor.arrow.set()
                }
            }
            .gesture(
                // `.global` coordinate space is stable regardless of the divider's
                // own movement; `value.translation.height` is the cumulative delta
                // since drag start in screen pixels.
                DragGesture(minimumDistance: 0, coordinateSpace: .global)
                    .updating($dragAnchor) { _, state, _ in
                        if state == nil { state = current }
                    }
                    .onChanged { value in
                        let anchor = dragAnchor ?? current
                        let target = resolveTarget(anchor, value.translation.height)
                        apply(target)
                    }
            )
    }
}
