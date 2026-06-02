import SwiftUI
import AppKit

// MARK: - Minimap View

/// A minimap overview of the document content
struct MinimapView: NSViewRepresentable {
    let content: String
    let visibleRange: NSRange
    let diagnostics: [TLADiagnostic]
    let onNavigate: (Int) -> Void

    private let minimapWidth: CGFloat = 80
    private let lineHeight: CGFloat = 2

    func makeNSView(context: Context) -> MinimapNSView {
        let view = MinimapNSView()
        view.onNavigate = onNavigate
        return view
    }

    func updateNSView(_ nsView: MinimapNSView, context: Context) {
        // Diff before invalidating: only mark dirty when something actually changed,
        // and when only the viewport indicator changed, invalidate just the viewport
        // band rather than triggering a full O(N-lines) repaint. See audit
        // F-S4-memory-005.
        let contentChanged = nsView.content != content
        let diagnosticsChanged = nsView.diagnostics != diagnostics
        let oldViewport = nsView.visibleRange
        let viewportChanged = !NSEqualRanges(oldViewport, visibleRange)

        if contentChanged {
            nsView.content = content
        }
        if diagnosticsChanged {
            nsView.diagnostics = diagnostics
        }
        if viewportChanged {
            nsView.visibleRange = visibleRange
        }

        if contentChanged || diagnosticsChanged {
            nsView.needsDisplay = true
        } else if viewportChanged {
            nsView.invalidateViewport(previous: oldViewport, current: visibleRange)
        }
    }
}

// MARK: - Minimap NSView

final class MinimapNSView: NSView {
    var content: String = "" {
        didSet {
            if content != oldValue {
                // Invalidate cached layout when content changes
                cachedLineMetrics = nil
                cachedLineOffsets = nil
            }
        }
    }
    var visibleRange: NSRange = NSRange(location: 0, length: 0)
    var diagnostics: [TLADiagnostic] = [] {
        didSet {
            if diagnostics != oldValue {
                // Diagnostic markers live in their own band; conservatively repaint.
                needsDisplay = true
            }
        }
    }
    var onNavigate: ((Int) -> Void)?

    private let lineHeight: CGFloat = 2
    private let charWidth: CGFloat = 1

    /// Per-line precomputed render metrics (visual width + fill color).
    /// Built once per content change via a single Substring iteration over `content`,
    /// avoiding the previous per-keystroke `[String]` line-split allocation.
    /// See audit F-S4-memory-004.
    private struct LineMetric {
        let width: CGFloat
        let color: NSColor
    }
    private var cachedLineMetrics: [LineMetric]?
    private var cachedLineOffsets: [Int]?

    override var isFlipped: Bool { true }

    /// Get cached per-line draw metrics, computing and caching on miss.
    /// One pass over `content.split(...omittingEmptySubsequences: false)` produces
    /// both the width and the color; we never materialize `[String]`.
    private var lineMetrics: [LineMetric] {
        if let cached = cachedLineMetrics {
            return cached
        }
        var metrics: [LineMetric] = []
        // Reserve a rough estimate; content.count is a Character count but a good
        // upper-bound proxy for "small" specs and a soft over-allocation for big.
        metrics.reserveCapacity(max(16, content.count / 32))
        let maxBarWidth = bounds.width - 4
        for substring in content.split(separator: "\n", omittingEmptySubsequences: false) {
            // `substring.count` is O(n) per line over Characters; but we already
            // had to walk the line for color classification, so the cost is one
            // amortized walk per cache build, not per draw.
            let width = min(CGFloat(substring.count) * charWidth, maxBarWidth)
            let color = colorForLine(substring)
            metrics.append(LineMetric(width: width, color: color))
        }
        cachedLineMetrics = metrics
        return metrics
    }

    /// Get cached line offsets for character position calculation
    private var lineOffsets: [Int] {
        if let cached = cachedLineOffsets {
            return cached
        }
        let offsets = TextCoordinateMapper.lineStartOffsets(in: content)
        cachedLineOffsets = offsets
        return offsets
    }

    /// Invalidate just the viewport indicator band when only the visible range
    /// changed. The union of the previous and current viewport rects is dirtied
    /// so the old indicator is erased and the new one drawn, without repainting
    /// the per-line bars or diagnostic markers.
    func invalidateViewport(previous: NSRange, current: NSRange) {
        let metrics = lineMetrics
        let lineCount = metrics.count
        guard lineCount > 0 else {
            needsDisplay = true
            return
        }

        // Diagnostic markers and per-line bars live in disjoint regions from the
        // viewport rect except for the body, but repainting the union of the two
        // viewport bands also re-fills the background and bars in that band, so we
        // dirty the slim diagnostic strip on the right edge for the affected
        // vertical extent too.
        let prevRect = viewportRect(for: previous)
        let curRect = viewportRect(for: current)
        let union = prevRect.union(curRect)
        // Extend to full width so diagnostic markers in the band are redrawn.
        let fullWidthBand = NSRect(x: 0, y: union.minY, width: bounds.width, height: union.height)
        setNeedsDisplay(fullWidthBand.insetBy(dx: -1, dy: -1))
    }

    private func viewportRect(for range: NSRange) -> NSRect {
        let startLine = lineNumber(for: range.location)
        let endLine = lineNumber(for: range.location + range.length)
        let y = CGFloat(startLine) * lineHeight
        let height = CGFloat(max(1, endLine - startLine + 1)) * lineHeight
        return NSRect(x: 0, y: y, width: bounds.width, height: height)
    }

    override func draw(_ dirtyRect: NSRect) {
        // Background — only fill the dirty rect rather than always the full bounds,
        // so viewport-only invalidations stay cheap.
        NSColor.textBackgroundColor.setFill()
        dirtyRect.fill()

        let metrics = lineMetrics

        // Draw each line as a thin bar, clipped to dirtyRect for cheap repaints.
        for (index, metric) in metrics.enumerated() {
            let y = CGFloat(index) * lineHeight
            if y + lineHeight < dirtyRect.minY { continue }
            if y > dirtyRect.maxY { break }

            if metric.width > 0 {
                metric.color.setFill()
                let lineRect = NSRect(x: 2, y: y, width: metric.width, height: lineHeight - 0.5)
                lineRect.fill()
            }
        }

        // Draw visible viewport indicator
        let viewportRect = self.viewportRect(for: visibleRange)

        NSColor.systemBlue.withAlphaComponent(0.15).setFill()
        viewportRect.fill()

        // Viewport border
        NSColor.systemBlue.withAlphaComponent(0.4).setStroke()
        let borderPath = NSBezierPath(rect: viewportRect.insetBy(dx: 0.5, dy: 0.5))
        borderPath.lineWidth = 1
        borderPath.stroke()

        // Draw diagnostic markers
        for diagnostic in diagnostics {
            let line = Int(diagnostic.range.start.line)
            let y = CGFloat(line) * lineHeight
            if y + lineHeight < dirtyRect.minY || y > dirtyRect.maxY { continue }

            let markerColor: NSColor = diagnostic.severity == .error ? .systemRed : .systemOrange
            markerColor.setFill()

            let markerRect = NSRect(x: bounds.width - 4, y: y, width: 3, height: lineHeight)
            markerRect.fill()
        }
    }

    override func mouseDown(with event: NSEvent) {
        let location = convert(event.locationInWindow, from: nil)
        let clickedLine = Int(location.y / lineHeight)

        // Use cached line offsets for efficient navigation
        let offsets = lineOffsets
        let charOffset = clickedLine < offsets.count ? offsets[clickedLine] : offsets.last ?? 0

        onNavigate?(charOffset)
    }

    private func lineNumber(for characterOffset: Int) -> Int {
        // Use binary search on cached line offsets for O(log n) lookup
        let offsets = lineOffsets
        guard !offsets.isEmpty else { return 0 }
        var low = 0
        var high = offsets.count - 1

        while low < high {
            let mid = (low + high + 1) / 2
            if offsets[mid] <= characterOffset {
                low = mid
            } else {
                high = mid - 1
            }
        }

        return low
    }

    /// Classify a line by its prefix to pick a minimap bar color.
    /// Accepts `Substring` so we can avoid copying to `String`.
    private func colorForLine(_ line: Substring) -> NSColor {
        // Trim leading whitespace by skipping space/tab characters.
        var idx = line.startIndex
        while idx < line.endIndex, line[idx] == " " || line[idx] == "\t" {
            idx = line.index(after: idx)
        }
        let trimmed = line[idx...]

        // Comments
        if trimmed.hasPrefix("\\*") || trimmed.hasPrefix("(*") {
            return NSColor.systemGreen.withAlphaComponent(0.6)
        }

        // Keywords
        let keywords: [String] = ["MODULE", "EXTENDS", "VARIABLE", "CONSTANT", "ASSUME", "THEOREM", "PROOF", "LET", "IN"]
        for keyword in keywords {
            if trimmed.hasPrefix(keyword) {
                return NSColor.systemPurple.withAlphaComponent(0.8)
            }
        }

        // Operators/definitions
        if trimmed.contains("==") {
            return NSColor.systemBlue.withAlphaComponent(0.7)
        }

        // Default
        return NSColor.secondaryLabelColor.withAlphaComponent(0.4)
    }

    override func setFrameSize(_ newSize: NSSize) {
        let widthChanged = newSize.width != frame.size.width
        super.setFrameSize(newSize)
        // Bar widths are clamped by bounds.width; resize invalidates them.
        if widthChanged {
            cachedLineMetrics = nil
            needsDisplay = true
        }
    }
}

// MARK: - SwiftUI Wrapper for Settings Toggle

struct MinimapContainer: View {
    let content: String
    let visibleRange: NSRange
    let diagnostics: [TLADiagnostic]
    let onNavigate: (Int) -> Void

    @AppStorage(UserSettings.Keys.showMinimap) private var showMinimap = false

    var body: some View {
        if showMinimap {
            MinimapView(
                content: content,
                visibleRange: visibleRange,
                diagnostics: diagnostics,
                onNavigate: onNavigate
            )
            .frame(width: 80)
        }
    }
}

// MARK: - Preview

#if DEBUG
struct MinimapView_Previews: PreviewProvider {
    static var previews: some View {
        MinimapView(
            content: """
            ---- MODULE Test ----
            EXTENDS Naturals

            VARIABLE x

            Init == x = 0

            Next == x' = x + 1

            (* This is a comment *)
            Spec == Init /\\ [][Next]_x
            ====
            """,
            visibleRange: NSRange(location: 0, length: 100),
            diagnostics: [],
            onNavigate: { _ in }
        )
        .frame(width: 80, height: 200)
    }
}
#endif
