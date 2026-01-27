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
        nsView.content = content
        nsView.visibleRange = visibleRange
        nsView.diagnostics = diagnostics
        nsView.needsDisplay = true
    }
}

// MARK: - Minimap NSView

final class MinimapNSView: NSView {
    var content: String = "" {
        didSet {
            if content != oldValue {
                // Invalidate cached lines when content changes
                cachedLines = nil
                cachedLineOffsets = nil
            }
        }
    }
    var visibleRange: NSRange = NSRange(location: 0, length: 0)
    var diagnostics: [TLADiagnostic] = []
    var onNavigate: ((Int) -> Void)?

    private let lineHeight: CGFloat = 2
    private let charWidth: CGFloat = 1

    // Cached line splits and offsets for efficient drawing and navigation
    private var cachedLines: [String]?
    private var cachedLineOffsets: [Int]?

    override var isFlipped: Bool { true }

    /// Get cached lines, computing and caching if needed
    private var lines: [String] {
        if let cached = cachedLines {
            return cached
        }
        let computed = content.components(separatedBy: "\n")
        cachedLines = computed
        return computed
    }

    /// Get cached line offsets for character position calculation
    private var lineOffsets: [Int] {
        if let cached = cachedLineOffsets {
            return cached
        }
        var offsets: [Int] = [0]
        var offset = 0
        for line in lines {
            offset += line.count + 1  // +1 for newline
            offsets.append(offset)
        }
        cachedLineOffsets = offsets
        return offsets
    }

    override func draw(_ dirtyRect: NSRect) {
        // Background
        NSColor.textBackgroundColor.setFill()
        bounds.fill()

        // Use cached lines
        let lineArray = lines

        // Draw each line as a thin bar
        for (index, line) in lineArray.enumerated() {
            let y = CGFloat(index) * lineHeight
            let width = min(CGFloat(line.count) * charWidth, bounds.width - 4)

            if width > 0 {
                // Determine line color based on content
                let color = colorForLine(line, at: index)
                color.setFill()

                let lineRect = NSRect(x: 2, y: y, width: width, height: lineHeight - 0.5)
                lineRect.fill()
            }
        }

        // Draw visible viewport indicator
        let visibleStartLine = lineNumber(for: visibleRange.location)
        let visibleEndLine = lineNumber(for: visibleRange.location + visibleRange.length)

        let viewportY = CGFloat(visibleStartLine) * lineHeight
        let viewportHeight = CGFloat(visibleEndLine - visibleStartLine + 1) * lineHeight

        NSColor.systemBlue.withAlphaComponent(0.15).setFill()
        let viewportRect = NSRect(x: 0, y: viewportY, width: bounds.width, height: viewportHeight)
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

    private func colorForLine(_ line: String, at index: Int) -> NSColor {
        let trimmed = line.trimmingCharacters(in: .whitespaces)

        // Comments
        if trimmed.hasPrefix("\\*") || trimmed.hasPrefix("(*") {
            return NSColor.systemGreen.withAlphaComponent(0.6)
        }

        // Keywords
        let keywords = ["MODULE", "EXTENDS", "VARIABLE", "CONSTANT", "ASSUME", "THEOREM", "PROOF", "LET", "IN"]
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
}

// MARK: - SwiftUI Wrapper for Settings Toggle

struct MinimapContainer: View {
    let content: String
    let visibleRange: NSRange
    let diagnostics: [TLADiagnostic]
    let onNavigate: (Int) -> Void

    @AppStorage("showMinimap") private var showMinimap = false

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
