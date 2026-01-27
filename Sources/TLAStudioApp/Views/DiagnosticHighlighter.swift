import AppKit
import Foundation

// MARK: - Diagnostic Highlighter

/// Manages diagnostic underlines and tooltips in the editor
final class DiagnosticHighlighter {

    // MARK: - Types

    /// A diagnostic with its calculated text range
    struct MappedDiagnostic {
        let diagnostic: TLADiagnostic
        let range: NSRange
    }

    // MARK: - Properties

    private weak var textView: NSTextView?
    private var currentDiagnostics: [TLADiagnostic] = []
    private var mappedDiagnostics: [MappedDiagnostic] = []

    // Custom underline attribute key
    private static let diagnosticKey = NSAttributedString.Key("TLADiagnostic")

    // MARK: - Initialization

    init(textView: NSTextView) {
        self.textView = textView
    }

    // MARK: - Public API

    /// Update diagnostics and apply underlines
    func updateDiagnostics(_ diagnostics: [TLADiagnostic], in text: String) {
        currentDiagnostics = diagnostics

        // Map diagnostics to text ranges
        mappedDiagnostics = diagnostics.compactMap { diagnostic in
            if let range = calculateRange(for: diagnostic, in: text) {
                return MappedDiagnostic(diagnostic: diagnostic, range: range)
            }
            return nil
        }

        // Apply underlines
        applyUnderlines()
    }

    /// Clear all diagnostic underlines
    func clearDiagnostics() {
        guard let textView = textView,
              let textStorage = textView.textStorage,
              textStorage.length > 0 else { return }

        let fullRange = NSRange(location: 0, length: textStorage.length)

        textStorage.beginEditing()
        textStorage.removeAttribute(.underlineStyle, range: fullRange)
        textStorage.removeAttribute(.underlineColor, range: fullRange)
        textStorage.removeAttribute(Self.diagnosticKey, range: fullRange)
        textStorage.removeAttribute(.toolTip, range: fullRange)
        textStorage.endEditing()

        currentDiagnostics = []
        mappedDiagnostics = []
    }

    /// Get diagnostic at a character index (for hover tooltips)
    func diagnostic(at characterIndex: Int) -> TLADiagnostic? {
        for mapped in mappedDiagnostics {
            if NSLocationInRange(characterIndex, mapped.range) {
                return mapped.diagnostic
            }
        }
        return nil
    }

    /// Get all diagnostics at a line
    func diagnostics(atLine line: Int) -> [TLADiagnostic] {
        currentDiagnostics.filter { Int($0.range.start.line) == line }
    }

    // MARK: - Private Methods

    private func calculateRange(for diagnostic: TLADiagnostic, in text: String) -> NSRange? {
        let lines = text.components(separatedBy: "\n")
        let startLine = Int(diagnostic.range.start.line)
        let startColumn = Int(diagnostic.range.start.column)
        let endLine = Int(diagnostic.range.end.line)
        let endColumn = Int(diagnostic.range.end.column)

        guard startLine < lines.count else { return nil }

        // Calculate start offset
        var startOffset = 0
        for i in 0..<startLine {
            startOffset += lines[i].count + 1 // +1 for newline
        }
        startOffset += min(startColumn, lines[startLine].count)

        // Calculate end offset
        var endOffset = 0
        let effectiveEndLine = min(endLine, lines.count - 1)
        for i in 0..<effectiveEndLine {
            endOffset += lines[i].count + 1
        }
        if effectiveEndLine < lines.count {
            endOffset += min(endColumn, lines[effectiveEndLine].count)
        }

        // Ensure end is after start and within bounds
        if endOffset <= startOffset {
            // Single point diagnostic - highlight the word or at least one character
            let lineLength = lines[startLine].count
            if startColumn < lineLength {
                // Find word boundary
                let lineStr = lines[startLine]
                var wordEnd = startColumn
                let chars = Array(lineStr)
                while wordEnd < chars.count && chars[wordEnd].isLetter || chars[wordEnd].isNumber || chars[wordEnd] == "_" {
                    wordEnd += 1
                }
                endOffset = startOffset + max(1, wordEnd - startColumn)
            } else {
                endOffset = startOffset + 1
            }
        }

        let length = min(endOffset - startOffset, text.count - startOffset)
        guard length > 0 else { return nil }

        return NSRange(location: startOffset, length: length)
    }

    private func applyUnderlines() {
        guard let textView = textView,
              let textStorage = textView.textStorage,
              textStorage.length > 0 else { return }

        textStorage.beginEditing()

        // First, clear existing diagnostic attributes
        let fullRange = NSRange(location: 0, length: textStorage.length)
        textStorage.removeAttribute(.underlineStyle, range: fullRange)
        textStorage.removeAttribute(.underlineColor, range: fullRange)
        textStorage.removeAttribute(Self.diagnosticKey, range: fullRange)
        textStorage.removeAttribute(.toolTip, range: fullRange)

        // Apply underlines for each diagnostic
        for mapped in mappedDiagnostics {
            guard mapped.range.location >= 0,
                  mapped.range.location + mapped.range.length <= textStorage.length else {
                continue
            }

            let color = underlineColor(for: mapped.diagnostic.severity)
            let style = underlineStyle(for: mapped.diagnostic.severity)

            textStorage.addAttribute(.underlineStyle, value: style.rawValue, range: mapped.range)
            textStorage.addAttribute(.underlineColor, value: color, range: mapped.range)
            textStorage.addAttribute(Self.diagnosticKey, value: mapped.diagnostic.id.uuidString, range: mapped.range)
            textStorage.addAttribute(.toolTip, value: mapped.diagnostic.message, range: mapped.range)
        }

        textStorage.endEditing()
    }

    private func underlineColor(for severity: TLADiagnosticSeverity) -> NSColor {
        switch severity {
        case .error:
            return NSColor.systemRed
        case .warning:
            return NSColor.systemOrange
        case .information:
            return NSColor.systemBlue
        case .hint:
            return NSColor.systemGreen
        }
    }

    private func underlineStyle(for severity: TLADiagnosticSeverity) -> NSUnderlineStyle {
        switch severity {
        case .error:
            // Thick dotted line to simulate wavy underline
            return [.single, .patternDot, .thick]
        case .warning:
            return [.single, .patternDot]
        case .information:
            return [.single, .patternDash]
        case .hint:
            return [.single, .patternDashDot]
        }
    }
}

// MARK: - Squiggle Drawing

/// Extension to draw custom squiggly underlines
extension NSLayoutManager {

    /// Draw a squiggly underline in the given rect
    func drawSquigglyUnderline(in rect: NSRect, color: NSColor) {
        let path = NSBezierPath()
        let waveHeight: CGFloat = 2.0
        let waveLength: CGFloat = 4.0

        var x = rect.minX
        let y = rect.maxY - 1 // Position at bottom of rect

        path.move(to: NSPoint(x: x, y: y))

        var goingUp = true
        while x < rect.maxX {
            x += waveLength / 2
            let newY = y + (goingUp ? -waveHeight : waveHeight)
            path.line(to: NSPoint(x: min(x, rect.maxX), y: newY))
            goingUp.toggle()
        }

        color.setStroke()
        path.lineWidth = 1.0
        path.stroke()
    }
}
