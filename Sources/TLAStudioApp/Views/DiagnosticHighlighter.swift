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
        let textAnalysis = TextCoordinateMapper.analyze(text)

        // Map diagnostics to text ranges
        mappedDiagnostics = diagnostics.compactMap { diagnostic in
            if let range = Self.mappedRange(for: diagnostic, in: text, analysis: textAnalysis) {
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

    /// All diagnostics whose mapped range contains the UTF-16 character index.
    /// Static so hover handling outside the editor coordinator (EditorArea)
    /// can resolve diagnostics without the highlighter instance; the text is
    /// analyzed once for the whole batch.
    static func diagnostics(
        at characterIndex: Int,
        in diagnostics: [TLADiagnostic],
        text: String
    ) -> [TLADiagnostic] {
        guard !diagnostics.isEmpty else { return [] }
        let analysis = TextCoordinateMapper.analyze(text)
        return diagnostics.filter { diagnostic in
            guard let range = mappedRange(for: diagnostic, in: text, analysis: analysis) else {
                return false
            }
            return NSLocationInRange(characterIndex, range)
        }
    }

    // MARK: - Private Methods

    static func mappedRange(for diagnostic: TLADiagnostic, in text: String) -> NSRange? {
        mappedRange(for: diagnostic, in: text, analysis: TextCoordinateMapper.analyze(text))
    }

    private static func mappedRange(
        for diagnostic: TLADiagnostic,
        in text: String,
        analysis: TextCoordinateMapper.TextAnalysis
    ) -> NSRange? {
        let startLine = Int(diagnostic.range.start.line)
        let startColumn = Int(diagnostic.range.start.column)
        let endLine = Int(diagnostic.range.end.line)
        let endColumn = Int(diagnostic.range.end.column)
        let lineCount = analysis.lineStartOffsets.count

        guard startLine >= 0, startLine < lineCount else { return nil }
        guard analysis.utf16Length >= 0 else { return nil }

        let startOffset = TextCoordinateMapper.utf16Offset(
            forLine: startLine,
            column: startColumn,
            in: text,
            lineStartOffsets: analysis.lineStartOffsets
        )
        let effectiveEndLine = max(startLine, min(endLine, lineCount - 1))
        var endOffset = TextCoordinateMapper.utf16Offset(
            forLine: effectiveEndLine,
            column: endColumn,
            in: text,
            lineStartOffsets: analysis.lineStartOffsets
        )

        if endOffset <= startOffset {
            endOffset = fallbackEndOffset(
                from: startOffset,
                line: startLine,
                column: startColumn,
                in: text,
                analysis: analysis
            )
        }

        let maxLength = max(0, analysis.utf16Length - startOffset)
        let length = min(endOffset - startOffset, maxLength)
        guard length > 0 else { return nil }

        return NSRange(location: startOffset, length: length)
    }

    private static func fallbackEndOffset(
        from startOffset: Int,
        line: Int,
        column: Int,
        in text: String,
        analysis: TextCoordinateMapper.TextAnalysis
    ) -> Int {
        guard startOffset < analysis.utf16Length else {
            return startOffset
        }

        let lineRange = utf16LineRange(for: line, in: analysis)
        let lineText = (text as NSString).substring(with: lineRange)
        let localColumn = TextCoordinateMapper.lineAndColumn(
            forUTF16Offset: startOffset,
            in: text,
            lineStartOffsets: analysis.lineStartOffsets
        ).column

        let characters = Array(lineText)
        guard localColumn < characters.count else {
            return min(startOffset + 1, analysis.utf16Length)
        }

        var wordEnd = localColumn
        while wordEnd < characters.count {
            let character = characters[wordEnd]
            guard character.isLetter || character.isNumber || character == "_" else { break }
            wordEnd += 1
        }

        let highlightedColumns = max(1, wordEnd - localColumn)
        let candidateEnd = TextCoordinateMapper.utf16Offset(
            forLine: line,
            column: column + highlightedColumns,
            in: text,
            lineStartOffsets: analysis.lineStartOffsets
        )
        return max(startOffset + 1, candidateEnd)
    }

    private static func utf16LineRange(
        for line: Int,
        in analysis: TextCoordinateMapper.TextAnalysis
    ) -> NSRange {
        let start = analysis.lineStartOffsets[line]
        let end: Int
        if line + 1 < analysis.lineStartOffsets.count {
            end = max(start, analysis.lineStartOffsets[line + 1] - 1)
        } else {
            end = analysis.utf16Length
        }
        return NSRange(location: start, length: max(0, end - start))
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
            // No .toolTip attribute: the hover popover shows diagnostics now,
            // and the system tooltip would double-report on top of it.
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
