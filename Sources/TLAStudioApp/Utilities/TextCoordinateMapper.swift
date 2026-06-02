import AppKit
import Foundation

/// Converts between AppKit UTF-16 offsets and logical line/column positions.
///
/// `NSTextView` and `NSRange` operate in UTF-16 code units, while most document-facing
/// logic in the app expects line/column pairs measured in visible Swift characters.
///
/// **Column semantics**: `column` is the count of Swift `Character` (grapheme cluster) elements
/// on the line before the target offset — *not* UTF-16 code units and *not* bytes. Two
/// consequences:
///   - An emoji or combining sequence that spans multiple UTF-16 units counts as a single column.
///   - External tools that expect UTF-16 or byte columns (e.g. raw LSP messages, TLC/TLAPM
///     error locations) need a separate conversion. Before passing a column to an external
///     tool, confirm which unit the tool expects and convert if necessary.
enum TextCoordinateMapper {

    struct TextAnalysis {
        let lineStartOffsets: [Int]
        let utf16Length: Int
        let isASCII: Bool
    }

    static func analyze(_ text: String) -> TextAnalysis {
        let utf16View = text.utf16
        var offsets = [0]
        offsets.reserveCapacity(max(1, utf16View.count / 40 + 1))

        var utf16Length = 0
        var isASCII = true

        for codeUnit in utf16View {
            if codeUnit == 0x0A {
                offsets.append(utf16Length + 1)
            }
            if isASCII && codeUnit > 0x7F {
                isASCII = false
            }
            utf16Length += 1
        }

        return TextAnalysis(
            lineStartOffsets: offsets,
            utf16Length: utf16Length,
            isASCII: isASCII
        )
    }

    static func lineStartOffsets(in text: String) -> [Int] {
        analyze(text).lineStartOffsets
    }

    static func lineAndColumn(
        forUTF16Offset offset: Int,
        in text: String,
        lineStartOffsets: [Int]? = nil
    ) -> (line: Int, column: Int) {
        let nsText = text as NSString
        let cachedLineStarts = lineStartOffsets ?? self.lineStartOffsets(in: text)
        let clampedOffset = clampedUTF16Offset(offset, in: nsText)

        guard !cachedLineStarts.isEmpty else {
            return (0, 0)
        }

        let line = lineIndex(forUTF16Offset: clampedOffset, in: cachedLineStarts)
        let lineStart = cachedLineStarts[line]
        let prefixLength = max(0, clampedOffset - lineStart)
        let prefix = nsText.substring(with: NSRange(location: lineStart, length: prefixLength))

        return (line, prefix.count)
    }

    static func utf16Offset(
        forLine line: Int,
        column: Int,
        in text: String,
        lineStartOffsets: [Int]? = nil
    ) -> Int {
        let nsText = text as NSString
        let cachedLineStarts = lineStartOffsets ?? self.lineStartOffsets(in: text)

        guard !cachedLineStarts.isEmpty else {
            return 0
        }

        let clampedLine = max(0, line)
        guard clampedLine < cachedLineStarts.count else {
            return nsText.length
        }

        let lineStart = cachedLineStarts[clampedLine]
        let lineEnd = lineEndOffset(forLine: clampedLine, in: cachedLineStarts, textLength: nsText.length)
        let lineText = nsText.substring(with: NSRange(location: lineStart, length: max(0, lineEnd - lineStart)))
        let targetColumn = max(0, column)

        guard targetColumn > 0, !lineText.isEmpty else {
            return lineStart
        }

        var stringIndex = lineText.startIndex
        var currentColumn = 0

        while stringIndex < lineText.endIndex && currentColumn < targetColumn {
            stringIndex = lineText.index(after: stringIndex)
            currentColumn += 1
        }

        let consumedUTF16 = lineText[..<stringIndex].utf16.count
        return lineStart + consumedUTF16
    }

    static func position(forUTF16Offset offset: Int, in text: String) -> TLAPosition {
        let (line, column) = lineAndColumn(forUTF16Offset: offset, in: text)
        return TLAPosition(line: UInt32(line), column: UInt32(column))
    }

    static func lineCount(in text: String) -> Int {
        analyze(text).lineStartOffsets.count
    }

    private static func clampedUTF16Offset(_ offset: Int, in text: NSString) -> Int {
        max(0, min(offset, text.length))
    }

    static func lineIndex(forUTF16Offset offset: Int, in lineStartOffsets: [Int]) -> Int {
        var low = 0
        var high = lineStartOffsets.count - 1

        while low < high {
            let mid = (low + high + 1) / 2
            if lineStartOffsets[mid] <= offset {
                low = mid
            } else {
                high = mid - 1
            }
        }

        return low
    }

    private static func lineEndOffset(forLine line: Int, in lineStartOffsets: [Int], textLength: Int) -> Int {
        if line + 1 < lineStartOffsets.count {
            return max(lineStartOffsets[line], lineStartOffsets[line + 1] - 1)
        }

        return textLength
    }
}

// MARK: - SharedTextLineIndex

/// Reference-type cache of a text view's line-start UTF-16 offsets, shared
/// across overlay views (line-number gutter, folding gutter, proof gutter, …)
/// so they perform a single combined walk of the text per change instead of
/// one walk per overlay. See audit F-S6-editor-perf-006.
///
/// The owner (`EditorContainerView`) invalidates the cache when text changes;
/// individual overlays then read `offsets` lazily on their next draw. Overlays
/// must not mutate the cache directly.
///
/// This class is intentionally not thread-safe — all access happens on the main
/// thread alongside `NSTextView` updates.
final class SharedTextLineIndex {
    private weak var textView: NSTextView?
    private var cachedOffsets: [Int]?
    private var cachedLength: Int = -1

    init(textView: NSTextView) {
        self.textView = textView
    }

    /// Force a recompute on the next `offsets` access.
    /// Call this when the underlying text changes (or may have changed).
    func invalidate() {
        cachedOffsets = nil
        cachedLength = -1
    }

    /// UTF-16 offsets of the start of each line in the current text.
    /// Returns `[0]` when the text view is nil.
    var offsets: [Int] {
        guard let textView = textView else {
            return [0]
        }
        // Length check is a cheap belt-and-braces fallback in case some caller
        // forgot to call `invalidate()`; the canonical invalidation channel is
        // the explicit `invalidate()` call.
        let length = textView.textStorage?.length ?? (textView.string as NSString).length
        if let cached = cachedOffsets, cachedLength == length {
            return cached
        }
        let computed = TextCoordinateMapper.lineStartOffsets(in: textView.string)
        cachedOffsets = computed
        cachedLength = length
        return computed
    }
}
