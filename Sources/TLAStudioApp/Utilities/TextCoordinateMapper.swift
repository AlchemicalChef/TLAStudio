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

// MARK: - Tree-sitter (byte-column) Conversion

extension TextCoordinateMapper {

    /// Converts tree-sitter positions — (row, **byte** column) — to UTF-16
    /// offsets and `NSRange`s.
    ///
    /// tree-sitter reports columns in UTF-8 bytes while AppKit ranges are
    /// UTF-16 code units; treating byte columns as character or UTF-16 columns
    /// is only correct for ASCII. Build one converter per text and reuse it for
    /// batch conversions — construction walks the whole UTF-8 view once to
    /// build line tables.
    struct TreeSitterRangeConverter {
        private let text: String
        private let utf16Length: Int
        private let lineStartsUTF8: [Int]
        private let lineStartsUTF16: [Int]

        init(text: String) {
            self.text = text
            self.utf16Length = (text as NSString).length

            let utf8 = text.utf8
            var lineStartsUTF8: [Int] = [0]
            var lineStartsUTF16: [Int] = [0]
            var utf16Offset = 0

            for (byteIndex, byte) in utf8.enumerated() {
                if byte == 0x0A {
                    utf16Offset += 1
                    lineStartsUTF8.append(byteIndex + 1)
                    lineStartsUTF16.append(utf16Offset)
                } else if byte & 0xC0 != 0x80 {
                    // Lead byte: 1 UTF-16 unit, except 4-byte sequences
                    // (code points above the BMP) which need a surrogate pair.
                    utf16Offset += byte < 0xF0 ? 1 : 2
                }
            }

            self.lineStartsUTF8 = lineStartsUTF8
            self.lineStartsUTF16 = lineStartsUTF16
        }

        /// UTF-16 offset for a tree-sitter point, or nil when the line is out
        /// of bounds. A byte column past the end of the line clamps to the
        /// line's end (mirrors tree-sitter's own clamping on edits).
        func utf16Offset(line: Int, byteColumn: Int) -> Int? {
            guard line >= 0,
                  line < lineStartsUTF8.count,
                  line < lineStartsUTF16.count else {
                return nil
            }

            let utf8 = text.utf8
            let lineByteStart = lineStartsUTF8[line]
            let lineUTF16Start = lineStartsUTF16[line]
            guard let startIndex = utf8.index(
                utf8.startIndex,
                offsetBy: lineByteStart,
                limitedBy: utf8.endIndex
            ) else {
                return nil
            }

            var bytesConsumed = 0
            var utf16Count = 0
            var index = startIndex

            while bytesConsumed < byteColumn && index < utf8.endIndex {
                let byte = utf8[index]
                if byte == 0x0A { break }

                let characterByteLength: Int
                let characterUTF16Length: Int
                if byte < 0x80 {
                    characterByteLength = 1
                    characterUTF16Length = 1
                } else if byte < 0xE0 {
                    characterByteLength = 2
                    characterUTF16Length = 1
                } else if byte < 0xF0 {
                    characterByteLength = 3
                    characterUTF16Length = 1
                } else {
                    characterByteLength = 4
                    characterUTF16Length = 2
                }

                bytesConsumed += characterByteLength
                utf16Count += characterUTF16Length
                index = utf8.index(index, offsetBy: characterByteLength, limitedBy: utf8.endIndex) ?? utf8.endIndex
            }

            return lineUTF16Start + utf16Count
        }

        /// UTF-16 `NSRange` for a tree-sitter range, or nil when out of bounds
        /// or inverted. Zero-length ranges are valid.
        func utf16Range(for range: TLARange) -> NSRange? {
            guard let start = utf16Offset(line: Int(range.start.line), byteColumn: Int(range.start.column)),
                  let end = utf16Offset(line: Int(range.end.line), byteColumn: Int(range.end.column)),
                  start <= utf16Length,
                  end <= utf16Length,
                  end >= start else {
                return nil
            }
            return NSRange(location: start, length: end - start)
        }
    }

    /// One-shot convenience; prefer building a `TreeSitterRangeConverter` for
    /// batch conversions.
    static func utf16Range(forTreeSitterRange range: TLARange, in text: String) -> NSRange? {
        TreeSitterRangeConverter(text: text).utf16Range(for: range)
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
