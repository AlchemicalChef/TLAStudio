import Foundation

/// Reusable line-oriented buffer for parsing process output.
///
/// Handles appending raw data, extracting complete lines (delimited by `\n`),
/// offset-based compaction to avoid O(n^2) copies, and overflow protection.
///
/// Both `TLCOutputParser` and `TLAPMOutputParser` use this to eliminate
/// duplicated buffer management code.
struct LineBuffer {
    private(set) var buffer = Data()
    private(set) var bufferOffset: Int = 0

    /// Best-effort compaction trigger.
    ///
    /// When `buffer.count + incoming.count` would exceed this size AND some prefix
    /// has already been consumed (`bufferOffset > 0`), the buffer is compacted to
    /// drop the consumed prefix before appending. This is intentionally a soft
    /// limit, not a hard cap: an in-progress single line that has not yet seen a
    /// `\n` will be preserved even if it exceeds this size, because TLC can emit
    /// a multi-megabyte JSON trace as one line and losing the prefix would render
    /// the whole trace unparsable. Callers needing a hard byte ceiling must
    /// enforce it externally.
    let maxBufferSize: Int

    /// Compact when consumed portion exceeds this threshold
    let compactionThreshold: Int

    /// Append data, extract complete lines, and compact if needed.
    ///
    /// Returns an array of complete line `Data` segments (without the `\n`
    /// delimiter; a trailing `\r` from CRLF-delimited output is also stripped).
    /// Any incomplete trailing line remains in the buffer for the next call.
    mutating func append(_ data: Data) -> [Data] {
        // Best-effort compaction: drop the already-consumed prefix when the buffer
        // would otherwise exceed `maxBufferSize`. Intentionally does NOT truncate
        // an active partial line — TLC can emit a large JSON trace as one line and
        // losing the prefix makes the whole trace unparsable. See `maxBufferSize`.
        if buffer.count + data.count > maxBufferSize, bufferOffset > 0 {
            buffer = Data(buffer[bufferOffset...])
            bufferOffset = 0
        }

        buffer.append(data)

        var lines: [Data] = []

        // Extract complete lines using index tracking (zero-copy until compaction)
        while let newlineIndex = buffer[bufferOffset...].firstIndex(of: UInt8(ascii: "\n")) {
            // Strip one trailing \r so CRLF-delimited output parses like LF.
            var lineEnd = newlineIndex
            if lineEnd > bufferOffset, buffer[buffer.index(before: lineEnd)] == UInt8(ascii: "\r") {
                lineEnd = buffer.index(before: lineEnd)
            }
            let lineData = Data(buffer[bufferOffset..<lineEnd])
            bufferOffset = buffer.index(after: newlineIndex)
            lines.append(lineData)
        }

        // Compact buffer after processing all complete lines
        compactIfNeeded()

        return lines
    }

    /// Reset all buffer state.
    mutating func reset() {
        buffer = Data()
        bufferOffset = 0
    }

    /// Compact buffer when offset exceeds threshold to prevent memory growth.
    private mutating func compactIfNeeded() {
        if bufferOffset > compactionThreshold {
            buffer = Data(buffer[bufferOffset...])
            bufferOffset = 0
        }
    }
}
