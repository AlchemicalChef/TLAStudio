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

    /// Maximum allowed buffer size before truncation
    let maxBufferSize: Int

    /// Compact when consumed portion exceeds this threshold
    let compactionThreshold: Int

    /// Append data, extract complete lines, and compact if needed.
    ///
    /// Returns an array of complete line `Data` segments (without the `\n` delimiter).
    /// Any incomplete trailing line remains in the buffer for the next call.
    mutating func append(_ data: Data) -> [Data] {
        // Check buffer size BEFORE appending to prevent unbounded growth
        if buffer.count + data.count > maxBufferSize {
            // Keep last compactionThreshold bytes to avoid losing partial line at end
            let keepBytes = min(buffer.count, compactionThreshold)
            buffer = Data(buffer.suffix(keepBytes))
            bufferOffset = 0
        }

        buffer.append(data)

        var lines: [Data] = []

        // Extract complete lines using index tracking (zero-copy until compaction)
        while let newlineIndex = buffer[bufferOffset...].firstIndex(of: UInt8(ascii: "\n")) {
            let lineData = Data(buffer[bufferOffset..<newlineIndex])
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
