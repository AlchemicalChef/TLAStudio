import XCTest
@testable import TLAStudioApp

final class LineBufferTests: XCTestCase {

    // MARK: - Basic Line Extraction

    func testBasicLineExtraction() {
        var buf = LineBuffer(maxBufferSize: 1024, compactionThreshold: 256)
        let data = "hello\nworld\n".data(using: .utf8)!
        let lines = buf.append(data)

        XCTAssertEqual(lines.count, 2)
        XCTAssertEqual(String(data: lines[0], encoding: .utf8), "hello")
        XCTAssertEqual(String(data: lines[1], encoding: .utf8), "world")
    }

    func testPartialLineBuffering() {
        var buf = LineBuffer(maxBufferSize: 1024, compactionThreshold: 256)

        // First chunk has no newline — should return nothing
        let lines1 = buf.append("partial".data(using: .utf8)!)
        XCTAssertTrue(lines1.isEmpty)

        // Second chunk completes the line
        let lines2 = buf.append(" line\n".data(using: .utf8)!)
        XCTAssertEqual(lines2.count, 1)
        XCTAssertEqual(String(data: lines2[0], encoding: .utf8), "partial line")
    }

    func testMultiLineChunk() {
        var buf = LineBuffer(maxBufferSize: 4096, compactionThreshold: 512)
        let data = "line1\nline2\nline3\nline4\n".data(using: .utf8)!
        let lines = buf.append(data)

        XCTAssertEqual(lines.count, 4)
        XCTAssertEqual(String(data: lines[0], encoding: .utf8), "line1")
        XCTAssertEqual(String(data: lines[3], encoding: .utf8), "line4")
    }

    func testEmptyInput() {
        var buf = LineBuffer(maxBufferSize: 1024, compactionThreshold: 256)
        let lines = buf.append(Data())
        XCTAssertTrue(lines.isEmpty)
    }

    func testNewlineOnlyInput() {
        var buf = LineBuffer(maxBufferSize: 1024, compactionThreshold: 256)
        let lines = buf.append("\n\n\n".data(using: .utf8)!)

        // Three newlines produce three empty lines
        XCTAssertEqual(lines.count, 3)
        for line in lines {
            XCTAssertTrue(line.isEmpty)
        }
    }

    // MARK: - Overflow Truncation

    func testOverflowTruncation() {
        let maxSize = 100
        let threshold = 20
        var buf = LineBuffer(maxBufferSize: maxSize, compactionThreshold: threshold)

        // Fill with data just under the limit
        let chunk1 = String(repeating: "a", count: 80) + "\n"
        _ = buf.append(chunk1.data(using: .utf8)!)

        // Now append data that would exceed the limit
        let chunk2 = String(repeating: "b", count: 50) + "\n"
        let lines = buf.append(chunk2.data(using: .utf8)!)

        // Should still produce a line (the 'b' line)
        XCTAssertFalse(lines.isEmpty)
        // Buffer should not exceed maxSize at any point
        XCTAssertLessThanOrEqual(buf.buffer.count, maxSize)
    }

    // MARK: - Compaction

    func testCompactionTrigger() {
        let threshold = 32
        var buf = LineBuffer(maxBufferSize: 4096, compactionThreshold: threshold)

        // Feed enough complete lines to push bufferOffset past threshold
        let lineData = String(repeating: "x", count: 20) + "\n"
        for _ in 0..<5 {
            _ = buf.append(lineData.data(using: .utf8)!)
        }

        // After compaction, bufferOffset should be small
        XCTAssertLessThanOrEqual(buf.bufferOffset, threshold)
    }

    // MARK: - Reset

    func testReset() {
        var buf = LineBuffer(maxBufferSize: 1024, compactionThreshold: 256)
        _ = buf.append("some data\n".data(using: .utf8)!)
        _ = buf.append("more partial".data(using: .utf8)!)

        buf.reset()

        XCTAssertTrue(buf.buffer.isEmpty)
        XCTAssertEqual(buf.bufferOffset, 0)

        // Should work cleanly after reset
        let lines = buf.append("after reset\n".data(using: .utf8)!)
        XCTAssertEqual(lines.count, 1)
        XCTAssertEqual(String(data: lines[0], encoding: .utf8), "after reset")
    }

    // MARK: - Incremental Appends

    func testIncrementalByteByByte() {
        var buf = LineBuffer(maxBufferSize: 1024, compactionThreshold: 256)
        var allLines: [Data] = []
        let message = "hello\n"

        for byte in message.utf8 {
            let lines = buf.append(Data([byte]))
            allLines.append(contentsOf: lines)
        }

        XCTAssertEqual(allLines.count, 1)
        XCTAssertEqual(String(data: allLines[0], encoding: .utf8), "hello")
    }
}
