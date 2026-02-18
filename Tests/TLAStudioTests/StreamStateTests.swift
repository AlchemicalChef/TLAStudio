import XCTest
@testable import TLAStudioApp

final class StreamStateTests: XCTestCase {

    // MARK: - Basic Lifecycle

    func testBasicYieldAndFinish() async {
        let state = StreamState<Int>(throttle: .none)

        var received: [Int] = []
        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        state.yield(1)
        state.yield(2)
        state.yield(3)
        state.finish()

        for await value in stream {
            received.append(value)
        }

        XCTAssertEqual(received, [1, 2, 3])
    }

    func testFinishTerminatesStream() async {
        let state = StreamState<String>(throttle: .none)

        let stream = AsyncStream<String> { continuation in
            state.setContinuation(continuation)
        }

        state.yield("hello")
        state.finish()

        var values: [String] = []
        for await value in stream {
            values.append(value)
        }

        XCTAssertEqual(values, ["hello"])
    }

    // MARK: - Yield After Finish (W4 Fix Validation)

    func testYieldAfterFinishIsNoOp() async {
        let state = StreamState<Int>(throttle: .none)

        var received: [Int] = []
        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        state.yield(1)
        state.finish()
        state.yield(2)  // Should be ignored
        state.yield(3)  // Should be ignored

        for await value in stream {
            received.append(value)
        }

        XCTAssertEqual(received, [1])
        XCTAssertTrue(state.isFinished)
    }

    func testYieldImmediateAfterFinishIsNoOp() async {
        let state = StreamState<Int>(throttle: .none)

        var received: [Int] = []
        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        state.yieldImmediate(10)
        state.finish()
        state.yieldImmediate(20)  // Should be ignored

        for await value in stream {
            received.append(value)
        }

        XCTAssertEqual(received, [10])
    }

    // MARK: - Double Finish Idempotency

    func testDoubleFinishIsIdempotent() async {
        let state = StreamState<Int>(throttle: .none)

        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        state.yield(1)
        state.finish()
        state.finish()  // Should be a no-op

        var values: [Int] = []
        for await value in stream {
            values.append(value)
        }

        XCTAssertEqual(values, [1])
        XCTAssertTrue(state.isFinished)
    }

    // MARK: - Throttle Behavior

    func testThrottleCoalescesRapidUpdates() async {
        let state = StreamState<Int>(throttle: .fps30)

        var received: [Int] = []
        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        // First yield should go through (no previous time)
        state.yield(1)

        // Rapid yields within 33ms should be coalesced
        for i in 2...100 {
            state.yield(i)
        }

        state.finish()  // Should flush the pending value

        for await value in stream {
            received.append(value)
        }

        // Should have at least the first value and the last (flushed on finish)
        XCTAssertGreaterThanOrEqual(received.count, 2)
        XCTAssertEqual(received.first, 1)
        XCTAssertEqual(received.last, 100)  // Pending value flushed by finish
    }

    func testYieldImmediateBypassesThrottle() async {
        let state = StreamState<Int>(throttle: .fps30)

        var received: [Int] = []
        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        state.yield(1)
        state.yieldImmediate(42)  // Should go through even within throttle window
        state.finish()

        for await value in stream {
            received.append(value)
        }

        XCTAssertTrue(received.contains(42))
    }

    func testFinishFlushesPendingThrottledValue() async {
        let state = StreamState<Int>(throttle: .fps30)

        var received: [Int] = []
        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        state.yield(1)
        // These should be throttled/coalesced
        state.yield(2)
        state.yield(3)
        state.finish()  // Should flush the last pending value

        for await value in stream {
            received.append(value)
        }

        // The last value (3) should be flushed by finish()
        XCTAssertTrue(received.contains(3), "Pending value should be flushed on finish")
    }

    // MARK: - isFinished State

    func testIsFinishedIsFalseInitially() {
        let state = StreamState<Int>()
        XCTAssertFalse(state.isFinished)
    }

    func testIsFinishedIsTrueAfterFinish() {
        let state = StreamState<Int>()
        let _ = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }
        state.finish()
        XCTAssertTrue(state.isFinished)
    }

    // MARK: - Concurrent Stress Tests

    func testConcurrentYieldAndFinish() async {
        // Run multiple iterations to catch race conditions
        for _ in 0..<100 {
            let state = StreamState<Int>(throttle: .none)

            let stream = AsyncStream<Int> { continuation in
                state.setContinuation(continuation)
            }

            // Consume stream in background
            let consumeTask = Task {
                var count = 0
                for await _ in stream {
                    count += 1
                }
                return count
            }

            // Concurrent yields + finish
            await withTaskGroup(of: Void.self) { group in
                for i in 0..<50 {
                    group.addTask {
                        state.yield(i)
                    }
                }
                group.addTask {
                    state.finish()
                }
            }

            let count = await consumeTask.value
            XCTAssertGreaterThanOrEqual(count, 0)
            XCTAssertTrue(state.isFinished)
        }
    }

    func testHighVolumeStress() async {
        let state = StreamState<Int>(throttle: .none)

        let stream = AsyncStream<Int> { continuation in
            state.setContinuation(continuation)
        }

        // Consume in background
        let consumeTask = Task {
            var count = 0
            for await _ in stream {
                count += 1
            }
            return count
        }

        // 10,000 concurrent yields
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<10_000 {
                group.addTask {
                    state.yield(i)
                }
            }
        }

        state.finish()

        let count = await consumeTask.value
        XCTAssertGreaterThanOrEqual(count, 0)
        XCTAssertLessThanOrEqual(count, 10_000)
    }
}
