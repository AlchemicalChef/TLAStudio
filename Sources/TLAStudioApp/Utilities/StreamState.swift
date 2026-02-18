import Foundation

// MARK: - Stream Throttle Configuration

struct StreamThrottleConfig {
    let interval: CFAbsoluteTime

    /// ~30fps throttle for high-frequency UI updates
    static let fps30 = StreamThrottleConfig(interval: 0.033)

    /// No throttling — every yield is delivered immediately
    static let none = StreamThrottleConfig(interval: 0)
}

// MARK: - Stream State

/// Generic thread-safe wrapper for AsyncStream continuation to prevent race conditions.
/// Guards against yielding after the stream has been finished, and optionally throttles
/// high-frequency updates to reduce UI overhead.
///
/// The race fix: `yield()` and `finish()` calls happen INSIDE the lock.
/// `AsyncStream.Continuation.yield()` is documented as non-blocking (enqueues into an
/// internal buffer), so holding the lock during yield is safe and eliminates the window
/// where `finish()` could execute between extracting the continuation and calling yield.
///
/// @unchecked Sendable: thread safety ensured by NSLock
final class StreamState<Value: Sendable>: @unchecked Sendable {

    // MARK: - State

    private let lock = NSLock()
    private var _continuation: AsyncStream<Value>.Continuation?
    private var _isFinished = false

    private let throttleInterval: CFAbsoluteTime
    private var lastYieldTime: CFAbsoluteTime = 0
    private var pendingUpdate: Value?

    // MARK: - Init

    init(throttle: StreamThrottleConfig = .none) {
        self.throttleInterval = throttle.interval
    }

    // MARK: - Public API

    var isFinished: Bool {
        lock.lock()
        defer { lock.unlock() }
        return _isFinished
    }

    func setContinuation(_ continuation: AsyncStream<Value>.Continuation) {
        lock.lock()
        defer { lock.unlock() }
        _continuation = continuation
    }

    /// Yield with optional throttling. High-frequency updates are coalesced;
    /// the latest pending value is flushed on the next interval or on `finish()`.
    func yield(_ value: Value) {
        lock.lock()
        defer { lock.unlock() }

        guard !_isFinished, let c = _continuation else { return }

        if throttleInterval <= 0 {
            // No throttle — yield immediately inside the lock
            c.yield(value)
            return
        }

        let now = CFAbsoluteTimeGetCurrent()
        if now - lastYieldTime >= throttleInterval {
            lastYieldTime = now
            pendingUpdate = nil
            c.yield(value)
        } else {
            // Store for flush on next interval or finish()
            pendingUpdate = value
        }
    }

    /// Yield immediately without throttling (for critical updates like errors).
    func yieldImmediate(_ value: Value) {
        lock.lock()
        defer { lock.unlock() }

        guard !_isFinished, let c = _continuation else { return }
        lastYieldTime = CFAbsoluteTimeGetCurrent()
        pendingUpdate = nil
        c.yield(value)
    }

    /// Flush any pending throttled value and finish the stream.
    /// Idempotent — safe to call multiple times.
    func finish() {
        lock.lock()
        defer { lock.unlock() }

        guard !_isFinished else { return }
        _isFinished = true

        let c = _continuation
        let pending = pendingUpdate
        pendingUpdate = nil
        _continuation = nil

        // Flush pending + finish inside the lock (both are non-blocking)
        if let pending = pending, let c = c {
            c.yield(pending)
        }
        c?.finish()
    }
}
