import Foundation

/// Thread-safe byte accumulator for subprocess output with a configurable
/// truncation policy.
///
/// Consolidates three previously-divergent implementations (D1 in the 2026-06-10
/// reuse review):
/// - `SubprocessRunner` (java tooling): bounded, **keep head** — anything past the
///   cap is almost certainly a pathological loop; the interesting output is at the start.
/// - `TLAPMProcessManager.checkSingleStep`: bounded, **keep tail** — the latest
///   obligation results matter, older output may be discarded.
/// - `GraphvizProcessManager`: **unbounded** — a rendered state-graph SVG/PDF on
///   stdout can legitimately exceed any reasonable cap; truncation would corrupt it.
///
/// The policy is a parameter on purpose: forcing one truncation policy on all
/// subprocess captures would be a regression dressed as cleanup (reuse review O5).
///
/// `@unchecked Sendable`: thread safety ensured by NSLock. Callers typically
/// append from pipe `readabilityHandler` threads and `snapshot()` once the
/// process has exited and handlers are cleared.
final class BoundedOutputAccumulator: @unchecked Sendable {

    /// What to do when accumulated bytes would exceed the cap.
    enum TruncationPolicy: Sendable {
        /// Keep the first `limit` bytes; drop everything after the cap is reached.
        case keepHead(limit: Int)
        /// Keep the most recent `limit` bytes; older data is discarded as new data arrives.
        case keepTail(limit: Int)
        /// No cap. Only for streams whose payload is legitimately large (e.g. Graphviz
        /// SVG/PDF render output) — do not use for chatty diagnostic streams.
        case unbounded
    }

    private let lock = NSLock()
    private var buffer = Data()
    private let policy: TruncationPolicy

    init(policy: TruncationPolicy) {
        self.policy = policy
    }

    func append(_ data: Data) {
        lock.lock()
        defer { lock.unlock() }
        switch policy {
        case .keepHead(let limit):
            guard buffer.count < limit else { return }
            buffer.append(data.prefix(limit - buffer.count))
        case .keepTail(let limit):
            buffer.append(data)
            if buffer.count > limit {
                buffer = Data(buffer.suffix(limit))
            }
        case .unbounded:
            buffer.append(data)
        }
    }

    /// The accumulated buffer. Safe to call at any time; for a complete capture,
    /// call after the process has exited and residual pipe data has been drained.
    func snapshot() -> Data {
        lock.lock()
        defer { lock.unlock() }
        return buffer
    }
}
