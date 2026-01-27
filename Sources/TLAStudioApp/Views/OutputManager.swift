import Foundation
import Combine

// MARK: - Output Manager

/// Manages output logging from various sources (TLC, TLAPM, Parser, etc.)
final class OutputManager: ObservableObject {

    // MARK: - Types

    enum OutputSource: String, CaseIterable {
        case tlc = "TLC"
        case tlapm = "TLAPM"
        case parser = "Parser"
        case system = "System"
    }

    struct OutputEntry: Identifiable {
        let id = UUID()
        let timestamp: Date
        let source: OutputSource
        let message: String
        let isError: Bool

        var formattedTimestamp: String {
            let formatter = DateFormatter()
            formatter.dateFormat = "HH:mm:ss"
            return formatter.string(from: timestamp)
        }
    }

    // MARK: - Singleton

    static let shared = OutputManager()

    // MARK: - Published Properties

    @Published private(set) var entries: [OutputEntry] = []
    @Published var selectedSource: OutputSource? = nil
    @Published var showErrorsOnly: Bool = false

    // MARK: - Computed Properties

    var filteredEntries: [OutputEntry] {
        var result = entries

        if let source = selectedSource {
            result = result.filter { $0.source == source }
        }

        if showErrorsOnly {
            result = result.filter { $0.isError }
        }

        return result
    }

    // MARK: - Private

    private let maxEntries = 5000
    private let queue = DispatchQueue(label: "com.tlastudio.outputmanager")

    // Batching state for ~60fps UI updates
    private var pendingEntries: [OutputEntry] = []
    private var batchFlushScheduled = false
    private let batchInterval: TimeInterval = 0.016  // ~60fps

    // MARK: - Initialization

    private init() {}

    // MARK: - Public API

    /// Log a message from a source (batched for performance)
    func log(_ message: String, source: OutputSource, isError: Bool = false) {
        let entry = OutputEntry(
            timestamp: Date(),
            source: source,
            message: message,
            isError: isError
        )

        queue.async { [weak self] in
            self?.queueEntry(entry)
        }
    }

    /// Log multiple lines from a source (efficient batch operation)
    func logLines(_ lines: [String], source: OutputSource, isError: Bool = false) {
        let timestamp = Date()
        let newEntries = lines.compactMap { line -> OutputEntry? in
            guard !line.isEmpty else { return nil }
            return OutputEntry(timestamp: timestamp, source: source, message: line, isError: isError)
        }

        guard !newEntries.isEmpty else { return }

        queue.async { [weak self] in
            self?.queueEntries(newEntries)
        }
    }

    /// Log a batch of messages at once (most efficient for high-volume output)
    func logBatch(_ messages: [String], source: OutputSource, isError: Bool = false) {
        logLines(messages, source: source, isError: isError)
    }

    /// Clear all entries
    func clear() {
        entries.removeAll()
    }

    /// Clear entries from a specific source
    func clear(source: OutputSource) {
        entries.removeAll { $0.source == source }
    }

    // MARK: - Private Methods

    /// Queue a single entry for batched flush
    private func queueEntry(_ entry: OutputEntry) {
        dispatchPrecondition(condition: .onQueue(queue))
        pendingEntries.append(entry)
        scheduleBatchFlush()
    }

    /// Queue multiple entries for batched flush
    private func queueEntries(_ newEntries: [OutputEntry]) {
        dispatchPrecondition(condition: .onQueue(queue))
        pendingEntries.append(contentsOf: newEntries)
        scheduleBatchFlush()
    }

    /// Schedule a batched flush to main queue at ~60fps
    private func scheduleBatchFlush() {
        dispatchPrecondition(condition: .onQueue(queue))
        guard !batchFlushScheduled else { return }
        batchFlushScheduled = true

        queue.asyncAfter(deadline: .now() + batchInterval) { [weak self] in
            self?.flushBatch()
        }
    }

    /// Flush all pending entries to the main queue
    private func flushBatch() {
        dispatchPrecondition(condition: .onQueue(queue))
        batchFlushScheduled = false
        guard !pendingEntries.isEmpty else { return }

        let entriesToFlush = pendingEntries
        pendingEntries.removeAll(keepingCapacity: true)

        DispatchQueue.main.async { [weak self] in
            self?.addEntries(entriesToFlush)
        }
    }

    /// Add entries to the published array (called on main queue)
    private func addEntries(_ newEntries: [OutputEntry]) {
        entries.append(contentsOf: newEntries)

        // Trim old entries if needed
        if entries.count > maxEntries {
            entries.removeFirst(entries.count - maxEntries)
        }
    }

    private func addEntry(_ entry: OutputEntry) {
        entries.append(entry)

        // Trim old entries if needed
        if entries.count > maxEntries {
            entries.removeFirst(entries.count - maxEntries)
        }
    }
}

// MARK: - Convenience Extensions

extension OutputManager {

    func logTLC(_ message: String, isError: Bool = false) {
        log(message, source: .tlc, isError: isError)
    }

    func logTLAPM(_ message: String, isError: Bool = false) {
        log(message, source: .tlapm, isError: isError)
    }

    func logParser(_ message: String, isError: Bool = false) {
        log(message, source: .parser, isError: isError)
    }

    func logSystem(_ message: String, isError: Bool = false) {
        log(message, source: .system, isError: isError)
    }
}
