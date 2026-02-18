import Foundation
import os

// MARK: - Trace Storage Manager

/// Manages large error traces by streaming to disk when they exceed memory thresholds.
/// This prevents memory exhaustion when TLC produces counterexamples with thousands of states.
actor TraceStorageManager {
    static let shared = TraceStorageManager()

    private let logger = Log.logger(category: "TraceStorage")

    /// Threshold for streaming to disk (states count)
    private let streamingThreshold = 1000

    /// Page size for loading states
    private let pageSize = 100

    /// Directory for trace storage
    private let storageDirectory: URL

    /// Active trace files indexed by session ID
    private var traceFiles: [UUID: TraceFileHandle] = [:]

    /// Tracks active trace session IDs for cleanup during app termination
    private var activeTraceIds: Set<UUID> = []

    /// In-memory cache for recently accessed pages
    private var pageCache: LRUCache<PageKey, [TraceState]>

    private init() {
        // Create storage directory in app support
        // Use fallback to temp directory if app support is unavailable
        let appSupport = FileManager.default.urls(for: .applicationSupportDirectory, in: .userDomainMask).first
            ?? FileManager.default.temporaryDirectory
        storageDirectory = appSupport.appendingPathComponent("TLAStudio/Traces", isDirectory: true)

        try? FileManager.default.createDirectory(at: storageDirectory, withIntermediateDirectories: true)

        // Initialize LRU cache with 50 pages (5000 states max in memory)
        pageCache = LRUCache(capacity: 50)
    }

    // MARK: - Public API

    /// Begin a new trace storage session
    func beginTrace(sessionId: UUID) async throws -> TraceWriter {
        let fileURL = storageDirectory.appendingPathComponent("\(sessionId.uuidString).trace")
        let handle = try TraceFileHandle(url: fileURL, mode: .write)
        traceFiles[sessionId] = handle
        activeTraceIds.insert(sessionId)

        logger.info("Started trace storage for session \(sessionId.uuidString)")

        return TraceWriter(sessionId: sessionId, manager: self)
    }

    /// Register a trace as active (for tracking during app termination)
    func registerActiveTrace(_ sessionId: UUID) {
        activeTraceIds.insert(sessionId)
    }

    /// Unregister a trace when it's no longer active
    func unregisterActiveTrace(_ sessionId: UUID) {
        activeTraceIds.remove(sessionId)
    }

    /// Append a state to the trace
    func appendState(_ state: TraceState, sessionId: UUID) async throws {
        guard let handle = traceFiles[sessionId] else {
            throw TraceStorageError.sessionNotFound(sessionId)
        }

        try handle.writeState(state)
    }

    /// Finalize a trace and return a lazy-loading ErrorTrace
    func finalizeTrace(
        sessionId: UUID,
        type: ErrorTrace.ErrorType,
        message: String,
        loopStart: Int?,
        violatedProperty: String?
    ) async throws -> LazyErrorTrace {
        guard let handle = traceFiles[sessionId] else {
            throw TraceStorageError.sessionNotFound(sessionId)
        }

        let stateCount = handle.stateCount
        try handle.finalize()

        logger.info("Finalized trace with \(stateCount) states for session \(sessionId.uuidString)")

        // Reopen for reading
        let readHandle = try TraceFileHandle(url: handle.url, mode: .read)
        traceFiles[sessionId] = readHandle

        return LazyErrorTrace(
            sessionId: sessionId,
            type: type,
            message: message,
            stateCount: stateCount,
            loopStart: loopStart,
            violatedProperty: violatedProperty,
            manager: self
        )
    }

    /// Load a page of states
    func loadPage(sessionId: UUID, pageIndex: Int) async throws -> [TraceState] {
        let key = PageKey(sessionId: sessionId, pageIndex: pageIndex)

        // Check cache
        if let cached = pageCache.get(key) {
            return cached
        }

        guard let handle = traceFiles[sessionId] else {
            throw TraceStorageError.sessionNotFound(sessionId)
        }

        let startIndex = pageIndex * pageSize
        let states = try handle.readStates(from: startIndex, count: pageSize)

        // Cache the page
        pageCache.set(key, value: states)

        return states
    }

    /// Load a single state by index
    func loadState(sessionId: UUID, index: Int) async throws -> TraceState {
        let pageIndex = index / pageSize
        let offsetInPage = index % pageSize

        let page = try await loadPage(sessionId: sessionId, pageIndex: pageIndex)

        guard offsetInPage < page.count else {
            throw TraceStorageError.stateNotFound(index)
        }

        return page[offsetInPage]
    }

    /// Clean up a trace session
    func cleanup(sessionId: UUID) async {
        activeTraceIds.remove(sessionId)

        if let handle = traceFiles.removeValue(forKey: sessionId) {
            handle.close()
            try? FileManager.default.removeItem(at: handle.url)
            logger.info("Cleaned up trace for session \(sessionId.uuidString)")
        }

        // Remove cached pages for this session
        pageCache.removeAll(where: { $0.sessionId == sessionId })
    }

    /// Clean up all active traces (called during app termination)
    func cleanupAllActiveTraces() async {
        // Collect both active traces and any pending cleanup from deinit
        var tracesToCleanup = activeTraceIds
        let pendingCleanup = LazyErrorTrace.drainPendingCleanup()
        tracesToCleanup.formUnion(pendingCleanup)

        for sessionId in tracesToCleanup {
            await cleanup(sessionId: sessionId)
        }
        activeTraceIds.removeAll()
        logger.info("Cleaned up \(tracesToCleanup.count) active traces during shutdown")
    }

    /// Clean up all old trace files (e.g., from previous crashes)
    func cleanupStaleTraces() async {
        let fileManager = FileManager.default
        guard let files = try? fileManager.contentsOfDirectory(at: storageDirectory, includingPropertiesForKeys: [.creationDateKey]) else {
            return
        }

        let staleThreshold = Date().addingTimeInterval(-24 * 60 * 60) // 24 hours

        for file in files where file.pathExtension == "trace" {
            if let attrs = try? fileManager.attributesOfItem(atPath: file.path),
               let creationDate = attrs[.creationDate] as? Date,
               creationDate < staleThreshold {
                try? fileManager.removeItem(at: file)
                logger.info("Removed stale trace file: \(file.lastPathComponent)")
            }
        }
    }

    /// Check if trace should use disk storage based on state count
    func shouldStreamToDisk(stateCount: Int) -> Bool {
        stateCount > streamingThreshold
    }
}

// MARK: - Trace Writer

/// Writer for appending states to a trace
/// @unchecked Sendable: accessed only via actor-isolated TraceStorageManager
final class TraceWriter: @unchecked Sendable {
    let sessionId: UUID
    private weak var manager: TraceStorageManager?
    private var stateCount = 0

    init(sessionId: UUID, manager: TraceStorageManager) {
        self.sessionId = sessionId
        self.manager = manager
    }

    func append(_ state: TraceState) async throws {
        guard let manager = manager else {
            throw TraceStorageError.managerDeallocated
        }
        try await manager.appendState(state, sessionId: sessionId)
        stateCount += 1
    }

    var count: Int { stateCount }
}

// MARK: - Lazy Error Trace

/// An error trace that loads states lazily from disk
/// @unchecked Sendable: immutable after init; manager access is actor-isolated
final class LazyErrorTrace: @unchecked Sendable {
    let sessionId: UUID
    let type: ErrorTrace.ErrorType
    let message: String
    let stateCount: Int
    let loopStart: Int?
    let violatedProperty: String?

    private weak var manager: TraceStorageManager?

    /// In-memory states for small traces (when not streamed to disk)
    private var inMemoryStates: [TraceState]?

    init(
        sessionId: UUID,
        type: ErrorTrace.ErrorType,
        message: String,
        stateCount: Int,
        loopStart: Int?,
        violatedProperty: String?,
        manager: TraceStorageManager
    ) {
        self.sessionId = sessionId
        self.type = type
        self.message = message
        self.stateCount = stateCount
        self.loopStart = loopStart
        self.violatedProperty = violatedProperty
        self.manager = manager
        // Ensure trace is registered for cleanup tracking during app termination
        Task {
            await manager.registerActiveTrace(sessionId)
        }
    }

    /// Create from in-memory states (for small traces)
    init(
        type: ErrorTrace.ErrorType,
        message: String,
        states: [TraceState],
        loopStart: Int?,
        violatedProperty: String?
    ) {
        self.sessionId = UUID()
        self.type = type
        self.message = message
        self.stateCount = states.count
        self.loopStart = loopStart
        self.violatedProperty = violatedProperty
        self.manager = nil
        self.inMemoryStates = states
    }

    /// Load a state by index
    func loadState(at index: Int) async throws -> TraceState {
        // Use in-memory states if available
        if let states = inMemoryStates {
            guard index < states.count else {
                throw TraceStorageError.stateNotFound(index)
            }
            return states[index]
        }

        guard let manager = manager else {
            throw TraceStorageError.managerDeallocated
        }

        return try await manager.loadState(sessionId: sessionId, index: index)
    }

    /// Load a range of states
    func loadStates(range: Swift.Range<Int>) async throws -> [TraceState] {
        // Use in-memory states if available
        if let states = inMemoryStates {
            return Array(states[range.clamped(to: 0..<states.count)])
        }

        guard let manager = manager else {
            throw TraceStorageError.managerDeallocated
        }

        var result: [TraceState] = []
        for index in range {
            if index >= stateCount { break }
            let state = try await manager.loadState(sessionId: sessionId, index: index)
            result.append(state)
        }
        return result
    }

    /// Convert to standard ErrorTrace (loads all states into memory - use with caution for large traces)
    func toErrorTrace() async throws -> ErrorTrace {
        let states: [TraceState]
        if let inMemory = inMemoryStates {
            states = inMemory
        } else {
            states = try await loadStates(range: 0..<stateCount)
        }

        return ErrorTrace(
            type: type,
            message: message,
            states: states,
            loopStart: loopStart,
            violatedProperty: violatedProperty
        )
    }

    /// Check if this trace is stored on disk
    var isStoredOnDisk: Bool {
        inMemoryStates == nil
    }

    deinit {
        // Cleanup disk storage when trace is deallocated.
        // We need to handle the case where deinit runs but async cleanup doesn't complete.
        if inMemoryStates == nil {
            let sessionId = self.sessionId
            // Add to pending cleanup queue synchronously (thread-safe)
            // This ensures the session is tracked even if async tasks don't complete
            LazyErrorTrace.addToPendingCleanup(sessionId)

            // Attempt async cleanup - may not complete during rapid shutdown
            // but the pending queue ensures we don't leak
            Task.detached {
                await TraceStorageManager.shared.cleanup(sessionId: sessionId)
                LazyErrorTrace.removeFromPendingCleanup(sessionId)
            }
        }
    }

    // MARK: - Pending Cleanup Queue (Thread-Safe)

    /// Thread-safe queue of session IDs pending cleanup.
    /// Used to track cleanup that started in deinit but may not have completed.
    private static let pendingCleanupLock = NSLock()
    private static var pendingCleanupIds = Set<UUID>()

    /// Add session to pending cleanup queue (called from deinit, must be synchronous)
    fileprivate static func addToPendingCleanup(_ sessionId: UUID) {
        pendingCleanupLock.lock()
        pendingCleanupIds.insert(sessionId)
        pendingCleanupLock.unlock()
    }

    /// Remove session from pending cleanup queue (called when cleanup completes)
    fileprivate static func removeFromPendingCleanup(_ sessionId: UUID) {
        pendingCleanupLock.lock()
        pendingCleanupIds.remove(sessionId)
        pendingCleanupLock.unlock()
    }

    /// Get all pending cleanup IDs and clear the queue (for termination handler)
    static func drainPendingCleanup() -> Set<UUID> {
        pendingCleanupLock.lock()
        let ids = pendingCleanupIds
        pendingCleanupIds.removeAll()
        pendingCleanupLock.unlock()
        return ids
    }
}

// MARK: - Trace File Handle

/// Low-level file handle for reading/writing trace states
private final class TraceFileHandle {
    let url: URL
    private let fileHandle: FileHandle
    private let encoder = JSONEncoder()
    private let decoder = JSONDecoder()
    private(set) var stateCount = 0
    private var stateOffsets: [UInt64] = []

    enum Mode {
        case read
        case write
    }

    init(url: URL, mode: Mode) throws {
        self.url = url

        switch mode {
        case .write:
            FileManager.default.createFile(atPath: url.path, contents: nil)
            do {
                fileHandle = try FileHandle(forWritingTo: url)
            } catch {
                // Clean up the created file if FileHandle init fails
                try? FileManager.default.removeItem(at: url)
                throw error
            }
        case .read:
            fileHandle = try FileHandle(forReadingFrom: url)
            try loadIndex()
        }
    }

    func writeState(_ state: TraceState) throws {
        let data = try encoder.encode(state)
        let length = UInt32(data.count)

        // Write length prefix
        var lengthBytes = length.littleEndian
        let lengthData = Data(bytes: &lengthBytes, count: 4)

        let offset = try fileHandle.seekToEnd()
        stateOffsets.append(offset)

        try fileHandle.write(contentsOf: lengthData)
        try fileHandle.write(contentsOf: data)

        stateCount += 1
    }

    func readStates(from startIndex: Int, count: Int) throws -> [TraceState] {
        var states: [TraceState] = []

        // Guard against out-of-bounds start index
        guard startIndex < stateOffsets.count else {
            return states
        }

        let endIndex = min(startIndex + count, stateOffsets.count)
        states.reserveCapacity(endIndex - startIndex)

        for index in startIndex..<endIndex {
            let state = try readState(at: index)
            states.append(state)
        }

        return states
    }

    func readState(at index: Int) throws -> TraceState {
        guard index < stateOffsets.count else {
            throw TraceStorageError.stateNotFound(index)
        }

        let offset = stateOffsets[index]
        try fileHandle.seek(toOffset: offset)

        // Read length prefix
        guard let lengthData = try fileHandle.read(upToCount: 4), lengthData.count == 4 else {
            throw TraceStorageError.corruptedFile
        }

        let length = lengthData.withUnsafeBytes { $0.load(as: UInt32.self).littleEndian }

        // Read state data
        guard let stateData = try fileHandle.read(upToCount: Int(length)), stateData.count == length else {
            throw TraceStorageError.corruptedFile
        }

        return try decoder.decode(TraceState.self, from: stateData)
    }

    func finalize() throws {
        // Write index at end of file
        // File format: [state data...][TLAINDEX][count][offsets...][indexStart]
        let indexStart = try fileHandle.seekToEnd()

        // Write marker
        let marker = "TLAINDEX".data(using: .utf8)!
        try fileHandle.write(contentsOf: marker)

        // Write state count
        var count = UInt32(stateCount).littleEndian
        let countData = Data(bytes: &count, count: 4)
        try fileHandle.write(contentsOf: countData)

        // Write offsets
        for offset in stateOffsets {
            var off = offset.littleEndian
            let offData = Data(bytes: &off, count: 8)
            try fileHandle.write(contentsOf: offData)
        }

        // Write index start position as footer (so we can find the index)
        var indexStartValue = indexStart.littleEndian
        let indexStartData = Data(bytes: &indexStartValue, count: 8)
        try fileHandle.write(contentsOf: indexStartData)

        try fileHandle.synchronize()
    }

    private func loadIndex() throws {
        // Read the last 8 bytes to get the index start position
        let endOffset = try fileHandle.seekToEnd()
        guard endOffset >= 20 else { // Minimum: marker(8) + count(4) + indexStart(8)
            throw TraceStorageError.corruptedFile
        }

        // Read footer (index start position)
        try fileHandle.seek(toOffset: endOffset - 8)
        guard let indexStartData = try fileHandle.read(upToCount: 8), indexStartData.count == 8 else {
            throw TraceStorageError.corruptedFile
        }
        let indexStart = indexStartData.withUnsafeBytes { $0.load(as: UInt64.self).littleEndian }

        // Seek to index start and read marker
        try fileHandle.seek(toOffset: indexStart)
        guard let markerData = try fileHandle.read(upToCount: 8),
              String(data: markerData, encoding: .utf8) == "TLAINDEX" else {
            throw TraceStorageError.corruptedFile
        }

        // Read state count
        guard let countData = try fileHandle.read(upToCount: 4), countData.count == 4 else {
            throw TraceStorageError.corruptedFile
        }
        stateCount = Int(countData.withUnsafeBytes { $0.load(as: UInt32.self).littleEndian })

        // Read offsets
        stateOffsets.reserveCapacity(stateCount)
        for _ in 0..<stateCount {
            guard let offData = try fileHandle.read(upToCount: 8), offData.count == 8 else {
                throw TraceStorageError.corruptedFile
            }
            let offset = offData.withUnsafeBytes { $0.load(as: UInt64.self).littleEndian }
            stateOffsets.append(offset)
        }
    }

    func close() {
        try? fileHandle.close()
    }

    deinit {
        close()
    }
}

// MARK: - Page Key

private struct PageKey: Hashable {
    let sessionId: UUID
    let pageIndex: Int
}

// MARK: - LRU Cache

/// O(1) LRU cache using a doubly-linked list and dictionary.
/// All operations (get, set, remove) are O(1).
private final class LRUCache<Key: Hashable, Value> {

    /// Doubly-linked list node with optional key/value for sentinel nodes
    private final class Node {
        var key: Key?
        var value: Value?
        var prev: Node?
        var next: Node?

        /// Create a data node
        init(key: Key, value: Value) {
            self.key = key
            self.value = value
        }

        /// Create a sentinel node (head or tail)
        init() {
            self.key = nil
            self.value = nil
        }
    }

    private let capacity: Int
    private var cache: [Key: Node] = [:]

    /// Sentinel head and tail for O(1) list operations
    private let head: Node
    private let tail: Node

    init(capacity: Int) {
        self.capacity = capacity
        self.head = Node()
        self.tail = Node()
        head.next = tail
        tail.prev = head
    }

    /// Get value for key, moving it to most recently used. O(1)
    func get(_ key: Key) -> Value? {
        guard let node = cache[key] else {
            return nil
        }
        // Move to front (most recently used)
        moveToFront(node)
        return node.value
    }

    /// Set value for key, evicting LRU if at capacity. O(1)
    func set(_ key: Key, value: Value) {
        if let node = cache[key] {
            // Update existing
            node.value = value
            moveToFront(node)
        } else {
            // Evict if at capacity
            while cache.count >= capacity {
                removeLRU()
            }

            // Add new node
            let node = Node(key: key, value: value)
            cache[key] = node
            addToFront(node)
        }
    }

    /// Remove all entries matching predicate. O(n) where n is matching entries
    func removeAll(where predicate: (Key) -> Bool) {
        let keysToRemove = cache.keys.filter(predicate)
        for key in keysToRemove {
            if let node = cache.removeValue(forKey: key) {
                removeNode(node)
            }
        }
    }

    // MARK: - Private List Operations (all O(1))

    private func addToFront(_ node: Node) {
        node.prev = head
        node.next = head.next
        head.next?.prev = node
        head.next = node
    }

    private func removeNode(_ node: Node) {
        node.prev?.next = node.next
        node.next?.prev = node.prev
        node.prev = nil
        node.next = nil
    }

    private func moveToFront(_ node: Node) {
        removeNode(node)
        addToFront(node)
    }

    private func removeLRU() {
        guard let lru = tail.prev, lru !== head, let key = lru.key else {
            return
        }
        removeNode(lru)
        cache.removeValue(forKey: key)
    }
}

// MARK: - Errors

enum TraceStorageError: Error, LocalizedError {
    case sessionNotFound(UUID)
    case stateNotFound(Int)
    case corruptedFile
    case managerDeallocated

    var errorDescription: String? {
        switch self {
        case .sessionNotFound(let id):
            return "Trace session not found: \(id)"
        case .stateNotFound(let index):
            return "State not found at index: \(index)"
        case .corruptedFile:
            return "Trace file is corrupted"
        case .managerDeallocated:
            return "Trace storage manager was deallocated"
        }
    }
}
