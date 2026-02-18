// ProofCache.swift
// TLAStudio
//
// An actor that manages fingerprint-based caching of proof results.
// The cache uses directory sharding for efficient file system access and
// maintains an index for fast lookups.

import Foundation
import os

private let logger = Log.logger(category: "ProofCache")

// MARK: - CacheEntry

/// A cached proof result entry.
///
/// Stores the essential information about a proof result along with
/// metadata for cache management.
public struct CacheEntry: Codable, Sendable {
    /// The TLAPM-generated fingerprint for this proof obligation.
    public let fingerprint: String

    /// The verification status of the obligation.
    public let status: ProofStatus

    /// The backend prover that was used for verification.
    public let backend: ProverBackend

    /// When this result was cached.
    public let timestamp: Date

    /// How long the verification took.
    public let duration: TimeInterval

    /// The spec URL path this entry is associated with (if any).
    public let specPath: String?

    public init(
        fingerprint: String,
        status: ProofStatus,
        backend: ProverBackend,
        timestamp: Date = Date(),
        duration: TimeInterval,
        specPath: String? = nil
    ) {
        self.fingerprint = fingerprint
        self.status = status
        self.backend = backend
        self.timestamp = timestamp
        self.duration = duration
        self.specPath = specPath
    }

    /// Returns the sharded directory prefix (first 2 characters of fingerprint).
    var shardPrefix: String {
        guard fingerprint.count >= 2 else { return "00" }
        return String(fingerprint.prefix(2))
    }

    /// Returns the filename for this cache entry.
    var filename: String {
        "\(fingerprint).json"
    }

    /// Checks if this entry has expired based on the given max age.
    func isExpired(maxAge: TimeInterval) -> Bool {
        Date().timeIntervalSince(timestamp) > maxAge
    }
}

// MARK: - CacheIndex

/// The index structure for fast fingerprint lookups.
///
/// The index maps fingerprints to their file locations and tracks
/// associations between specs and their proof obligations.
private struct CacheIndex: Codable {
    /// Index format version for future migrations.
    var version: Int = 1

    /// Maps fingerprints to their index entries.
    var entries: [String: IndexEntry] = [:]

    /// Maps spec paths to sets of fingerprints for spec-specific cache clearing.
    var specAssociations: [String: Set<String>] = [:]

    struct IndexEntry: Codable {
        let relativePath: String
        let timestamp: Date
        let specPath: String?
    }

    mutating func addEntry(
        fingerprint: String,
        relativePath: String,
        timestamp: Date,
        specPath: String?
    ) {
        entries[fingerprint] = IndexEntry(
            relativePath: relativePath,
            timestamp: timestamp,
            specPath: specPath
        )

        if let specPath = specPath {
            var fingerprints = specAssociations[specPath] ?? []
            fingerprints.insert(fingerprint)
            specAssociations[specPath] = fingerprints
        }
    }

    mutating func removeEntry(fingerprint: String) {
        if let entry = entries[fingerprint], let specPath = entry.specPath {
            specAssociations[specPath]?.remove(fingerprint)
            if specAssociations[specPath]?.isEmpty == true {
                specAssociations.removeValue(forKey: specPath)
            }
        }
        entries.removeValue(forKey: fingerprint)
    }

    func fingerprints(for specPath: String) -> Set<String> {
        specAssociations[specPath] ?? []
    }
}

// MARK: - CacheStatistics

/// Statistics about the proof cache.
public struct CacheStatistics: Sendable {
    /// Total number of entries in the cache.
    public let totalEntries: Int

    /// Number of cache hits since statistics were last reset.
    public let cacheHits: Int

    /// Number of cache misses since statistics were last reset.
    public let cacheMisses: Int

    /// Total size of all cached files in bytes.
    public let totalSize: Int64

    /// Timestamp of the oldest entry in the cache.
    public let oldestEntry: Date?

    /// Timestamp of the newest entry in the cache.
    public let newestEntry: Date?

    /// The cache hit rate as a percentage (0.0 to 1.0).
    public var hitRate: Double {
        let total = cacheHits + cacheMisses
        guard total > 0 else { return 0.0 }
        return Double(cacheHits) / Double(total)
    }

    /// Human-readable description of the cache size.
    public var formattedSize: String {
        let formatter = ByteCountFormatter()
        formatter.countStyle = .file
        return formatter.string(fromByteCount: totalSize)
    }
}

// MARK: - CacheConfiguration

/// Configuration options for the proof cache.
public struct CacheConfiguration: Sendable {
    /// Maximum age of cache entries in seconds (default: 30 days).
    public var maxAge: TimeInterval

    /// Maximum total cache size in bytes (default: 100 MB).
    public var maxSize: Int64

    /// Whether caching is enabled.
    public var isEnabled: Bool

    /// Default configuration with 30-day expiry and 100 MB limit.
    public static let `default` = CacheConfiguration(
        maxAge: 30 * 24 * 60 * 60,  // 30 days
        maxSize: 100 * 1024 * 1024,  // 100 MB
        isEnabled: true
    )

    public init(
        maxAge: TimeInterval = 30 * 24 * 60 * 60,
        maxSize: Int64 = 100 * 1024 * 1024,
        isEnabled: Bool = true
    ) {
        self.maxAge = maxAge
        self.maxSize = maxSize
        self.isEnabled = isEnabled
    }
}

// MARK: - ProofCache Actor

/// An actor that manages fingerprint-based caching of proof results.
///
/// The cache stores proof results organized by fingerprint using directory sharding
/// for efficient file system access. The first two characters of the fingerprint
/// determine the subdirectory, preventing any single directory from containing
/// too many files.
///
/// ## Cache Structure
///
/// ```
/// ~/Library/Application Support/TLAStudio/ProofCache/
/// ├── ab/
/// │   ├── ab12cd34...json
/// │   └── ab98ef76...json
/// ├── cd/
/// │   └── cd45...json
/// └── index.json
/// ```
///
/// ## Thread Safety
///
/// As an actor, `ProofCache` provides complete thread safety for all operations.
/// Multiple concurrent proof checks can safely query and update the cache.
///
/// ## Usage Example
///
/// ```swift
/// let cache = try await ProofCache()
///
/// // Check for cached result
/// if let cached = await cache.getCachedResult(fingerprint: obligation.fingerprint) {
///     // Use cached result
///     return cached.status
/// }
///
/// // Cache new result
/// await cache.cacheResult(obligation: verifiedObligation)
/// ```
public actor ProofCache {

    // MARK: - Properties

    /// The root directory for the proof cache.
    private let cacheDirectory: URL

    /// The path to the index file.
    private var indexURL: URL {
        cacheDirectory.appendingPathComponent("index.json")
    }

    /// The in-memory cache index.
    private var index: CacheIndex

    /// Configuration for the cache.
    public private(set) var configuration: CacheConfiguration

    /// JSON encoder for cache entries.
    private let encoder: JSONEncoder = {
        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        return encoder
    }()

    /// JSON decoder for cache entries.
    private let decoder: JSONDecoder = {
        let decoder = JSONDecoder()
        decoder.dateDecodingStrategy = .iso8601
        return decoder
    }()

    // MARK: - Statistics Tracking

    private var _cacheHits: Int = 0
    private var _cacheMisses: Int = 0
    private var _totalSize: Int64 = 0

    // MARK: - Initialization

    /// Creates a new proof cache with the specified directory and configuration.
    ///
    /// - Parameters:
    ///   - directory: The root directory for the cache. If nil, uses the default location.
    ///   - configuration: Cache configuration options.
    /// - Throws: An error if the cache directory cannot be created.
    public init(
        directory: URL? = nil,
        configuration: CacheConfiguration = .default
    ) async throws {
        let cacheDir = directory ?? Self.defaultCacheDirectory
        self.cacheDirectory = cacheDir
        self.configuration = configuration
        self.index = CacheIndex()

        try await initializeCache()
    }

    /// The default cache directory in Application Support.
    public static var defaultCacheDirectory: URL {
        let appSupport = FileManager.default.urls(
            for: .applicationSupportDirectory,
            in: .userDomainMask
        ).first!
        return appSupport.appendingPathComponent("TLAStudio/ProofCache", isDirectory: true)
    }

    // MARK: - Public Methods

    /// Retrieves a cached result for the given fingerprint.
    ///
    /// - Parameter fingerprint: The TLAPM-generated fingerprint to look up.
    /// - Returns: The cached entry if found and not expired, nil otherwise.
    public func getCachedResult(fingerprint: String) -> CacheEntry? {
        guard configuration.isEnabled else {
            _cacheMisses += 1
            return nil
        }

        guard let indexEntry = index.entries[fingerprint] else {
            _cacheMisses += 1
            return nil
        }

        let entryURL = cacheDirectory.appendingPathComponent(indexEntry.relativePath)

        guard let data = try? Data(contentsOf: entryURL),
              let entry = try? decoder.decode(CacheEntry.self, from: data) else {
            // Cache file is corrupted or missing, remove from index
            index.removeEntry(fingerprint: fingerprint)
            _cacheMisses += 1
            return nil
        }

        // Check if entry has expired
        if entry.isExpired(maxAge: configuration.maxAge) {
            // Remove expired entry asynchronously
            Task { await removeEntry(fingerprint: fingerprint) }
            _cacheMisses += 1
            return nil
        }

        _cacheHits += 1
        return entry
    }

    /// Retrieves cached results for multiple fingerprints.
    ///
    /// This is more efficient than calling `getCachedResult` multiple times
    /// when you need to look up several fingerprints at once.
    ///
    /// - Parameter fingerprints: The fingerprints to look up.
    /// - Returns: A dictionary mapping fingerprints to their cached entries.
    public func getCachedResults(fingerprints: [String]) -> [String: CacheEntry] {
        var results: [String: CacheEntry] = [:]

        for fingerprint in fingerprints {
            if let entry = getCachedResult(fingerprint: fingerprint) {
                results[fingerprint] = entry
            }
        }

        return results
    }

    /// Caches a proof result from a completed obligation.
    ///
    /// Only terminal proof statuses are cached (proved, failed, timeout, trivial).
    /// Non-terminal statuses (unknown, pending) are ignored.
    ///
    /// - Parameter obligation: The proof obligation with completed verification results.
    public func cacheResult(obligation: ProofObligation) async {
        guard configuration.isEnabled else { return }

        // Only cache terminal statuses
        guard obligation.status.isTerminal else { return }

        // Require a backend for non-trivial proofs
        guard let backend = obligation.backend else {
            // For trivial proofs, use auto as a placeholder
            if obligation.status == .trivial {
                await cacheEntry(
                    fingerprint: obligation.fingerprint,
                    status: obligation.status,
                    backend: .auto,
                    duration: obligation.duration ?? 0,
                    specPath: obligation.location.fileURL.path
                )
            }
            return
        }

        await cacheEntry(
            fingerprint: obligation.fingerprint,
            status: obligation.status,
            backend: backend,
            duration: obligation.duration ?? 0,
            specPath: obligation.location.fileURL.path
        )
    }

    /// Caches a proof result with explicit parameters.
    ///
    /// - Parameters:
    ///   - fingerprint: The TLAPM-generated fingerprint.
    ///   - status: The verification status.
    ///   - backend: The prover backend used.
    ///   - duration: The time taken for verification.
    ///   - specPath: The path to the spec file (optional).
    public func cacheEntry(
        fingerprint: String,
        status: ProofStatus,
        backend: ProverBackend,
        duration: TimeInterval,
        specPath: String? = nil
    ) async {
        guard configuration.isEnabled else { return }

        let entry = CacheEntry(
            fingerprint: fingerprint,
            status: status,
            backend: backend,
            timestamp: Date(),
            duration: duration,
            specPath: specPath
        )

        do {
            try await writeEntry(entry)
        } catch {
            // Log error but don't throw - caching failures shouldn't break the app
            logger.error("Failed to cache result for \(fingerprint): \(error)")
        }
    }

    /// Clears the cache for a specific spec or the entire cache.
    ///
    /// - Parameter specURL: If provided, only clears entries associated with this spec.
    ///                      If nil, clears the entire cache.
    public func clearCache(for specURL: URL? = nil) async {
        if let specURL = specURL {
            await clearCacheForSpec(specURL)
        } else {
            await clearAllCache()
        }
    }

    /// Removes cache entries older than the specified interval.
    ///
    /// This method scans all cached entries and removes those that have
    /// exceeded the specified age. Use this for periodic cache maintenance.
    ///
    /// - Parameter olderThan: The maximum age for entries. Entries older than this will be removed.
    public func pruneExpiredEntries(olderThan: TimeInterval) async {
        let cutoffDate = Date().addingTimeInterval(-olderThan)
        var fingerprintsToRemove: [String] = []

        for (fingerprint, indexEntry) in index.entries {
            if indexEntry.timestamp < cutoffDate {
                fingerprintsToRemove.append(fingerprint)
            }
        }

        for fingerprint in fingerprintsToRemove {
            await removeEntry(fingerprint: fingerprint)
        }

        if !fingerprintsToRemove.isEmpty {
            await saveIndex()
        }
    }

    /// Updates the cache configuration.
    ///
    /// - Parameter configuration: The new configuration to apply.
    public func updateConfiguration(_ configuration: CacheConfiguration) {
        self.configuration = configuration
    }

    /// Returns current cache statistics.
    ///
    /// - Returns: A statistics object containing cache metrics.
    public func getStatistics() async -> CacheStatistics {
        // Calculate total size by scanning the cache directory
        let totalSize = await calculateTotalSize()
        _totalSize = totalSize

        let timestamps = index.entries.values.map(\.timestamp)

        return CacheStatistics(
            totalEntries: index.entries.count,
            cacheHits: _cacheHits,
            cacheMisses: _cacheMisses,
            totalSize: totalSize,
            oldestEntry: timestamps.min(),
            newestEntry: timestamps.max()
        )
    }

    /// Resets the hit/miss statistics counters.
    public func resetStatistics() {
        _cacheHits = 0
        _cacheMisses = 0
    }

    /// Enforces the maximum cache size by removing oldest entries.
    ///
    /// This method is called automatically after writing new entries.
    /// It removes the oldest entries until the total cache size is
    /// below the configured maximum.
    public func enforceMaxSize() async {
        let currentSize = await calculateTotalSize()
        guard currentSize > configuration.maxSize else { return }

        // Sort entries by timestamp (oldest first)
        let sortedEntries = index.entries.sorted { $0.value.timestamp < $1.value.timestamp }

        var freedSize: Int64 = 0
        let targetFreed = currentSize - configuration.maxSize

        for (fingerprint, indexEntry) in sortedEntries {
            guard freedSize < targetFreed else { break }

            let entryURL = cacheDirectory.appendingPathComponent(indexEntry.relativePath)
            if let attrs = try? FileManager.default.attributesOfItem(atPath: entryURL.path),
               let fileSize = attrs[.size] as? Int64 {
                freedSize += fileSize
            }

            await removeEntry(fingerprint: fingerprint)
        }

        await saveIndex()
    }

    // MARK: - Private Methods

    /// Initializes the cache directory and loads the index.
    private func initializeCache() async throws {
        let fileManager = FileManager.default

        // Create cache directory if needed
        if !fileManager.fileExists(atPath: cacheDirectory.path) {
            do {
                try fileManager.createDirectory(
                    at: cacheDirectory,
                    withIntermediateDirectories: true,
                    attributes: nil
                )
            } catch {
                throw CacheError.directoryCreationFailed(cacheDirectory, error)
            }
        }

        // Load existing index or create new one
        if fileManager.fileExists(atPath: indexURL.path) {
            do {
                let data = try Data(contentsOf: indexURL)
                index = try decoder.decode(CacheIndex.self, from: data)

                // Validate index entries against actual files
                await validateIndex()
            } catch {
                // Index is corrupted, rebuild it
                logger.warning("Rebuilding corrupted index: \(error)")
                await rebuildIndex()
            }
        } else {
            // No index exists, scan for existing cache files
            await rebuildIndex()
        }

        // Calculate initial size
        _totalSize = await calculateTotalSize()
    }

    /// Writes a cache entry to disk.
    private func writeEntry(_ entry: CacheEntry) async throws {
        let fileManager = FileManager.default

        // Create shard directory if needed
        let shardDir = cacheDirectory.appendingPathComponent(entry.shardPrefix, isDirectory: true)
        if !fileManager.fileExists(atPath: shardDir.path) {
            try fileManager.createDirectory(
                at: shardDir,
                withIntermediateDirectories: true,
                attributes: nil
            )
        }

        // Write entry file
        let entryURL = shardDir.appendingPathComponent(entry.filename)
        let data = try encoder.encode(entry)
        try data.write(to: entryURL, options: .atomic)

        // Update index
        let relativePath = "\(entry.shardPrefix)/\(entry.filename)"
        index.addEntry(
            fingerprint: entry.fingerprint,
            relativePath: relativePath,
            timestamp: entry.timestamp,
            specPath: entry.specPath
        )

        await saveIndex()

        // Check if we need to enforce size limits
        await enforceMaxSize()
    }

    /// Removes a single cache entry.
    private func removeEntry(fingerprint: String) async {
        guard let indexEntry = index.entries[fingerprint] else { return }

        let entryURL = cacheDirectory.appendingPathComponent(indexEntry.relativePath)
        try? FileManager.default.removeItem(at: entryURL)

        index.removeEntry(fingerprint: fingerprint)

        // Try to remove empty shard directory (will fail if not empty, which is expected)
        let shardDir = entryURL.deletingLastPathComponent()
        try? FileManager.default.removeItem(at: shardDir)
    }

    /// Clears all cache entries for a specific spec.
    private func clearCacheForSpec(_ specURL: URL) async {
        let specPath = specURL.path
        let fingerprints = index.fingerprints(for: specPath)

        for fingerprint in fingerprints {
            await removeEntry(fingerprint: fingerprint)
        }

        await saveIndex()
    }

    /// Clears the entire cache.
    private func clearAllCache() async {
        let fileManager = FileManager.default

        // Remove all files in cache directory except index
        if let contents = try? fileManager.contentsOfDirectory(
            at: cacheDirectory,
            includingPropertiesForKeys: nil
        ) {
            for url in contents {
                if url.lastPathComponent != "index.json" {
                    try? fileManager.removeItem(at: url)
                }
            }
        }

        // Reset index
        index = CacheIndex()
        await saveIndex()

        // Reset statistics
        _totalSize = 0
    }

    /// Saves the index to disk.
    private func saveIndex() async {
        do {
            let data = try encoder.encode(index)
            try data.write(to: indexURL, options: .atomic)
        } catch {
            logger.error("Failed to save index: \(error)")
        }
    }

    /// Validates the index against the file system.
    private func validateIndex() async {
        var invalidFingerprints: [String] = []
        let fileManager = FileManager.default

        for (fingerprint, indexEntry) in index.entries {
            let entryURL = cacheDirectory.appendingPathComponent(indexEntry.relativePath)
            if !fileManager.fileExists(atPath: entryURL.path) {
                invalidFingerprints.append(fingerprint)
            }
        }

        // Remove invalid entries
        for fingerprint in invalidFingerprints {
            index.removeEntry(fingerprint: fingerprint)
        }

        if !invalidFingerprints.isEmpty {
            await saveIndex()
        }
    }

    /// Rebuilds the index by scanning the cache directory.
    private func rebuildIndex() async {
        index = CacheIndex()
        let fileManager = FileManager.default

        guard let contents = try? fileManager.contentsOfDirectory(
            at: cacheDirectory,
            includingPropertiesForKeys: [.isDirectoryKey]
        ) else {
            return
        }

        for item in contents {
            // Check if this is a shard directory (2-character name)
            let shardName = item.lastPathComponent
            guard shardName.count == 2 else { continue }

            // Check if it's a directory
            var isDirectory: ObjCBool = false
            guard fileManager.fileExists(atPath: item.path, isDirectory: &isDirectory),
                  isDirectory.boolValue else {
                continue
            }

            // Scan shard directory for cache files
            guard let entryFiles = try? fileManager.contentsOfDirectory(
                at: item,
                includingPropertiesForKeys: nil
            ) else {
                continue
            }

            for entryFile in entryFiles {
                guard entryFile.pathExtension == "json" else { continue }

                do {
                    let data = try Data(contentsOf: entryFile)
                    let entry = try decoder.decode(CacheEntry.self, from: data)

                    let relativePath = "\(shardName)/\(entryFile.lastPathComponent)"
                    index.addEntry(
                        fingerprint: entry.fingerprint,
                        relativePath: relativePath,
                        timestamp: entry.timestamp,
                        specPath: entry.specPath
                    )
                } catch {
                    // Skip corrupted files
                    logger.warning("Skipping corrupted cache file: \(entryFile.path)")
                }
            }
        }

        await saveIndex()
    }

    /// Calculates the total size of all cached files.
    private func calculateTotalSize() async -> Int64 {
        let fileManager = FileManager.default
        var totalSize: Int64 = 0

        for indexEntry in index.entries.values {
            let entryURL = cacheDirectory.appendingPathComponent(indexEntry.relativePath)
            if let attrs = try? fileManager.attributesOfItem(atPath: entryURL.path),
               let fileSize = attrs[.size] as? Int64 {
                totalSize += fileSize
            }
        }

        // Include index file size
        if let attrs = try? fileManager.attributesOfItem(atPath: indexURL.path),
           let fileSize = attrs[.size] as? Int64 {
            totalSize += fileSize
        }

        return totalSize
    }
}

// MARK: - Convenience Extensions

extension ProofCache {

    /// Checks if a result exists in the cache for the given fingerprint.
    ///
    /// - Parameter fingerprint: The fingerprint to check.
    /// - Returns: True if a valid, non-expired entry exists.
    public func hasCachedResult(fingerprint: String) -> Bool {
        getCachedResult(fingerprint: fingerprint) != nil
    }

    /// Returns all fingerprints currently in the cache.
    public var cachedFingerprints: Set<String> {
        Set(index.entries.keys)
    }

    /// Returns the number of entries in the cache.
    public var entryCount: Int {
        index.entries.count
    }
}

// MARK: - Cache Errors

/// Errors that can occur during cache operations.
public enum CacheError: Error, LocalizedError {
    case directoryCreationFailed(URL, Error)
    case indexCorrupted(Error)
    case writeError(String, Error)

    public var errorDescription: String? {
        switch self {
        case .directoryCreationFailed(let url, let error):
            return "Failed to create cache directory at \(url.path): \(error.localizedDescription)"
        case .indexCorrupted(let error):
            return "Cache index is corrupted: \(error.localizedDescription)"
        case .writeError(let fingerprint, let error):
            return "Failed to write cache entry for \(fingerprint): \(error.localizedDescription)"
        }
    }
}
