import XCTest
@testable import TLAStudioApp

// MARK: - Proof Cache Tests

/// Tests for the ProofCache actor that manages fingerprint-based caching.
final class ProofCacheTests: TempDirectoryTestCase {

    // MARK: - Cache Entry Tests

    func testCacheEntryCreation() {
        let entry = CacheEntry(
            fingerprint: "abc123def456",
            status: .proved,
            backend: .auto,
            duration: 1.5,
            specPath: "/path/to/spec.tla"
        )

        XCTAssertEqual(entry.fingerprint, "abc123def456")
        XCTAssertEqual(entry.status, .proved)
        XCTAssertEqual(entry.backend, .auto)
        XCTAssertEqual(entry.duration, 1.5)
        XCTAssertEqual(entry.specPath, "/path/to/spec.tla")
    }

    func testShardPrefix() {
        let entry = CacheEntry(
            fingerprint: "ab12cd34ef56",
            status: .proved,
            backend: .auto,
            duration: 1.0
        )

        XCTAssertEqual(entry.shardPrefix, "ab")
    }

    func testShardPrefixShortFingerprint() {
        let entry = CacheEntry(
            fingerprint: "a",
            status: .proved,
            backend: .auto,
            duration: 1.0
        )

        // Should fall back to "00" for too-short fingerprints
        XCTAssertEqual(entry.shardPrefix, "00")
    }

    func testCacheEntryFilename() {
        let entry = CacheEntry(
            fingerprint: "testfingerprint123",
            status: .proved,
            backend: .auto,
            duration: 1.0
        )

        XCTAssertEqual(entry.filename, "testfingerprint123.json")
    }

    func testCacheEntryExpiration() {
        let oldEntry = CacheEntry(
            fingerprint: "old",
            status: .proved,
            backend: .auto,
            timestamp: Date().addingTimeInterval(-60 * 60 * 25),  // 25 hours ago
            duration: 1.0
        )

        let newEntry = CacheEntry(
            fingerprint: "new",
            status: .proved,
            backend: .auto,
            timestamp: Date(),
            duration: 1.0
        )

        let maxAge: TimeInterval = 60 * 60 * 24  // 24 hours

        XCTAssertTrue(oldEntry.isExpired(maxAge: maxAge))
        XCTAssertFalse(newEntry.isExpired(maxAge: maxAge))
    }

    // MARK: - Cache Configuration Tests

    func testDefaultConfiguration() {
        let config = CacheConfiguration.default

        XCTAssertEqual(config.maxAge, 30 * 24 * 60 * 60)  // 30 days
        XCTAssertEqual(config.maxSize, 100 * 1024 * 1024) // 100 MB
        XCTAssertTrue(config.isEnabled)
    }

    func testCustomConfiguration() {
        let config = CacheConfiguration(
            maxAge: 7 * 24 * 60 * 60,  // 7 days
            maxSize: 50 * 1024 * 1024, // 50 MB
            isEnabled: false
        )

        XCTAssertEqual(config.maxAge, 7 * 24 * 60 * 60)
        XCTAssertEqual(config.maxSize, 50 * 1024 * 1024)
        XCTAssertFalse(config.isEnabled)
    }

    // MARK: - Cache Statistics Tests

    func testCacheStatisticsHitRate() {
        let statsWithHits = CacheStatistics(
            totalEntries: 100,
            cacheHits: 80,
            cacheMisses: 20,
            totalSize: 1024,
            oldestEntry: Date(),
            newestEntry: Date()
        )

        XCTAssertEqual(statsWithHits.hitRate, 0.8, accuracy: 0.001)
    }

    func testCacheStatisticsZeroTotal() {
        let statsEmpty = CacheStatistics(
            totalEntries: 0,
            cacheHits: 0,
            cacheMisses: 0,
            totalSize: 0,
            oldestEntry: nil,
            newestEntry: nil
        )

        XCTAssertEqual(statsEmpty.hitRate, 0.0)
    }

    func testCacheStatisticsFormattedSize() {
        let stats = CacheStatistics(
            totalEntries: 10,
            cacheHits: 5,
            cacheMisses: 5,
            totalSize: 1024 * 1024,  // 1 MB
            oldestEntry: nil,
            newestEntry: nil
        )

        XCTAssertFalse(stats.formattedSize.isEmpty)
        // The formatter should produce something like "1 MB"
    }

    // MARK: - Cache Error Tests

    func testCacheErrorDescriptions() {
        let testDir = URL(fileURLWithPath: "/tmp/test")
        let underlyingError = NSError(domain: "test", code: 1)

        let errors: [CacheError] = [
            .directoryCreationFailed(testDir, underlyingError),
            .indexCorrupted(underlyingError),
            .writeError("fingerprint123", underlyingError)
        ]

        for error in errors {
            XCTAssertNotNil(error.errorDescription)
            XCTAssertFalse(error.errorDescription!.isEmpty)
        }
    }

    func testDirectoryCreationFailedError() {
        let url = URL(fileURLWithPath: "/invalid/path")
        let underlyingError = NSError(domain: "FileManager", code: 1, userInfo: [NSLocalizedDescriptionKey: "Permission denied"])
        let error = CacheError.directoryCreationFailed(url, underlyingError)

        XCTAssertTrue(error.errorDescription?.contains("/invalid/path") ?? false)
        XCTAssertTrue(error.errorDescription?.contains("Permission denied") ?? false)
    }

    // MARK: - ProofCache Actor Tests

    func testCacheInitialization() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        let entryCount = await cache.entryCount
        let fingerprints = await cache.cachedFingerprints

        XCTAssertEqual(entryCount, 0)
        XCTAssertTrue(fingerprints.isEmpty)
    }

    func testCacheEntryAndRetrieval() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        // Cache an entry
        await cache.cacheEntry(
            fingerprint: "test123",
            status: .proved,
            backend: .auto,
            duration: 0.5,
            specPath: "/test.tla"
        )

        // Retrieve it
        let result = await cache.getCachedResult(fingerprint: "test123")

        XCTAssertNotNil(result)
        XCTAssertEqual(result?.fingerprint, "test123")
        XCTAssertEqual(result?.status, .proved)
    }

    func testCacheMiss() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        let result = await cache.getCachedResult(fingerprint: "nonexistent")

        XCTAssertNil(result)
    }

    func testHasCachedResult() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        let beforeCache = await cache.hasCachedResult(fingerprint: "test")
        XCTAssertFalse(beforeCache)

        await cache.cacheEntry(
            fingerprint: "test",
            status: .proved,
            backend: .auto,
            duration: 0.1
        )

        let afterCache = await cache.hasCachedResult(fingerprint: "test")
        XCTAssertTrue(afterCache)
    }

    func testMultipleCacheEntries() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        for i in 0..<10 {
            await cache.cacheEntry(
                fingerprint: "fp\(i)",
                status: .proved,
                backend: .auto,
                duration: Double(i) * 0.1
            )
        }

        let entryCount = await cache.entryCount
        let fingerprints = await cache.cachedFingerprints

        XCTAssertEqual(entryCount, 10)
        XCTAssertEqual(fingerprints.count, 10)
        XCTAssertTrue(fingerprints.contains("fp0"))
        XCTAssertTrue(fingerprints.contains("fp9"))
    }

    func testGetCachedResults() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        await cache.cacheEntry(fingerprint: "a", status: .proved, backend: .auto, duration: 0.1)
        await cache.cacheEntry(fingerprint: "b", status: .failed, backend: .auto, duration: 0.2)

        let results = await cache.getCachedResults(fingerprints: ["a", "b", "c"])

        XCTAssertEqual(results.count, 2)
        XCTAssertNotNil(results["a"])
        XCTAssertNotNil(results["b"])
        XCTAssertNil(results["c"])
    }

    func testClearAllCache() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        for i in 0..<5 {
            await cache.cacheEntry(
                fingerprint: "fp\(i)",
                status: .proved,
                backend: .auto,
                duration: 0.1
            )
        }

        let beforeClear = await cache.entryCount
        XCTAssertEqual(beforeClear, 5)

        await cache.clearCache()

        let afterClear = await cache.entryCount
        XCTAssertEqual(afterClear, 0)
    }

    func testCacheDisabled() async throws {
        var config = CacheConfiguration.default
        config.isEnabled = false

        let cache = try await ProofCache(directory: tempDirectory, configuration: config)

        await cache.cacheEntry(
            fingerprint: "test",
            status: .proved,
            backend: .auto,
            duration: 0.1
        )

        // Entry should not be cached when disabled
        let result = await cache.getCachedResult(fingerprint: "test")
        XCTAssertNil(result)
    }

    func testUpdateConfiguration() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        var newConfig = CacheConfiguration.default
        newConfig.isEnabled = false
        await cache.updateConfiguration(newConfig)

        // After disabling, new entries should not be cached
        await cache.cacheEntry(
            fingerprint: "test",
            status: .proved,
            backend: .auto,
            duration: 0.1
        )

        let result = await cache.getCachedResult(fingerprint: "test")
        XCTAssertNil(result)
    }

    func testGetStatistics() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        // Generate some activity
        await cache.cacheEntry(fingerprint: "hit", status: .proved, backend: .auto, duration: 0.1)
        _ = await cache.getCachedResult(fingerprint: "hit")      // Hit
        _ = await cache.getCachedResult(fingerprint: "miss")     // Miss

        let stats = await cache.getStatistics()

        XCTAssertEqual(stats.totalEntries, 1)
        XCTAssertGreaterThanOrEqual(stats.cacheHits, 1)
        XCTAssertGreaterThanOrEqual(stats.cacheMisses, 1)
    }

    func testResetStatistics() async throws {
        let cache = try await ProofCache(directory: tempDirectory)

        // Generate some activity
        _ = await cache.getCachedResult(fingerprint: "miss")

        await cache.resetStatistics()

        let stats = await cache.getStatistics()
        XCTAssertEqual(stats.cacheHits, 0)
        XCTAssertEqual(stats.cacheMisses, 0)
    }

    func testDefaultCacheDirectory() {
        let defaultDir = ProofCache.defaultCacheDirectory

        XCTAssertTrue(defaultDir.path.contains("Application Support"))
        XCTAssertTrue(defaultDir.path.contains("TLAStudio"))
        XCTAssertTrue(defaultDir.path.contains("ProofCache"))
    }

    // MARK: - ProofStatus Tests

    func testProofStatusIsTerminal() {
        // Terminal statuses (can be cached)
        XCTAssertTrue(ProofStatus.proved.isTerminal)
        XCTAssertTrue(ProofStatus.failed.isTerminal)
        XCTAssertTrue(ProofStatus.trivial.isTerminal)
        XCTAssertTrue(ProofStatus.omitted.isTerminal)
        XCTAssertTrue(ProofStatus.timeout.isTerminal)

        // Non-terminal statuses
        XCTAssertFalse(ProofStatus.pending.isTerminal)
        XCTAssertFalse(ProofStatus.unknown.isTerminal)
    }
}
