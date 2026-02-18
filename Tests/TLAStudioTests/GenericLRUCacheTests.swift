import XCTest
@testable import TLAStudioApp

final class GenericLRUCacheTests: XCTestCase {

    // MARK: - Basic Operations

    func testSetAndGet() {
        let cache = GenericLRUCache<String, Int>(capacity: 5)
        cache.set("a", value: 1)
        cache.set("b", value: 2)
        XCTAssertEqual(cache.get("a"), 1)
        XCTAssertEqual(cache.get("b"), 2)
    }

    func testGetMissingKeyReturnsNil() {
        let cache = GenericLRUCache<String, Int>(capacity: 5)
        XCTAssertNil(cache.get("missing"))
    }

    func testOverwriteExistingKey() {
        let cache = GenericLRUCache<String, Int>(capacity: 5)
        cache.set("a", value: 1)
        cache.set("a", value: 42)
        XCTAssertEqual(cache.get("a"), 42)
        XCTAssertEqual(cache.count, 1)
    }

    // MARK: - Eviction

    func testEvictionAtCapacity() {
        let cache = GenericLRUCache<String, Int>(capacity: 3)
        cache.set("a", value: 1)
        cache.set("b", value: 2)
        cache.set("c", value: 3)
        // Cache is full. Adding "d" should evict "a" (least recently used)
        cache.set("d", value: 4)

        XCTAssertNil(cache.get("a"), "LRU item 'a' should be evicted")
        XCTAssertEqual(cache.get("b"), 2)
        XCTAssertEqual(cache.get("c"), 3)
        XCTAssertEqual(cache.get("d"), 4)
        XCTAssertEqual(cache.count, 3)
    }

    func testGetPromotesToFront() {
        let cache = GenericLRUCache<String, Int>(capacity: 3)
        cache.set("a", value: 1)
        cache.set("b", value: 2)
        cache.set("c", value: 3)

        // Access "a" to promote it
        _ = cache.get("a")

        // Now adding "d" should evict "b" (now the LRU), not "a"
        cache.set("d", value: 4)

        XCTAssertEqual(cache.get("a"), 1, "'a' should still be present (was promoted)")
        XCTAssertNil(cache.get("b"), "'b' should be evicted (was LRU)")
        XCTAssertEqual(cache.get("c"), 3)
        XCTAssertEqual(cache.get("d"), 4)
    }

    func testSetExistingKeyPromotesToFront() {
        let cache = GenericLRUCache<String, Int>(capacity: 3)
        cache.set("a", value: 1)
        cache.set("b", value: 2)
        cache.set("c", value: 3)

        // Update "a" to promote it
        cache.set("a", value: 10)

        // Now "b" is LRU
        cache.set("d", value: 4)

        XCTAssertEqual(cache.get("a"), 10)
        XCTAssertNil(cache.get("b"), "'b' should be evicted")
    }

    // MARK: - Edge Cases

    func testCapacityOne() {
        let cache = GenericLRUCache<String, Int>(capacity: 1)
        cache.set("a", value: 1)
        XCTAssertEqual(cache.get("a"), 1)

        cache.set("b", value: 2)
        XCTAssertNil(cache.get("a"), "Only capacity for 1 item")
        XCTAssertEqual(cache.get("b"), 2)
        XCTAssertEqual(cache.count, 1)
    }

    func testMultipleEvictions() {
        let cache = GenericLRUCache<Int, String>(capacity: 2)

        for i in 0..<100 {
            cache.set(i, value: "val_\(i)")
        }

        // Only the last 2 should remain
        XCTAssertEqual(cache.count, 2)
        XCTAssertEqual(cache.get(99), "val_99")
        XCTAssertEqual(cache.get(98), "val_98")
        XCTAssertNil(cache.get(97))
    }

    func testCountTracking() {
        let cache = GenericLRUCache<String, Int>(capacity: 5)
        XCTAssertEqual(cache.count, 0)

        cache.set("a", value: 1)
        XCTAssertEqual(cache.count, 1)

        cache.set("b", value: 2)
        XCTAssertEqual(cache.count, 2)

        // Overwrite shouldn't change count
        cache.set("a", value: 10)
        XCTAssertEqual(cache.count, 2)
    }

    // MARK: - Concurrent Stress Test

    func testConcurrentSetAndGet() async {
        let cache = GenericLRUCache<Int, Int>(capacity: 50)

        await withTaskGroup(of: Void.self) { group in
            // Writers
            for i in 0..<100 {
                group.addTask {
                    cache.set(i, value: i * 10)
                }
            }
            // Readers (concurrent with writers)
            for i in 0..<100 {
                group.addTask {
                    _ = cache.get(i)
                }
            }
        }

        // Cache shouldn't exceed capacity
        XCTAssertLessThanOrEqual(cache.count, 50)
        // And should have some entries
        XCTAssertGreaterThan(cache.count, 0)
    }
}
