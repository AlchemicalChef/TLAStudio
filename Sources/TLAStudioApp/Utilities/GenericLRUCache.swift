import Foundation

// MARK: - Generic LRU Cache

/// Thread-safe generic LRU cache with O(1) get/set/eviction operations.
/// Uses a doubly-linked list for LRU ordering and a dictionary for O(1) key lookup.
final class GenericLRUCache<Key: Hashable, Value> {
    private let capacity: Int
    private var cache: [Key: GenericLRUNode<Key, Value>] = [:]
    private let lock = NSLock()

    /// Sentinel node for doubly-linked list (head = most recently used)
    private var head: GenericLRUNode<Key, Value>?
    private var tail: GenericLRUNode<Key, Value>?

    init(capacity: Int) {
        precondition(capacity > 0, "LRU cache capacity must be positive")
        self.capacity = capacity
    }

    deinit {
        // Clear the linked list to allow prompt deallocation.
        // With weak prev, there are no retain cycles, but clearing
        // the chain avoids a deep recursive dealloc stack for large caches.
        var node = head
        while let current = node {
            let next = current.next
            current.next = nil
            node = next
        }
    }

    /// Get value for key, marking it as most recently used. O(1)
    func get(_ key: Key) -> Value? {
        lock.lock()
        defer { lock.unlock() }
        guard let node = cache[key] else { return nil }
        moveToFront(node)
        return node.value
    }

    /// Set value for key, evicting LRU entry if at capacity. O(1)
    func set(_ key: Key, value: Value) {
        lock.lock()
        defer { lock.unlock() }
        if let node = cache[key] {
            // Update existing
            node.value = value
            moveToFront(node)
        } else {
            // Evict oldest if at capacity
            while cache.count >= capacity {
                removeLRU()
            }

            // Add new node
            let node = GenericLRUNode(key: key, value: value)
            cache[key] = node
            addToFront(node)
        }
    }

    /// Current number of entries in the cache.
    var count: Int {
        lock.lock()
        defer { lock.unlock() }
        return cache.count
    }

    // MARK: - Private List Operations (all O(1), must be called with lock held)

    private func addToFront(_ node: GenericLRUNode<Key, Value>) {
        node.prev = nil
        node.next = head
        head?.prev = node
        head = node
        if tail == nil {
            tail = node
        }
    }

    private func removeNode(_ node: GenericLRUNode<Key, Value>) {
        if node === head {
            head = node.next
        }
        if node === tail {
            tail = node.prev
        }
        node.prev?.next = node.next
        node.next?.prev = node.prev
        node.prev = nil
        node.next = nil
    }

    private func moveToFront(_ node: GenericLRUNode<Key, Value>) {
        guard node !== head else { return }
        removeNode(node)
        addToFront(node)
    }

    private func removeLRU() {
        guard let lru = tail else { return }
        cache.removeValue(forKey: lru.key)
        removeNode(lru)
    }
}

/// Node for GenericLRUCache doubly-linked list.
final class GenericLRUNode<Key: Hashable, Value> {
    let key: Key
    var value: Value
    weak var prev: GenericLRUNode?
    var next: GenericLRUNode?

    init(key: Key, value: Value) {
        self.key = key
        self.value = value
    }
}
