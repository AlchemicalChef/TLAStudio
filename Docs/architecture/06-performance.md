# Performance Optimization Architecture

## Performance Targets

| Metric | Baseline (JVM TLA Toolbox) | Target | Strategy |
|--------|----------------------------|--------|----------|
| App cold start | 3-5s | <500ms | Lazy loading, precompiled |
| TLC first state | 2-3s | <100ms | GraalVM AOT |
| File open (100K lines) | 2-3s | <200ms | Memory-mapped, streaming |
| Keystroke latency | 50-100ms | <8ms | Incremental, off-main-thread |
| Syntax highlight | 100-200ms | <5ms | Visible-only, incremental |
| Proof dispatch | 500ms | <50ms | Parallel backends |

## Apple Silicon Optimization

### Core Affinity

Apple Silicon has Performance (P) and Efficiency (E) cores. Route tasks appropriately:

| Task | Core Type | QoS Class |
|------|-----------|-----------|
| Model checking | P-cores | .userInitiated |
| Proof verification | P-cores | .userInitiated |
| UI updates | P-cores | .userInteractive |
| File watching | E-cores | .utility |
| Background indexing | E-cores | .background |
| Cache maintenance | E-cores | .background |

```swift
// High-priority compute task
Task(priority: .high) {
    await modelChecker.explore()
}

// Background task on E-cores
DispatchQueue.global(qos: .utility).async {
    fileWatcher.start()
}
```

### Unified Memory

Apple Silicon's unified memory enables zero-copy sharing between CPU and GPU:

```swift
// Create buffer accessible by both CPU and GPU
let device = MTLCreateSystemDefaultDevice()!
let buffer = device.makeBuffer(
    length: size,
    options: .storageModeShared  // CPU + GPU access
)!
```

Use cases:
- State fingerprint computation (GPU accelerated)
- Large text rendering
- Parallel syntax highlighting

### Metal Compute

Batch operations suitable for GPU:

```swift
// GPU-accelerated fingerprint hashing
func computeFingerprints(states: [State]) -> [UInt64] {
    // Encode states to Metal buffer
    // Dispatch compute shader
    // Read results (zero-copy)
}
```

## TLC Model Checker Optimization

### GraalVM Profile-Guided Optimization

```bash
# 1. Build instrumented binary
native-image --pgo-instrument -jar tla2tools.jar -o tlc-instrumented

# 2. Run representative workloads
./tlc-instrumented benchmark/DieHard.tla
./tlc-instrumented benchmark/TwoPhase.tla
./tlc-instrumented benchmark/Paxos.tla

# 3. Build optimized binary
native-image --pgo=default.iprof -O3 -jar tla2tools.jar -o tlc-native
```

Expected improvements: 15-25% faster state exploration.

### Parallel State Exploration

Use work-stealing queues for load balancing across cores:

```swift
actor StateExplorer {
    private var workQueues: [WorkStealingDeque<State>]
    
    func explore(workers: Int) async {
        await withTaskGroup(of: Void.self) { group in
            for id in 0..<workers {
                group.addTask(priority: .high) {
                    await self.workerLoop(id: id)
                }
            }
        }
    }
    
    private func workerLoop(id: Int) async {
        while true {
            // Try own queue first
            if let state = workQueues[id].popBottom() {
                process(state)
            } else {
                // Steal from other queues
                for other in 0..<workQueues.count where other != id {
                    if let state = workQueues[other].steal() {
                        process(state)
                        break
                    }
                }
            }
        }
    }
}
```

### Disk-Backed State Storage

For models exceeding RAM, use memory-mapped files with bloom filter:

```swift
class DiskBackedStateStore {
    private var bloomFilter: BloomFilter<UInt64>  // Fast negative lookup
    private var mappedFile: UnsafeMutableRawBufferPointer
    
    func contains(fingerprint: UInt64) -> Bool {
        // Fast path: bloom filter says no
        if !bloomFilter.mightContain(fingerprint) {
            return false
        }
        // Slow path: check disk
        return diskLookup(fingerprint)
    }
}
```

## Editor Optimization

### Incremental Syntax Highlighting

Only re-highlight changed + visible regions:

```swift
func updateHighlights(edit: TextEdit, visibleRange: Range<Int>) {
    // 1. Apply edit to tree-sitter tree
    currentTree?.applyEdit(edit.toTSEdit())
    
    // 2. Re-parse incrementally
    let newTree = parser.parse(source: content, oldTree: currentTree)
    
    // 3. Get changed ranges
    let changedRanges = currentTree?.changedRanges(comparedTo: newTree)
    
    // 4. Re-highlight only changed ∩ visible
    for range in changedRanges where range.overlaps(visibleRange) {
        highlightRange(range)
    }
    
    currentTree = newTree
}
```

### Virtual Scrolling

For million-line files, only render visible lines:

```swift
class VirtualTextView {
    private var linePool: ObjectPool<LineView>  // Reuse views
    private var visibleLines: [Int: LineView] = [:]
    
    override func draw(_ dirtyRect: NSRect) {
        let startLine = lineAtOffset(visibleRect.minY)
        let endLine = lineAtOffset(visibleRect.maxY)
        
        // Recycle lines outside visible range
        for (line, view) in visibleLines {
            if line < startLine || line > endLine {
                linePool.recycle(view)
                visibleLines.removeValue(forKey: line)
            }
        }
        
        // Create/update visible lines
        for line in startLine...endLine {
            let view = visibleLines[line] ?? linePool.dequeue()
            view.configure(line: line, content: lineContent(line))
            visibleLines[line] = view
        }
    }
}
```

### Background Processing Pipeline

Move heavy work off main thread:

```swift
actor TextProcessingPipeline {
    private let parseQueue = OperationQueue()      // QoS: .userInitiated
    private let highlightQueue = OperationQueue()  // QoS: .userInteractive
    private let indexQueue = OperationQueue()      // QoS: .utility (E-cores)
    
    func processChange(_ change: TextChange) async {
        // Parse (P-cores)
        let parseResult = await withCheckedContinuation { cont in
            parseQueue.addOperation {
                cont.resume(returning: self.parser.parse(change))
            }
        }
        
        // Highlight visible (highest priority)
        async let highlights = highlightQueue.addOperation { ... }
        
        // Index symbols (background, E-cores)
        indexQueue.addOperation {
            self.symbolIndex.update(from: parseResult)
        }
        
        // Deliver highlights immediately
        await MainActor.run {
            editor.applyHighlights(await highlights)
        }
    }
}
```

## TLAPS Optimization

### Parallel Proof Dispatch

Check multiple obligations simultaneously:

```swift
actor ParallelProofChecker {
    private let maxParallel = 4
    
    func check(obligations: [ProofObligation]) async -> [ProofResult] {
        var results: [ProofResult] = []
        var pending = obligations[...]
        
        await withTaskGroup(of: ProofResult.self) { group in
            // Start initial batch
            for _ in 0..<min(maxParallel, pending.count) {
                let ob = pending.removeFirst()
                group.addTask { await self.checkOne(ob) }
            }
            
            // Process results, add more work
            for await result in group {
                results.append(result)
                if let next = pending.first {
                    pending.removeFirst()
                    group.addTask { await self.checkOne(next) }
                }
            }
        }
        
        return results
    }
}
```

### Speculative Multi-Backend Execution

Try multiple provers, take first success:

```swift
func proveSpeculatively(ob: ProofObligation) async -> ProofResult {
    try await withThrowingTaskGroup(of: ProofResult.self) { group in
        // Launch all backends
        for backend in [.zenon, .z3, .spass] {
            group.addTask {
                try await self.runProver(ob, backend: backend)
            }
        }
        
        // Return first success, cancel others
        while let result = try await group.next() {
            if result.success {
                group.cancelAll()
                return result
            }
        }
        throw ProofError.allFailed
    }
}
```

### Similarity-Based Cache

Find proofs of similar obligations:

```swift
actor SmartProofCache {
    private var exactCache: [String: ProofResult] = [:]
    private var lshIndex: LocalitySensitiveHash
    
    func lookup(obligation: ProofObligation) -> CacheResult {
        // Exact match
        if let result = exactCache[obligation.fingerprint] {
            return .exactMatch(result)
        }
        
        // Similar obligation (suggest same backend)
        let similar = lshIndex.findSimilar(obligation.text, threshold: 0.85)
        if let match = similar.first, let result = exactCache[match] {
            return .similarMatch(result, backend: result.backend)
        }
        
        return .miss
    }
}
```

## Memory Optimization

### String Interning

Reuse common strings (keywords, operators):

```swift
class StringInterner {
    private var table: [String: String] = [:]
    
    func intern(_ s: String) -> String {
        if s.count > 50 { return s }  // Don't intern long strings
        if let existing = table[s] { return existing }
        table[s] = s
        return s
    }
}
```

### Compact Syntax Nodes

Pack node data into minimal space:

```swift
struct CompactNode {
    // 8 bytes total vs 40+ for full struct
    private var packed: UInt64
    // Bits 0-15:  type
    // Bits 16-31: start line
    // Bits 32-47: end line
    // Bits 48-55: start col
    // Bits 56-63: end col
}
```

## I/O Optimization

### Streaming File Parser

Parse large files without loading entirely:

```swift
func parseFile(url: URL) async throws -> ParseResult {
    let handle = try FileHandle(forReadingFrom: url)
    var tree: ParseResult?
    
    while let chunk = try handle.read(upToCount: 64 * 1024) {
        tree = parser.parseChunk(chunk, previousTree: tree)
        await Task.yield()  // Allow other work
    }
    
    return tree ?? .empty
}
```

### Dispatch I/O

High-performance async file operations:

```swift
func readFile(url: URL) async throws -> Data {
    try await withCheckedThrowingContinuation { cont in
        let channel = DispatchIO(
            type: .stream,
            path: url.path,
            oflag: O_RDONLY,
            mode: 0,
            queue: .global(qos: .userInitiated)
        ) { _ in }
        
        var data = Data()
        channel.read(offset: 0, length: .max, queue: .global()) { done, chunk, _ in
            if let chunk { data.append(contentsOf: chunk) }
            if done { cont.resume(returning: data) }
        }
    }
}
```

## Performance Monitoring

Built-in profiling:

```swift
class PerformanceMonitor {
    static let shared = PerformanceMonitor()
    private var samples: [String: [TimeInterval]] = [:]
    
    func measure<T>(_ name: String, _ op: () throws -> T) rethrows -> T {
        let start = CFAbsoluteTimeGetCurrent()
        defer {
            let duration = CFAbsoluteTimeGetCurrent() - start
            samples[name, default: []].append(duration)
        }
        return try op()
    }
    
    func stats(for name: String) -> (p50: Double, p95: Double, p99: Double)? {
        guard let s = samples[name]?.sorted(), !s.isEmpty else { return nil }
        return (
            s[s.count / 2],
            s[Int(Double(s.count) * 0.95)],
            s[Int(Double(s.count) * 0.99)]
        )
    }
}

// Usage
let result = PerformanceMonitor.shared.measure("parseDocument") {
    parser.parse(document)
}
```

## Implementation Checklist

- [ ] Implement work-stealing deque for TLC parallelism
- [ ] Set up GraalVM PGO build pipeline
- [ ] Create Metal compute shader for fingerprinting
- [ ] Implement incremental highlighter
- [ ] Implement virtual scrolling text view
- [ ] Set up background processing pipeline
- [ ] Implement parallel proof checker
- [ ] Add bloom filter for disk-backed state store
- [ ] Add performance monitoring hooks
- [ ] Benchmark all targets
