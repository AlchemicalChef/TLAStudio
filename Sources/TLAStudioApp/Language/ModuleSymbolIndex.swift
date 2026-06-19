import Foundation
import os

// MARK: - Module Symbol

/// A symbol exported by an `EXTENDS`'d module. `symbol` ranges refer to the
/// module file's own content (tree-sitter coordinates), not the querying
/// document.
struct ModuleSymbol: Identifiable, Equatable {
    let symbol: TLASymbol
    /// Module the symbol was found in (the name the EXTENDS chain requested).
    let moduleName: String
    /// Resolved on-disk location of the module file.
    let fileURL: URL
    /// 1 = direct EXTENDS of the querying document, 2+ = transitive.
    let depth: Int

    var id: String { "\(moduleName)|\(symbol.name)|\(symbol.range.start.line)" }
}

// MARK: - Standard Module Catalog

/// Modules whose symbols the Rust core already provides via its hardcoded
/// `STANDARD_MODULES` data — the index skips these to avoid duplicates.
enum StandardModuleCatalog {
    static let names: Set<String> = [
        "Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags", "TLC", "TLAPS"
    ]

    /// Whether a resolved module file lives in a bundled/standard-library
    /// location rather than the user's project.
    static func isStandardLibraryLocation(_ url: URL) -> Bool {
        let path = url.standardizedFileURL.path
        if let resources = Bundle.main.resourcePath {
            let resourcesPath = URL(fileURLWithPath: resources).standardizedFileURL.path
            if path.hasPrefix(resourcesPath + "/") {
                return true
            }
        }
        return BinaryDiscovery.standardModulesDirectories().contains { directory in
            path.hasPrefix(directory.standardizedFileURL.path + "/")
        }
    }
}

// MARK: - Module Symbol Index

/// Cross-module symbol index: resolves the transitive `EXTENDS` closure of a
/// document, parses each module file with the tree-sitter core, and caches the
/// exported symbols by (path, mtime, size).
///
/// Powers cross-module completions, hover, signature help, and
/// go-to-definition. Queries against warm cache are pure dictionary work;
/// cold files are read and parsed inside the actor using its **own** core
/// instance so index parses never evict the editor's shared parse LRU.
actor ModuleSymbolIndex {

    static let shared = ModuleSymbolIndex()

    struct Query: Equatable, Sendable {
        /// Direct EXTENDS of the querying document.
        let rootModules: [String]
        /// Directory of the querying document (searched first by findModule).
        let specDirectory: URL?
        /// The querying document's own file — never indexed (self-extends and
        /// modules that resolve back to the document itself are skipped).
        let excludedFileURL: URL?
    }

    // MARK: Caps

    static let maxModules = 24
    static let maxDepth = 6
    static let maxFileSize = 2 * 1024 * 1024
    static let maxSymbolsPerModule = 2000
    static let cacheCapacity = 64
    static let negativeCacheTTL: TimeInterval = 30
    static let statThrottle: TimeInterval = 2

    // MARK: State

    private struct IndexedModule {
        let moduleName: String
        let fileURL: URL
        let mtime: Date
        let fileSize: Int
        let symbols: [TLASymbol]
        let extends: [String]
    }

    private let core: any TLACoreProtocol
    private let statThrottle: TimeInterval
    private let negativeCacheTTL: TimeInterval
    private let logger = Log.logger(category: "ModuleSymbolIndex")

    private var cache: [String: IndexedModule] = [:]
    private var cacheOrder: [String] = []
    /// "name|specDir" → time of last failed resolution.
    private var negativeCache: [String: Date] = [:]
    private var lastStat: [String: Date] = [:]

    /// - Parameters:
    ///   - core: Test seam. Defaults to a dedicated core instance so index
    ///     parsing never competes with the editor's caches.
    ///   - statThrottle/negativeCacheTTL: Test seams for time-based behavior.
    init(
        core: (any TLACoreProtocol)? = nil,
        statThrottle: TimeInterval = ModuleSymbolIndex.statThrottle,
        negativeCacheTTL: TimeInterval = ModuleSymbolIndex.negativeCacheTTL
    ) {
        self.core = core ?? TLACoreFactory.create()
        self.statThrottle = statThrottle
        self.negativeCacheTTL = negativeCacheTTL
    }

    // MARK: - Queries

    /// Resolve + (re)index the transitive EXTENDS closure and return the
    /// flattened symbols: BFS order, deduplicated by name with the
    /// nearest-depth occurrence winning.
    /// Canonical cache key for a module file: standardized AND symlink-resolved,
    /// so an aliased path can't be double-indexed or dodge self-exclusion.
    private static func canonicalPath(of url: URL) -> String {
        url.standardizedFileURL.resolvingSymlinksInPath().path
    }

    func symbols(for query: Query) async -> [ModuleSymbol] {
        var visited = Set<String>()
        if let excluded = query.excludedFileURL {
            visited.insert(Self.canonicalPath(of: excluded))
        }

        var queue: [(name: String, depth: Int)] = query.rootModules.map { ($0, 1) }
        var requestedNames = Set(query.rootModules)
        var queueIndex = 0
        var resolvedCount = 0
        var collected: [ModuleSymbol] = []

        while queueIndex < queue.count, resolvedCount < Self.maxModules {
            let (name, depth) = queue[queueIndex]
            queueIndex += 1

            guard depth <= Self.maxDepth else { continue }
            guard !StandardModuleCatalog.names.contains(name) else { continue }

            let negativeKey = "\(name)|\(query.specDirectory?.path ?? "")"
            if let failedAt = negativeCache[negativeKey],
               Date().timeIntervalSince(failedAt) < negativeCacheTTL {
                continue
            }

            guard let url = BinaryDiscovery.findModule(named: name, specDirectory: query.specDirectory) else {
                recordNegative(negativeKey)
                continue
            }
            let path = Self.canonicalPath(of: url)
            guard visited.insert(path).inserted else { continue }
            guard !StandardModuleCatalog.isStandardLibraryLocation(url) else { continue }

            guard let module = await indexedModule(named: name, at: url) else { continue }
            resolvedCount += 1

            for symbol in module.symbols {
                collected.append(ModuleSymbol(
                    symbol: symbol,
                    moduleName: name,
                    fileURL: module.fileURL,
                    depth: depth
                ))
            }

            if depth < Self.maxDepth {
                for extendedName in module.extends where requestedNames.insert(extendedName).inserted {
                    queue.append((extendedName, depth + 1))
                }
            }
        }

        // Nearest-depth shadowing: BFS order means the first occurrence of a
        // name is from the closest module.
        var seenNames = Set<String>()
        return collected.filter { seenNames.insert($0.symbol.name).inserted }
    }

    /// Cheap mtime/size stat pass over cached entries (throttled per path);
    /// drops stale entries and notifies so providers re-query. Returns true
    /// when anything was stale.
    @discardableResult
    func refreshIfStale(for query: Query) async -> Bool {
        let now = Date()
        var changed = false

        for (path, module) in cache {
            if let last = lastStat[path], now.timeIntervalSince(last) < statThrottle {
                continue
            }
            lastStat[path] = now

            let attributes = try? FileManager.default.attributesOfItem(atPath: path)
            let mtime = attributes?[.modificationDate] as? Date
            let size = (attributes?[.size] as? NSNumber)?.intValue
            if mtime != module.mtime || size != module.fileSize {
                removeFromCache(path)
                changed = true
            }
        }

        if changed {
            postDidUpdate()
        }
        return changed
    }

    /// Drop the cache entry for a file (called when a document is saved) and
    /// clear failed resolutions — the save may have created a module that was
    /// previously missing. Always notifies so open documents re-query.
    func invalidate(fileURL: URL) {
        removeFromCache(Self.canonicalPath(of: fileURL))
        negativeCache.removeAll()
        postDidUpdate()
    }

    /// Record a failed resolution, keeping the negative cache bounded (unlike
    /// the LRU-capped positive cache it has no natural ceiling — every distinct
    /// unresolvable name in any directory adds a key).
    private func recordNegative(_ key: String) {
        negativeCache[key] = Date()
        if negativeCache.count > 256 {
            let newest = negativeCache.sorted { $0.value > $1.value }.prefix(128)
            negativeCache = Dictionary(uniqueKeysWithValues: Array(newest))
        }
    }

    func invalidateAll() {
        cache.removeAll()
        cacheOrder.removeAll()
        negativeCache.removeAll()
        lastStat.removeAll()
        postDidUpdate()
    }

    // MARK: - Indexing

    private func indexedModule(named name: String, at url: URL) async -> IndexedModule? {
        let standardizedURL = url.standardizedFileURL
        let path = Self.canonicalPath(of: url)

        guard let attributes = try? FileManager.default.attributesOfItem(atPath: path),
              // Regular files only: a FIFO/socket named `<Module>.tla` would
              // otherwise wedge this actor on the blocking String(contentsOf:)
              // read below (e2e Low / security hardening).
              (attributes[.type] as? FileAttributeType) == .typeRegular,
              let mtime = attributes[.modificationDate] as? Date,
              let size = (attributes[.size] as? NSNumber)?.intValue else {
            return nil
        }
        guard size <= Self.maxFileSize else {
            logger.debug("Skipping oversized module \(name) (\(size) bytes)")
            return nil
        }
        // Record the stat timestamp only for paths we'll actually cache: an
        // oversized/skipped path never enters the cache, so removeFromCache would
        // never evict its lastStat entry — recording it here would leak (e2e Low).
        lastStat[path] = Date()

        if let cached = cache[path], cached.mtime == mtime, cached.fileSize == size {
            touch(path)
            return cached
        }

        guard let content = try? String(contentsOf: standardizedURL, encoding: .utf8),
              let parseResult = try? await core.parse(content) else {
            return nil
        }
        let allSymbols = await core.getSymbols(from: parseResult)

        let module = IndexedModule(
            moduleName: name,
            fileURL: standardizedURL,
            mtime: mtime,
            fileSize: size,
            symbols: exportedSymbols(from: allSymbols, content: content),
            extends: TLADocument.extendedModuleNames(in: content).sorted()
        )
        store(module, at: path)
        return module
    }

    /// A module's exports: the module node's children (falling back to the
    /// top-level symbols for error-recovered parses), minus `LOCAL`
    /// definitions, capped.
    private func exportedSymbols(from symbols: [TLASymbol], content: String) -> [TLASymbol] {
        var exports = symbols.first { $0.kind == .module }?.children ?? symbols
        exports = exports.filter { $0.kind != .module }

        let lines = content.components(separatedBy: "\n")
        let withoutLocals = exports.filter { symbol in
            let line = Int(symbol.range.start.line)
            guard line < lines.count else { return true }
            // Match a leading `LOCAL` keyword regardless of the following
            // whitespace (space OR tab), so `LOCAL\tFoo` is filtered too (e2e Low).
            let trimmed = lines[line].trimmingCharacters(in: .whitespaces)
            return trimmed.prefix { !$0.isWhitespace } != "LOCAL"
        }
        return Array(withoutLocals.prefix(Self.maxSymbolsPerModule))
    }

    // MARK: - Cache plumbing

    private func store(_ module: IndexedModule, at path: String) {
        if cache[path] == nil {
            cacheOrder.append(path)
        }
        cache[path] = module
        touch(path)
        while cache.count > Self.cacheCapacity, let oldest = cacheOrder.first {
            removeFromCache(oldest)
        }
    }

    private func touch(_ path: String) {
        if let index = cacheOrder.firstIndex(of: path) {
            cacheOrder.remove(at: index)
            cacheOrder.append(path)
        }
    }

    private func removeFromCache(_ path: String) {
        cache.removeValue(forKey: path)
        lastStat.removeValue(forKey: path)
        if let index = cacheOrder.firstIndex(of: path) {
            cacheOrder.remove(at: index)
        }
    }

    private nonisolated func postDidUpdate() {
        Task { @MainActor in
            NotificationCenter.default.post(name: .moduleSymbolIndexDidUpdate, object: nil)
        }
    }
}
