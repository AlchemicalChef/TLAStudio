import Foundation
import Combine

/// Per-document facade over `ModuleSymbolIndex`: owns a published, warm
/// snapshot of the document's cross-module symbols that completions, hover,
/// signature help, and go-to-definition read **synchronously** — UI paths
/// never wait on file IO or parsing.
///
/// Refreshes are coalesced with the generation-counter idiom (a finished
/// refresh only publishes if no newer one was scheduled), mirroring
/// `TLADocument.semanticCheckGeneration`.
@MainActor
final class CrossModuleSymbolProvider: ObservableObject {

    @Published private(set) var symbols: [ModuleSymbol] = []

    private let index: ModuleSymbolIndex
    private var generation = 0
    private var lastQuery: ModuleSymbolIndex.Query?
    private var refreshTask: Task<Void, Never>?
    private var indexObserver: NSObjectProtocol?

    init(index: ModuleSymbolIndex = .shared) {
        self.index = index
        indexObserver = NotificationCenter.default.addObserver(
            forName: .moduleSymbolIndexDidUpdate,
            object: nil,
            queue: .main
        ) { [weak self] _ in
            Task { @MainActor [weak self] in
                self?.refreshCurrentQuery()
            }
        }
    }

    /// Called after every parse with the document's current EXTENDS set.
    /// No-ops when the query is unchanged (the index notification path covers
    /// on-disk changes).
    func scheduleRefresh(extendedModules: [String], specDirectory: URL?, ownFileURL: URL?) {
        let query = ModuleSymbolIndex.Query(
            rootModules: extendedModules.sorted(),
            specDirectory: specDirectory,
            excludedFileURL: ownFileURL
        )
        guard query != lastQuery else { return }
        lastQuery = query
        refreshCurrentQuery()
    }

    /// Fire-and-forget staleness probe from feature entry points (completion
    /// keystrokes, hover, go-to-def). The *current* call still reads the warm
    /// snapshot; if anything on disk changed, the index notifies and the
    /// snapshot catches up for the next query.
    func refreshIfStaleInBackground() {
        guard let query = lastQuery else { return }
        let index = self.index
        Task.detached(priority: .utility) {
            await index.refreshIfStale(for: query)
        }
    }

    func teardown() {
        generation += 1
        // Clearing the query (not just bumping the generation) also stops a
        // notification Task dispatched just before teardown from re-populating
        // the snapshot of a dead document.
        lastQuery = nil
        refreshTask?.cancel()
        refreshTask = nil
        if let indexObserver {
            NotificationCenter.default.removeObserver(indexObserver)
        }
        indexObserver = nil
        symbols = []
    }

    private func refreshCurrentQuery() {
        guard let query = lastQuery else { return }
        refreshTask?.cancel()
        generation += 1
        let generation = self.generation

        refreshTask = Task { @MainActor [weak self] in
            guard let self else { return }
            let result = await self.index.symbols(for: query)
            guard self.generation == generation else { return }
            if self.symbols != result {
                self.symbols = result
            }
        }
    }
}
