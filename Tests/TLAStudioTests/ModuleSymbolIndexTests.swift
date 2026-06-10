import XCTest
@testable import TLAStudioApp

final class ModuleSymbolIndexTests: TempDirectoryTestCase {

    private var index: ModuleSymbolIndex!

    override func setUp() async throws {
        try await super.setUp()
        // Fast time behavior + dedicated core; fresh instance isolates caches.
        index = ModuleSymbolIndex(statThrottle: 0, negativeCacheTTL: 30)
    }

    override func tearDown() async throws {
        index = nil
        try await super.tearDown()
    }

    @discardableResult
    private func writeModule(_ name: String, _ body: String) throws -> URL {
        let url = tempDirectory.appendingPathComponent("\(name).tla")
        let content = """
        ---- MODULE \(name) ----
        \(body)
        ====
        """
        try content.write(to: url, atomically: true, encoding: .utf8)
        return url
    }

    private func query(_ roots: [String], excluding: URL? = nil) -> ModuleSymbolIndex.Query {
        ModuleSymbolIndex.Query(
            rootModules: roots,
            specDirectory: tempDirectory,
            excludedFileURL: excluding
        )
    }

    // MARK: - Basics

    func testDirectExtendsExportsSymbols() async throws {
        try writeModule("HelperZq", """
        EXTENDS Naturals
        VARIABLE hv
        CONSTANT hc
        HelperOp(a, b) == a + b
        """)

        let symbols = await index.symbols(for: query(["HelperZq"]))

        let op = try XCTUnwrap(symbols.first { $0.symbol.name == "HelperOp" })
        XCTAssertEqual(op.moduleName, "HelperZq")
        XCTAssertEqual(op.depth, 1)
        XCTAssertEqual(op.symbol.parameters, ["a", "b"])
        XCTAssertEqual(op.fileURL.lastPathComponent, "HelperZq.tla")
        XCTAssertTrue(symbols.contains { $0.symbol.name == "hv" })
        XCTAssertTrue(symbols.contains { $0.symbol.name == "hc" })
    }

    func testTransitiveExtends() async throws {
        try writeModule("AlphaZq", "EXTENDS BetaZq\nAOp == 1")
        try writeModule("BetaZq", "EXTENDS GammaZq\nBOp == 2")
        try writeModule("GammaZq", "GOp == 3")

        let symbols = await index.symbols(for: query(["AlphaZq"]))

        XCTAssertEqual(symbols.first { $0.symbol.name == "BOp" }?.depth, 2)
        XCTAssertEqual(symbols.first { $0.symbol.name == "GOp" }?.depth, 3)
    }

    func testCycleTerminatesWithoutDuplicates() async throws {
        try writeModule("CycAZq", "EXTENDS CycBZq\nAOp == 1")
        try writeModule("CycBZq", "EXTENDS CycAZq\nBOp == 2")

        let symbols = await index.symbols(for: query(["CycAZq"]))

        XCTAssertEqual(symbols.filter { $0.symbol.name == "AOp" }.count, 1)
        XCTAssertEqual(symbols.filter { $0.symbol.name == "BOp" }.count, 1)
    }

    func testOwnFileIsExcluded() async throws {
        let main = try writeModule("MainZq", "EXTENDS SelfHelperZq\nMainOp == 1")
        try writeModule("SelfHelperZq", "EXTENDS MainZq\nHOp == 2")

        let symbols = await index.symbols(for: query(["SelfHelperZq"], excluding: main))

        XCTAssertTrue(symbols.contains { $0.symbol.name == "HOp" })
        XCTAssertFalse(symbols.contains { $0.symbol.name == "MainOp" },
                       "the querying document's own symbols must not come back through the index")
    }

    func testMissingModuleIsSkippedSilently() async throws {
        try writeModule("PartialZq", "EXTENDS TotallyMissingModuleZq\nPOp == 1")

        let symbols = await index.symbols(for: query(["PartialZq"]))
        XCTAssertTrue(symbols.contains { $0.symbol.name == "POp" })
        XCTAssertFalse(symbols.contains { $0.moduleName == "TotallyMissingModuleZq" })
    }

    func testStandardModulesAreNotIndexed() async throws {
        try writeModule("StdUserZq", "EXTENDS Naturals, Sequences\nSOp == 1")

        let symbols = await index.symbols(for: query(["StdUserZq"]))
        XCTAssertTrue(symbols.allSatisfy { $0.moduleName == "StdUserZq" })
    }

    // MARK: - Shadowing & filtering

    func testNearestDepthWinsForDuplicateNames() async throws {
        try writeModule("NearZq", "EXTENDS FarZq\nShared == \"near\"")
        try writeModule("FarZq", "Shared == \"far\"\nFarOnly == 1")

        let symbols = await index.symbols(for: query(["NearZq"]))

        let shared = symbols.filter { $0.symbol.name == "Shared" }
        XCTAssertEqual(shared.count, 1)
        XCTAssertEqual(shared.first?.moduleName, "NearZq")
        XCTAssertTrue(symbols.contains { $0.symbol.name == "FarOnly" })
    }

    func testLocalDefinitionsAreFiltered() async throws {
        try writeModule("LocalsZq", """
        PublicOp == 1
        LOCAL PrivateOp == 2
        """)

        let symbols = await index.symbols(for: query(["LocalsZq"]))
        XCTAssertTrue(symbols.contains { $0.symbol.name == "PublicOp" })
        XCTAssertFalse(symbols.contains { $0.symbol.name == "PrivateOp" })
    }

    // MARK: - Invalidation

    func testInvalidateReflectsRewrittenFile() async throws {
        let url = try writeModule("MutZq", "FirstOp == 1")
        var symbols = await index.symbols(for: query(["MutZq"]))
        XCTAssertTrue(symbols.contains { $0.symbol.name == "FirstOp" })

        try writeModule("MutZq", "FirstOp == 1\nSecondOp == 2")
        await index.invalidate(fileURL: url)

        symbols = await index.symbols(for: query(["MutZq"]))
        XCTAssertTrue(symbols.contains { $0.symbol.name == "SecondOp" })
    }

    func testRefreshIfStaleDetectsMtimeChange() async throws {
        let url = try writeModule("StaleZq", "OldOp == 1")
        _ = await index.symbols(for: query(["StaleZq"]))

        try writeModule("StaleZq", "OldOp == 1\nNewOp == 2")
        // Force a distinct mtime regardless of filesystem granularity.
        try FileManager.default.setAttributes(
            [.modificationDate: Date().addingTimeInterval(10)],
            ofItemAtPath: url.path
        )

        let changed = await index.refreshIfStale(for: query(["StaleZq"]))
        XCTAssertTrue(changed)

        let symbols = await index.symbols(for: query(["StaleZq"]))
        XCTAssertTrue(symbols.contains { $0.symbol.name == "NewOp" })
    }

    // MARK: - Caps

    func testModuleCapBoundsLongChains() async throws {
        for moduleIndex in 0..<8 {
            let next = moduleIndex < 7 ? "EXTENDS ChainZq\(moduleIndex + 1)\n" : ""
            try writeModule("ChainZq\(moduleIndex)", "\(next)ChainOp\(moduleIndex) == \(moduleIndex)")
        }

        let symbols = await index.symbols(for: query(["ChainZq0"]))
        // maxDepth = 6: depths 1...6 indexed, depth 7 (ChainZq6's extends → ChainZq7)...
        // ChainZq0 is depth 1, so the deepest reachable is ChainZq5 at depth 6.
        XCTAssertTrue(symbols.contains { $0.symbol.name == "ChainOp5" })
        XCTAssertFalse(symbols.contains { $0.symbol.name == "ChainOp6" })
    }
}

// MARK: - Provider Tests

@MainActor
final class CrossModuleSymbolProviderTests: XCTestCase {

    func testScheduleRefreshPublishesSnapshot() async throws {
        let directory = FileManager.default.temporaryDirectory
            .appendingPathComponent("provider-test-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: directory, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: directory) }

        let content = "---- MODULE ProvHelperZq ----\nPOp == 1\n===="
        try content.write(
            to: directory.appendingPathComponent("ProvHelperZq.tla"),
            atomically: true, encoding: .utf8
        )

        let provider = CrossModuleSymbolProvider(index: ModuleSymbolIndex(statThrottle: 0))
        provider.scheduleRefresh(
            extendedModules: ["ProvHelperZq"],
            specDirectory: directory,
            ownFileURL: nil
        )

        let deadline = Date().addingTimeInterval(5)
        while provider.symbols.isEmpty && Date() < deadline {
            try await Task.sleep(nanoseconds: 20_000_000)
        }
        XCTAssertTrue(provider.symbols.contains { $0.symbol.name == "POp" })
        provider.teardown()
        XCTAssertTrue(provider.symbols.isEmpty)
    }
}
