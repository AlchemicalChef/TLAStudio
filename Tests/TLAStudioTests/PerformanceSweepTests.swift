import XCTest
@testable import TLAStudioApp

private actor InvocationCounter {
    private var parseCount = 0

    func increment() {
        parseCount += 1
    }

    func value() -> Int {
        parseCount
    }
}

private struct MockTLACore: TLACoreProtocol {
    let parseCounter: InvocationCounter
    let symbolCounter: InvocationCounter?
    let parseDelayNanoseconds: UInt64

    func parse(_ source: String) async throws -> TLAParseResult {
        await parseCounter.increment()
        try? await Task.sleep(nanoseconds: parseDelayNanoseconds)
        return TLAParseResult(isValid: true, diagnostics: [], source: source)
    }

    func getSymbols(from result: TLAParseResult) async -> [TLASymbol] {
        await symbolCounter?.increment()
        return [
            TLASymbol(
                name: "Init",
                kind: .operator,
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 4)
                ),
                selectionRange: nil,
                children: [],
                parameters: []
            )
        ]
    }
    func getHighlights(from result: TLAParseResult, in range: TLARange) async -> [TLAHighlightToken] { [] }
    func getCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLACompletionItem] { [] }
    func analyzeContext(from result: TLAParseResult, at position: TLAPosition) async -> TLACompletionContext { .unknown }
    func getDetailedCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLADetailedCompletionItem] { [] }
    func getSignatureHelp(from result: TLAParseResult, at position: TLAPosition) async -> TLASignatureHelp? { nil }
}

final class PerformanceSweepTests: XCTestCase {

    @MainActor
    func testParseCoalescesConcurrentRequestsForSameSource() async throws {
        let counter = InvocationCounter()
        let wrapper = TLACoreWrapper(
            core: MockTLACore(parseCounter: counter, symbolCounter: nil, parseDelayNanoseconds: 50_000_000),
            parseCacheCapacity: 2
        )

        async let first = wrapper.parse("---- MODULE Test ----\n====")
        async let second = wrapper.parse("---- MODULE Test ----\n====")

        let (resultA, resultB) = try await (first, second)
        let parseCount = await counter.value()

        XCTAssertEqual(resultA.source, resultB.source)
        XCTAssertEqual(parseCount, 1)
    }

    @MainActor
    func testGetSymbolsUsesCacheForRepeatedLookup() async throws {
        let parseCounter = InvocationCounter()
        let symbolCounter = InvocationCounter()
        let wrapper = TLACoreWrapper(
            core: MockTLACore(
                parseCounter: parseCounter,
                symbolCounter: symbolCounter,
                parseDelayNanoseconds: 0
            ),
            parseCacheCapacity: 2
        )

        let source = """
        ---- MODULE Test ----
        VARIABLES x
        Init == x = 0
        ====
        """

        let firstResult = try await wrapper.parse(source)
        _ = await wrapper.getSymbols(from: firstResult)
        _ = await wrapper.getSymbols(from: firstResult)

        let cachedResult = try await wrapper.parse(source)
        _ = await wrapper.getSymbols(from: cachedResult)

        let parseInvocations = await parseCounter.value()
        let symbolInvocations = await symbolCounter.value()

        XCTAssertEqual(parseInvocations, 1)
        XCTAssertEqual(symbolInvocations, 1)
    }

    @MainActor
    func testLazyTraceLoadsOnlyWhenRequested() async {
        let document = TLADocument()
        let lazyTrace = LazyErrorTrace(
            type: .invariantViolation,
            message: "Counterexample",
            states: [
                TraceState(id: 0, action: "Init", variables: ["x": .int(0)]),
                TraceState(id: 1, action: "Next", variables: ["x": .int(1)])
            ],
            loopStart: nil,
            violatedProperty: "TypeOK"
        )

        document.lastTLCResult = ModelCheckResult(
            sessionId: UUID(),
            success: false,
            statesFound: 2,
            distinctStates: 2,
            duration: 0.1,
            coverage: [],
            errorTrace: nil,
            message: "Invariant violated",
            lazyErrorTrace: lazyTrace
        )

        let viewModel = ModelCheckViewModel(document: document)

        await viewModel.refreshLoadedErrorTrace(loadIfNeeded: false)
        XCTAssertNil(viewModel.loadedErrorTrace)
        XCTAssertNil(viewModel.errorTrace)
        XCTAssertFalse(viewModel.isLoadingErrorTrace)

        await viewModel.refreshLoadedErrorTrace(loadIfNeeded: true)
        XCTAssertEqual(viewModel.errorTrace?.states.count, 2)
        XCTAssertEqual(viewModel.loadedErrorTrace?.states.last?.variables["x"], .int(1))
        XCTAssertFalse(viewModel.isLoadingErrorTrace)
    }

    @MainActor
    func testFindReplaceLiteralSearchPerformanceLargeDocument() {
        let manager = FindReplaceManager(debounceInterval: .zero)
        let content = (0..<10_000)
            .map { line in
                "Line \(line): token value token next token"
            }
            .joined(separator: "\n")

        manager.textProvider = { content }
        manager.searchQuery = "token"

        measure {
            for _ in 0..<50 {
                manager.findAll()
            }
        }
    }
}
