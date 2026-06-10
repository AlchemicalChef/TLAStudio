import XCTest
@testable import TLAStudioApp

final class CrossModuleFeatureTests: XCTestCase {

    private func moduleSymbol(
        _ name: String,
        kind: TLASymbolKind = .operator,
        parameters: [String] = [],
        module: String = "Helper",
        depth: Int = 1
    ) -> ModuleSymbol {
        let range = TLARange(
            start: TLAPosition(line: 2, column: 0),
            end: TLAPosition(line: 2, column: UInt32(name.count))
        )
        return ModuleSymbol(
            symbol: TLASymbol(
                name: name, kind: kind, range: range,
                selectionRange: range, children: [], parameters: parameters
            ),
            moduleName: module,
            fileURL: URL(fileURLWithPath: "/tmp/\(module).tla"),
            depth: depth
        )
    }

    private func baseItem(_ label: String, priority: UInt32 = 15) -> TLADetailedCompletionItem {
        TLADetailedCompletionItem(
            label: label, kind: .function, detail: nil, documentation: nil,
            insertText: nil, filterText: nil, sortPriority: priority, signature: nil
        )
    }

    // MARK: - Merger

    func testModuleNameContextsAreNotPolluted() {
        let base = [baseItem("Naturals")]
        let merged = CrossModuleCompletionMerger.merge(
            base: base,
            crossModule: [moduleSymbol("HelperOp")],
            context: .afterExtends
        )
        XCTAssertEqual(merged.map(\.label), ["Naturals"])
        XCTAssertFalse(CrossModuleCompletionMerger.shouldMerge(into: .afterInstance))
        XCTAssertFalse(CrossModuleCompletionMerger.shouldMerge(into: .afterWith))
        XCTAssertTrue(CrossModuleCompletionMerger.shouldMerge(into: .inExpression))
    }

    func testMergeAddsCrossModuleItemsWithDetailAndSignature() throws {
        let merged = CrossModuleCompletionMerger.merge(
            base: [baseItem("LocalOp")],
            crossModule: [moduleSymbol("HelperOp", parameters: ["a", "b"])],
            context: .inExpression
        )
        let item = try XCTUnwrap(merged.first { $0.label == "HelperOp" })
        XCTAssertEqual(item.detail, "from Helper")
        XCTAssertEqual(item.signature, "HelperOp(a, b)")
        XCTAssertEqual(item.kind, .function)
        XCTAssertEqual(item.sortPriority, 16)
    }

    func testLocalSymbolShadowsCrossModule() {
        let merged = CrossModuleCompletionMerger.merge(
            base: [baseItem("Shared")],
            crossModule: [moduleSymbol("Shared")],
            context: .inExpression
        )
        XCTAssertEqual(merged.filter { $0.label == "Shared" }.count, 1)
        XCTAssertNil(merged.first { $0.label == "Shared" }?.detail)
    }

    func testLocalPriorityOutranksCrossModule() throws {
        let merged = CrossModuleCompletionMerger.merge(
            base: [baseItem("ZLocal", priority: 15)],
            crossModule: [moduleSymbol("AHelper")],
            context: .inExpression
        )
        let localIndex = try XCTUnwrap(merged.firstIndex { $0.label == "ZLocal" })
        let helperIndex = try XCTUnwrap(merged.firstIndex { $0.label == "AHelper" })
        XCTAssertLessThan(localIndex, helperIndex)
    }

    func testMergeCapHolds() {
        let crossModule = (0..<50).map { moduleSymbol("Op\($0)") }
        let merged = CrossModuleCompletionMerger.merge(
            base: [], crossModule: crossModule, context: .inExpression, maxItems: 10
        )
        XCTAssertEqual(merged.count, 10)
    }

    // MARK: - Call Context Scanner

    private func call(_ line: String, column: Int) -> CallContextScanner.Call? {
        CallContextScanner.enclosingCall(
            in: line,
            at: TLAPosition(line: 0, column: UInt32(column))
        )
    }

    func testScannerFindsSimpleCall() {
        let result = call("x == HelperOp(1, 2", column: 18)
        XCTAssertEqual(result, .init(operatorName: "HelperOp", activeParameter: 1))
    }

    func testScannerSkipsNestedParens() {
        let result = call("Op(Inner(a, b), c", column: 17)
        XCTAssertEqual(result, .init(operatorName: "Op", activeParameter: 1))
    }

    func testScannerIgnoresCommasInsideBrackets() {
        let result = call("Op([a |-> 1, b |-> 2], x", column: 24)
        XCTAssertEqual(result, .init(operatorName: "Op", activeParameter: 1))
    }

    func testScannerReturnsNilOutsideCall() {
        XCTAssertNil(call("x == 1 + 2", column: 9))
        XCTAssertNil(call("(a + b", column: 6), "paren without preceding identifier is not a call")
    }

    func testScannerHandlesMultiByteCharacters() {
        // Emoji in a comment-ish prefix must not break Character math.
        let result = call("\\* 😀 note\nOp(a", column: 5)
        XCTAssertNil(result)   // row 0, column 5 is inside the comment line — no call
        let second = CallContextScanner.enclosingCall(
            in: "\\* 😀 note\nOp(a",
            at: TLAPosition(line: 1, column: 4)
        )
        XCTAssertEqual(second, .init(operatorName: "Op", activeParameter: 0))
    }

    // MARK: - Hover

    @MainActor
    func testHoverPrefersLocalSymbolOverCrossModule() throws {
        let source = "---- MODULE M ----\nShared == 1\nUse == Shared\n===="
        let local = TLASymbol(
            name: "Shared", kind: .operator,
            range: TLARange(start: TLAPosition(line: 1, column: 0), end: TLAPosition(line: 1, column: 6)),
            selectionRange: nil, children: [], parameters: []
        )
        let info = try XCTUnwrap(TLACoreWrapper.shared.getHoverDocumentation(
            at: TLAPosition(line: 2, column: 8),
            in: source,
            symbols: [local],
            crossModuleSymbols: [moduleSymbol("Shared")]
        ))
        XCTAssertNil(info.sourceModule, "local definition must win over cross-module")
    }

    @MainActor
    func testHoverFallsBackToCrossModuleSymbol() throws {
        let source = "---- MODULE M ----\nUse == HelperOp(1, 2)\n===="
        let info = try XCTUnwrap(TLACoreWrapper.shared.getHoverDocumentation(
            at: TLAPosition(line: 1, column: 8),
            in: source,
            symbols: [],
            crossModuleSymbols: [moduleSymbol("HelperOp", parameters: ["a", "b"])]
        ))
        XCTAssertEqual(info.sourceModule, "Helper")
        XCTAssertEqual(info.signature, "HelperOp(a, b)")
    }

    // MARK: - Signature Help Fallback

    @MainActor
    func testSignatureHelpFallsBackToCrossModuleOperator() async throws {
        let source = "---- MODULE M ----\nUse == HelperOp(1, \n===="
        let help = await CrossModuleIntelliSense.signatureHelp(
            text: source,
            utf16Position: (source as NSString).range(of: "(1, ").upperBound,
            crossModuleSymbols: [moduleSymbol("HelperOp", parameters: ["a", "b"])]
        )
        let resolved = try XCTUnwrap(help)
        XCTAssertEqual(resolved.signatures.first?.label, "HelperOp(a, b)")
        XCTAssertEqual(resolved.activeParameter, 1)
        XCTAssertEqual(resolved.signatures.first?.documentation, "Operator defined in Helper")
    }
}
