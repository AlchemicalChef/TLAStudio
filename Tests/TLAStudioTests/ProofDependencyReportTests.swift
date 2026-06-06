import XCTest
@testable import TLAStudioApp

/// Unit tests for the pure decision logic of `ProofDependencyReport` — the part that
/// drives whether/when the proof-setup prompt appears. The filesystem-dependent
/// `ProofDependencyChecker.current()` is exercised by the live app, not here.
final class ProofDependencyReportTests: XCTestCase {

    private func tool(
        _ id: String,
        role: ProofToolRole,
        kind: ProofToolKind,
        available: Bool
    ) -> ProofToolStatus {
        ProofToolStatus(id: id, name: id, detail: "", role: role, kind: kind, isAvailable: available)
    }

    func testFullyReadyDoesNotPrompt() {
        let report = ProofDependencyReport(tools: [
            tool("tlapm", role: .core, kind: .bundled, available: true),
            tool("z3", role: .core, kind: .bundled, available: true),
            tool("zenon", role: .core, kind: .bundled, available: true),
            tool("isabelle", role: .optional, kind: .downloadable, available: true),
            tool("spass", role: .optional, kind: .manual, available: false)
        ])

        // SPASS is manual-only and missing, but it's never an actionable gap.
        XCTAssertTrue(report.allCoreReady)
        XCTAssertTrue(report.missingDownloadable.isEmpty)
        XCTAssertFalse(report.shouldPrompt)
    }

    func testMissingIsabellePrompts() {
        let report = ProofDependencyReport(tools: [
            tool("tlapm", role: .core, kind: .bundled, available: true),
            tool("z3", role: .core, kind: .bundled, available: true),
            tool("zenon", role: .core, kind: .bundled, available: true),
            tool("isabelle", role: .optional, kind: .downloadable, available: false)
        ])

        XCTAssertTrue(report.allCoreReady)
        XCTAssertEqual(report.missingDownloadable.map(\.id), ["isabelle"])
        XCTAssertTrue(report.shouldPrompt)
    }

    func testBrokenCorePromptsEvenWithoutDownloadableGap() {
        let report = ProofDependencyReport(tools: [
            tool("tlapm", role: .core, kind: .bundled, available: true),
            tool("z3", role: .core, kind: .bundled, available: false), // broken core
            tool("isabelle", role: .optional, kind: .downloadable, available: true)
        ])

        XCTAssertFalse(report.allCoreReady)
        XCTAssertTrue(report.missingDownloadable.isEmpty)
        XCTAssertTrue(report.shouldPrompt, "A missing core backend must surface even when nothing is auto-installable")
    }

    func testMissingManualToolAloneDoesNotPrompt() {
        let report = ProofDependencyReport(tools: [
            tool("tlapm", role: .core, kind: .bundled, available: true),
            tool("z3", role: .core, kind: .bundled, available: true),
            tool("zenon", role: .core, kind: .bundled, available: true),
            tool("spass", role: .optional, kind: .manual, available: false)
        ])

        XCTAssertFalse(report.shouldPrompt, "A missing manual-only optional tool is not actionable")
    }

    func testReadyCounts() {
        let report = ProofDependencyReport(tools: [
            tool("a", role: .core, kind: .bundled, available: true),
            tool("b", role: .core, kind: .bundled, available: false),
            tool("c", role: .optional, kind: .bundled, available: true)
        ])
        XCTAssertEqual(report.readyCount, 2)
        XCTAssertEqual(report.totalCount, 3)
    }
}
