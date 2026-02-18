import XCTest
@testable import TLAStudioApp

@MainActor
final class ProofAnnotationManagerTests: XCTestCase {

    // MARK: - Update/Clear Annotations

    func testUpdateAnnotations() {
        let manager = ProofAnnotationManager()
        let obligations = [
            TestFactories.makeProofObligation(startLine: 5, status: .proved),
            TestFactories.makeProofObligation(startLine: 10, status: .failed),
            TestFactories.makeProofObligation(startLine: 15, status: .pending),
        ]

        manager.updateAnnotations(for: obligations)

        XCTAssertEqual(manager.annotations.count, 3)
        XCTAssertEqual(manager.totalCount, 3)
    }

    func testClearAnnotations() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 5, status: .proved)
        ])

        XCTAssertEqual(manager.totalCount, 1)

        manager.clearAnnotations()
        XCTAssertEqual(manager.totalCount, 0)
        XCTAssertNil(manager.currentObligation)
        XCTAssertNil(manager.currentNavigationIndex)
    }

    // MARK: - Sorted Order

    func testAnnotationsAreSortedByLine() {
        let manager = ProofAnnotationManager()
        let obligations = [
            TestFactories.makeProofObligation(startLine: 20),
            TestFactories.makeProofObligation(startLine: 5),
            TestFactories.makeProofObligation(startLine: 15),
            TestFactories.makeProofObligation(startLine: 1),
        ]

        manager.updateAnnotations(for: obligations)

        let lines = manager.annotations.map { $0.lineRange.lowerBound }
        XCTAssertEqual(lines, [1, 5, 15, 20])
    }

    // MARK: - Line-Range Indexing

    func testAnnotationAtLine() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 10, endLine: 12, status: .proved)
        ])

        XCTAssertNotNil(manager.annotationAt(line: 10))
        XCTAssertNotNil(manager.annotationAt(line: 11))
        XCTAssertNotNil(manager.annotationAt(line: 12))
        XCTAssertNil(manager.annotationAt(line: 13))
        XCTAssertNil(manager.annotationAt(line: 9))
    }

    func testAnnotationsAtLine() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 5, endLine: 7),
            TestFactories.makeProofObligation(startLine: 6, endLine: 8),
        ])

        // Line 6 should have both annotations (overlapping ranges)
        XCTAssertEqual(manager.annotationsAt(line: 6).count, 2)
        XCTAssertEqual(manager.annotationsAt(line: 5).count, 1)
        XCTAssertEqual(manager.annotationsAt(line: 8).count, 1)
    }

    // MARK: - Status Counts

    func testStatusCounts() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 1, status: .proved),
            TestFactories.makeProofObligation(startLine: 2, status: .proved),
            TestFactories.makeProofObligation(startLine: 3, status: .failed),
            TestFactories.makeProofObligation(startLine: 4, status: .pending),
            TestFactories.makeProofObligation(startLine: 5, status: .trivial),
        ])

        XCTAssertEqual(manager.provedCount, 3)  // proved + trivial
        XCTAssertEqual(manager.failedCount, 1)
        XCTAssertEqual(manager.pendingCount, 1)
    }

    func testTimeoutCount() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 1, status: .timeout),
            TestFactories.makeProofObligation(startLine: 2, status: .timeout),
        ])

        XCTAssertEqual(manager.timeoutCount, 2)
    }

    // MARK: - Progress Calculation

    func testProgressAllProved() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 1, status: .proved),
            TestFactories.makeProofObligation(startLine: 2, status: .trivial),
        ])

        XCTAssertEqual(manager.progress, 1.0, accuracy: 0.01)
    }

    func testProgressPartial() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 1, status: .proved),
            TestFactories.makeProofObligation(startLine: 2, status: .pending),
            TestFactories.makeProofObligation(startLine: 3, status: .failed),
            TestFactories.makeProofObligation(startLine: 4, status: .trivial),
        ])

        // proved(1) + trivial(1) + omitted(0) = 2 out of 4 = 0.5
        XCTAssertEqual(manager.progress, 0.5, accuracy: 0.01)
    }

    func testProgressEmpty() {
        let manager = ProofAnnotationManager()
        XCTAssertEqual(manager.progress, 0.0)
    }

    // MARK: - Navigation: Next by Status

    func testNavigateToNextFailed() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 5, status: .proved),
            TestFactories.makeProofObligation(startLine: 10, status: .failed),
            TestFactories.makeProofObligation(startLine: 15, status: .proved),
            TestFactories.makeProofObligation(startLine: 20, status: .failed),
        ])

        // No current — should find the first failed (line 10)
        let first = manager.navigateToNextFailed()
        XCTAssertEqual(first?.location.startLine, 10)

        // Now navigate to next failed (line 20)
        let second = manager.navigateToNextFailed()
        XCTAssertEqual(second?.location.startLine, 20)
    }

    func testNavigateToNextFailedWrapsAround() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 5, status: .failed),
            TestFactories.makeProofObligation(startLine: 10, status: .proved),
        ])

        let first = manager.navigateToNextFailed()
        XCTAssertEqual(first?.location.startLine, 5)

        // Already at last failed, should wrap to first
        let wrapped = manager.navigateToNextFailed()
        XCTAssertEqual(wrapped?.location.startLine, 5)
    }

    func testNavigateToNextFailedReturnsNilWhenNone() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 5, status: .proved),
        ])

        let result = manager.navigateToNextFailed()
        XCTAssertNil(result)
    }

    // MARK: - Navigation: Previous by Status

    func testNavigateToPreviousFailed() {
        let manager = ProofAnnotationManager()
        let failedId1 = UUID()
        let failedId2 = UUID()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(id: failedId1, startLine: 5, status: .failed),
            TestFactories.makeProofObligation(startLine: 10, status: .proved),
            TestFactories.makeProofObligation(id: failedId2, startLine: 20, status: .failed),
        ])

        // Navigate to last failed first
        _ = manager.navigateToNextFailed()  // Goes to line 5
        _ = manager.navigateToNextFailed()  // Goes to line 20

        // Now go back
        let prev = manager.navigateToPreviousFailed()
        XCTAssertEqual(prev?.location.startLine, 5)
    }

    func testNavigateToPreviousFailedWrapsAround() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 5, status: .proved),
            TestFactories.makeProofObligation(startLine: 10, status: .failed),
            TestFactories.makeProofObligation(startLine: 20, status: .failed),
        ])

        // No current — should wrap to last
        let result = manager.navigateToPreviousFailed()
        XCTAssertEqual(result?.location.startLine, 20)
    }

    // MARK: - Navigation: Next/Previous by Specific Status

    func testNavigateToNextByStatus() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 1, status: .proved),
            TestFactories.makeProofObligation(startLine: 5, status: .pending),
            TestFactories.makeProofObligation(startLine: 10, status: .proved),
            TestFactories.makeProofObligation(startLine: 15, status: .pending),
        ])

        let first = manager.navigateToNext(status: .pending)
        XCTAssertEqual(first?.location.startLine, 5)

        let second = manager.navigateToNext(status: .pending)
        XCTAssertEqual(second?.location.startLine, 15)
    }

    func testNavigateToPreviousByStatus() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 1, status: .proved),
            TestFactories.makeProofObligation(startLine: 5, status: .proved),
            TestFactories.makeProofObligation(startLine: 10, status: .pending),
        ])

        // No current — wrap to last proved
        let result = manager.navigateToPrevious(status: .proved)
        XCTAssertEqual(result?.location.startLine, 5)
    }

    func testNavigateReturnsNilForMissingStatus() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(startLine: 1, status: .proved),
        ])

        XCTAssertNil(manager.navigateToNext(status: .failed))
        XCTAssertNil(manager.navigateToPrevious(status: .timeout))
    }

    // MARK: - Incremental Status Update

    func testUpdateObligationStatusChangesCounts() {
        let manager = ProofAnnotationManager()
        let oblId = UUID()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(id: oblId, startLine: 5, status: .pending),
            TestFactories.makeProofObligation(startLine: 10, status: .proved),
        ])

        XCTAssertEqual(manager.pendingCount, 1)
        XCTAssertEqual(manager.provedCount, 1)

        // Update the pending obligation to proved
        manager.updateObligationStatus(id: oblId, status: .proved, duration: 0.5)

        XCTAssertEqual(manager.pendingCount, 0)
        XCTAssertEqual(manager.provedCount, 2)
    }

    func testUpdateObligationStatusUpdatesAttentionIndices() {
        let manager = ProofAnnotationManager()
        let oblId = UUID()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(id: oblId, startLine: 5, status: .failed),
        ])

        // Should be navigable as failed
        XCTAssertNotNil(manager.navigateToNextFailed())

        // Mark as proved
        manager.updateObligationStatus(id: oblId, status: .proved)

        // No longer navigable as failed
        let manager2 = ProofAnnotationManager()
        manager2.updateAnnotations(for: manager.annotations.map { $0.obligation })
        // Rebuilding from the updated obligations should show no failed
        XCTAssertEqual(manager.failedCount, 0)
    }

    // MARK: - Edge Cases

    func testSingleObligation() {
        let manager = ProofAnnotationManager()
        let oblId = UUID()
        manager.updateAnnotations(for: [
            TestFactories.makeProofObligation(id: oblId, startLine: 1, status: .proved),
        ])

        XCTAssertEqual(manager.totalCount, 1)
        XCTAssertEqual(manager.provedCount, 1)
        XCTAssertEqual(manager.progress, 1.0, accuracy: 0.01)
    }

    func testEmptyObligations() {
        let manager = ProofAnnotationManager()
        manager.updateAnnotations(for: [])

        XCTAssertEqual(manager.totalCount, 0)
        XCTAssertNil(manager.navigateToNextFailed())
        XCTAssertEqual(manager.progress, 0.0)
    }

    func testSelectObligation() {
        let manager = ProofAnnotationManager()
        let obl = TestFactories.makeProofObligation(startLine: 5, status: .proved)
        manager.updateAnnotations(for: [obl])

        manager.selectObligation(obl)

        XCTAssertEqual(manager.currentObligation?.id, obl.id)
        XCTAssertNotNil(manager.currentNavigationIndex)
    }
}
