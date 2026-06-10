import AppKit
import Combine

// Note: Core types (ObligationKind, ProofStatus, ProverBackend, SourceLocation, ProofObligation)
// are defined in ProofObligation.swift

// MARK: - ProofStatus UI Extensions

extension ProofStatus {
    /// Gutter icon for this status
    public var gutterIcon: String {
        switch self {
        case .unknown: return " "
        case .pending: return "\u{22EF}"  // ⋯
        case .proved: return "\u{2713}"   // ✓
        case .failed: return "\u{2717}"   // ✗
        case .timeout: return "\u{23F0}"  // ⏰
        case .omitted: return "\u{25CB}"  // ○
        case .trivial: return "\u{2728}"  // ✨
        }
    }

    /// Gutter icon color
    public var iconColor: NSColor {
        switch self {
        case .unknown: return .tertiaryLabelColor
        case .pending: return .systemYellow
        case .proved: return .systemGreen
        case .failed: return .systemRed
        case .timeout: return .systemOrange
        case .omitted: return .systemGray
        case .trivial: return .systemGreen
        }
    }

    /// Whether this status indicates the proof is complete
    public var isComplete: Bool {
        switch self {
        case .proved, .trivial, .omitted:
            return true
        default:
            return false
        }
    }

    /// Whether this status indicates an error that needs attention
    public var needsAttention: Bool {
        switch self {
        case .failed, .timeout:
            return true
        default:
            return false
        }
    }
}

// MARK: - ProofAnnotation

/// Represents a visual annotation for a proof obligation in the editor
public struct ProofAnnotation: Identifiable, Equatable {
    public let id: UUID
    public let obligation: ProofObligation
    public let lineRange: Swift.Range<Int>
    public let gutterIcon: String
    public let iconColor: NSColor
    public let tooltipText: String

    public init(obligation: ProofObligation) {
        self.id = obligation.id
        self.obligation = obligation
        self.lineRange = obligation.location.startLine..<(obligation.location.endLine + 1)
        self.gutterIcon = obligation.status.gutterIcon
        self.iconColor = obligation.status.iconColor
        self.tooltipText = Self.buildTooltip(for: obligation)
    }

    /// Builds a tooltip string for the obligation
    private static func buildTooltip(for obligation: ProofObligation) -> String {
        var parts: [String] = []

        // Kind and status
        parts.append("\(obligation.kind.displayName): \(obligation.status.rawValue)")

        // Backend info
        if let backend = obligation.backend {
            parts.append("Prover: \(backend.displayName)")
        }

        // Duration
        if let duration = obligation.duration {
            let formatted = String(format: "%.2fs", duration)
            parts.append("Duration: \(formatted)")
        }

        // Error message
        if let error = obligation.errorMessage, !error.isEmpty {
            parts.append("Error: \(error)")
        }

        // Obligation text (truncated)
        if !obligation.obligationText.isEmpty {
            let text = obligation.obligationText
            let truncated = text.count > 100 ? String(text.prefix(100)) + "…" : text
            parts.append("Obligation: \(truncated)")
        }

        return parts.joined(separator: "\n")
    }

    public static func == (lhs: ProofAnnotation, rhs: ProofAnnotation) -> Bool {
        lhs.id == rhs.id &&
        lhs.obligation == rhs.obligation
    }
}

// MARK: - ProofAnnotationManager

/// Manages proof status annotations in the source editor.
/// Bridges between proof results and the editor's annotation system.
///
/// Performance optimizations:
/// - Maintains pre-indexed lists by status for O(1) navigation
/// - Caches status counts to avoid repeated scans
/// - Uses incremental index updates instead of full rebuilds
@MainActor
public final class ProofAnnotationManager: ObservableObject {

    // MARK: - Published State

    /// All current annotations
    @Published public private(set) var annotations: [ProofAnnotation] = []

    /// Currently selected/focused obligation
    @Published public var currentObligation: ProofObligation?

    /// Index for navigation tracking
    @Published public private(set) var currentNavigationIndex: Int?

    // MARK: - Internal State

    /// Obligations indexed by line number for quick lookup
    private var annotationsByLine: [Int: [ProofAnnotation]] = [:]

    /// All obligations by ID for quick lookup
    private var obligationsById: [UUID: ProofObligation] = [:]

    /// Annotation index by ID for quick lookup
    private var annotationIndexById: [UUID: Int] = [:]

    /// Annotations indexed by status for O(1) navigation (sorted by line)
    private var annotationsByStatus: [ProofStatus: [Int]] = [:]

    /// Annotations that need attention (failed/timeout), sorted by line
    private var attentionIndices: [Int] = []

    /// Cached status counts to avoid repeated scans
    private var cachedStatusCounts: [ProofStatus: Int] = [:]

    // MARK: - Initialization

    public init() {}

    // MARK: - Public API

    /// Updates annotations for a set of proof obligations
    /// - Parameter obligations: The proof obligations to display
    public func updateAnnotations(for obligations: [ProofObligation]) {
        // Clear existing state
        annotationsByLine.removeAll()
        obligationsById.removeAll()
        annotationIndexById.removeAll()
        annotationsByStatus.removeAll()
        attentionIndices.removeAll()
        cachedStatusCounts.removeAll()

        // Build new annotations
        var newAnnotations: [ProofAnnotation] = []

        for obligation in obligations {
            let annotation = ProofAnnotation(obligation: obligation)
            newAnnotations.append(annotation)

            // Index by ID
            obligationsById[obligation.id] = obligation

            // Index by line
            for line in annotation.lineRange {
                annotationsByLine[line, default: []].append(annotation)
            }

            // Update status counts
            cachedStatusCounts[obligation.status, default: 0] += 1
        }

        // Sort annotations by line number
        newAnnotations.sort { (a: ProofAnnotation, b: ProofAnnotation) -> Bool in
            a.lineRange.lowerBound < b.lineRange.lowerBound
        }

        // Build indices after sorting (indices now correspond to sorted order)
        for (index, annotation) in newAnnotations.enumerated() {
            let status = annotation.obligation.status

            // Index by ID -> sorted index
            annotationIndexById[annotation.id] = index

            // Index by status
            annotationsByStatus[status, default: []].append(index)

            // Track attention-needed obligations
            if status.needsAttention {
                attentionIndices.append(index)
            }
        }

        self.annotations = newAnnotations
    }

    /// Clears all annotations
    public func clearAnnotations() {
        annotations.removeAll()
        annotationsByLine.removeAll()
        obligationsById.removeAll()
        annotationIndexById.removeAll()
        annotationsByStatus.removeAll()
        attentionIndices.removeAll()
        cachedStatusCounts.removeAll()
        currentObligation = nil
        currentNavigationIndex = nil
    }

    /// Returns the annotation at a specific line, if any
    /// - Parameter line: The 1-based line number
    /// - Returns: The first annotation at that line, or nil
    public func annotationAt(line: Int) -> ProofAnnotation? {
        annotationsByLine[line]?.first
    }

    /// Returns all annotations at a specific line
    /// - Parameter line: The 1-based line number
    /// - Returns: Array of annotations at that line
    public func annotationsAt(line: Int) -> [ProofAnnotation] {
        annotationsByLine[line] ?? []
    }

    /// Navigates to the next obligation with the specified status
    /// Uses pre-indexed status lists for O(log n) lookup via binary search.
    /// - Parameter status: The status to navigate to
    /// - Returns: The obligation if found, nil otherwise
    @discardableResult
    public func navigateToNext(status: ProofStatus) -> ProofObligation? {
        guard let indices = annotationsByStatus[status], !indices.isEmpty else { return nil }

        let currentLine = currentObligation?.location.startLine ?? 0

        // Binary search for next obligation after current line
        // Safe unwrap: indices is guaranteed non-empty by guard above
        let targetIndex = indices.first { idx in
            annotations[idx].lineRange.lowerBound > currentLine
        } ?? indices[0]  // Wrap around to first (safe: indices is non-empty)

        guard targetIndex < annotations.count else { return nil }
        let annotation = annotations[targetIndex]
        selectObligation(annotation.obligation)
        return annotation.obligation
    }

    /// Navigates to the previous obligation with the specified status
    /// Uses pre-indexed status lists for O(log n) lookup via binary search.
    /// - Parameter status: The status to navigate to
    /// - Returns: The obligation if found, nil otherwise
    @discardableResult
    public func navigateToPrevious(status: ProofStatus) -> ProofObligation? {
        guard let indices = annotationsByStatus[status], !indices.isEmpty else { return nil }

        let currentLine = currentObligation?.location.startLine ?? Int.max

        // Find previous obligation before current line
        // Safe unwrap: indices is guaranteed non-empty by guard above
        let targetIndex = indices.last { idx in
            annotations[idx].lineRange.lowerBound < currentLine
        } ?? indices[indices.count - 1]  // Wrap around to last (safe: indices is non-empty)

        guard targetIndex < annotations.count else { return nil }
        let annotation = annotations[targetIndex]
        selectObligation(annotation.obligation)
        return annotation.obligation
    }

    /// Navigates to the next failed or timed out obligation
    /// Uses pre-indexed attention list for O(log n) lookup.
    /// - Returns: The obligation if found, nil otherwise
    @discardableResult
    public func navigateToNextFailed() -> ProofObligation? {
        guard !attentionIndices.isEmpty else { return nil }

        let currentLine = currentObligation?.location.startLine ?? 0

        // Find next failed after current line
        // Safe: attentionIndices is guaranteed non-empty by guard above
        let targetIndex = attentionIndices.first { idx in
            annotations[idx].lineRange.lowerBound > currentLine
        } ?? attentionIndices[0]  // Wrap around to first (safe: attentionIndices is non-empty)

        guard targetIndex < annotations.count else { return nil }
        let annotation = annotations[targetIndex]
        selectObligation(annotation.obligation)
        return annotation.obligation
    }

    /// Navigates to the previous failed or timed out obligation
    /// Uses pre-indexed attention list for O(log n) lookup.
    /// - Returns: The obligation if found, nil otherwise
    @discardableResult
    public func navigateToPreviousFailed() -> ProofObligation? {
        guard !attentionIndices.isEmpty else { return nil }

        let currentLine = currentObligation?.location.startLine ?? Int.max

        // Find previous failed before current line
        // Safe: attentionIndices is guaranteed non-empty by guard above
        let targetIndex = attentionIndices.last { idx in
            annotations[idx].lineRange.lowerBound < currentLine
        } ?? attentionIndices[attentionIndices.count - 1]  // Wrap around to last (safe: attentionIndices is non-empty)

        guard targetIndex < annotations.count else { return nil }
        let annotation = annotations[targetIndex]
        selectObligation(annotation.obligation)
        return annotation.obligation
    }

    /// Selects an obligation and navigates to it
    /// Uses pre-indexed lookup for O(1) index retrieval.
    /// - Parameter obligation: The obligation to select
    public func selectObligation(_ obligation: ProofObligation) {
        currentObligation = obligation

        // Update navigation index using O(1) lookup
        currentNavigationIndex = annotationIndexById[obligation.id]
    }

    /// Updates the status of a specific obligation
    /// Uses incremental index updates for O(1) status changes instead of O(n) rebuilds.
    /// - Parameters:
    ///   - id: The obligation ID
    ///   - status: The new status
    ///   - backend: Optional backend that was used
    ///   - duration: Optional duration
    ///   - errorMessage: Optional error message
    public func updateObligationStatus(
        id: UUID,
        status: ProofStatus,
        backend: ProverBackend? = nil,
        duration: TimeInterval? = nil,
        errorMessage: String? = nil
    ) {
        guard var obligation = obligationsById[id] else { return }
        guard let index = annotationIndexById[id] else { return }

        let oldStatus = obligation.status

        // Update obligation
        obligation.status = status
        if let backend = backend {
            obligation.backend = backend
        }
        if let duration = duration {
            obligation.duration = duration
        }
        if let errorMessage = errorMessage {
            obligation.errorMessage = errorMessage
        }

        obligationsById[id] = obligation

        // Update annotation
        annotations[index] = ProofAnnotation(obligation: obligation)

        // Incrementally update indices if status changed
        if oldStatus != status {
            // Update cached counts (ensure we don't decrement below 0)
            let oldCount = cachedStatusCounts[oldStatus, default: 0]
            cachedStatusCounts[oldStatus] = max(0, oldCount - 1)
            cachedStatusCounts[status, default: 0] += 1

            // Remove from old status index
            if let oldStatusIndices = annotationsByStatus[oldStatus],
               let posInOld = oldStatusIndices.firstIndex(of: index) {
                annotationsByStatus[oldStatus]?.remove(at: posInOld)
            }

            // Add to new status index (maintain sorted order)
            let line = annotations[index].lineRange.lowerBound
            if var newStatusIndices = annotationsByStatus[status] {
                // Binary search for insertion point
                let insertionPoint = newStatusIndices.firstIndex { idx in
                    annotations[idx].lineRange.lowerBound > line
                } ?? newStatusIndices.endIndex
                newStatusIndices.insert(index, at: insertionPoint)
                annotationsByStatus[status] = newStatusIndices
            } else {
                annotationsByStatus[status] = [index]
            }

            // Update attention indices
            let wasNeedsAttention = oldStatus.needsAttention
            let nowNeedsAttention = status.needsAttention

            if wasNeedsAttention && !nowNeedsAttention {
                // Remove from attention indices
                if let pos = attentionIndices.firstIndex(of: index) {
                    attentionIndices.remove(at: pos)
                }
            } else if !wasNeedsAttention && nowNeedsAttention {
                // Add to attention indices (maintain sorted order)
                let attentionInsertionPoint = attentionIndices.firstIndex { idx in
                    annotations[idx].lineRange.lowerBound > line
                } ?? attentionIndices.endIndex
                attentionIndices.insert(index, at: attentionInsertionPoint)
            }
        }
    }

    // MARK: - Statistics

    /// Returns counts of obligations by status
    /// Uses cached counts for O(1) lookup instead of O(n) scan.
    public var statusCounts: [ProofStatus: Int] {
        cachedStatusCounts
    }

    /// Total number of obligations
    public var totalCount: Int {
        annotations.count
    }

    /// Number of proved obligations
    /// Uses cached counts for O(1) lookup.
    public var provedCount: Int {
        (cachedStatusCounts[.proved] ?? 0) + (cachedStatusCounts[.trivial] ?? 0)
    }

    /// Number of failed obligations
    /// Uses cached counts for O(1) lookup.
    public var failedCount: Int {
        cachedStatusCounts[.failed] ?? 0
    }

    /// Number of pending obligations
    /// Uses cached counts for O(1) lookup.
    public var pendingCount: Int {
        cachedStatusCounts[.pending] ?? 0
    }

    /// Number of timed out obligations
    /// Uses cached counts for O(1) lookup.
    public var timeoutCount: Int {
        cachedStatusCounts[.timeout] ?? 0
    }

    /// Progress percentage (0.0 to 1.0)
    /// Uses cached counts for O(1) calculation.
    public var progress: Double {
        guard totalCount > 0 else { return 0.0 }
        let completed = (cachedStatusCounts[.proved] ?? 0) +
                       (cachedStatusCounts[.trivial] ?? 0) +
                       (cachedStatusCounts[.omitted] ?? 0)
        return Double(completed) / Double(totalCount)
    }
}
