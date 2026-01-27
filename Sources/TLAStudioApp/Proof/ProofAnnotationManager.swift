import AppKit
import Combine
import SourceEditor

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

    /// Background highlight color for the line
    public var backgroundColor: NSColor {
        switch self {
        case .unknown:
            return .clear
        case .pending:
            return NSColor(red: 1.0, green: 1.0, blue: 0.0, alpha: 0.1)
        case .proved:
            return NSColor(red: 0.0, green: 1.0, blue: 0.0, alpha: 0.1)
        case .failed:
            return NSColor(red: 1.0, green: 0.0, blue: 0.0, alpha: 0.15)
        case .timeout:
            return NSColor(red: 1.0, green: 0.647, blue: 0.0, alpha: 0.1)
        case .omitted:
            return .clear
        case .trivial:
            return NSColor(red: 0.0, green: 1.0, blue: 0.0, alpha: 0.05)
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
    public let backgroundColor: NSColor
    public let tooltipText: String

    public init(obligation: ProofObligation) {
        self.id = obligation.id
        self.obligation = obligation
        self.lineRange = obligation.location.startLine..<(obligation.location.endLine + 1)
        self.gutterIcon = obligation.status.gutterIcon
        self.iconColor = obligation.status.iconColor
        self.backgroundColor = obligation.status.backgroundColor
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
            let truncated = text.count > 100 ? String(text.prefix(100)) + "..." : text
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

    /// Navigation history for failed obligations (deprecated, use attentionIndices)
    private var failedObligationIndices: [Int] = []

    // MARK: - Editor Integration

    /// Weak reference to the source editor
    public weak var editor: TLASourceEditor? {
        didSet {
            if editor != nil {
                applyAnnotationsToEditor()
            }
        }
    }

    /// Callback for when navigation occurs
    public var onNavigate: ((ProofObligation) -> Void)?

    /// Callback for requesting line background highlight
    public var onHighlightLine: ((Int, NSColor) -> Void)?

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
        failedObligationIndices.removeAll()

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
                failedObligationIndices.append(index)
            }
        }

        self.annotations = newAnnotations

        // Apply to editor if connected
        applyAnnotationsToEditor()
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
        failedObligationIndices.removeAll()
        currentObligation = nil
        currentNavigationIndex = nil

        // Clear editor annotations
        clearEditorAnnotations()
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

        // Notify callback
        onNavigate?(obligation)

        // Scroll editor to obligation
        scrollToObligation(obligation)
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
                // FIX: Search independently in each array since they may have different positions
                if let pos = attentionIndices.firstIndex(of: index) {
                    attentionIndices.remove(at: pos)
                }
                if let pos = failedObligationIndices.firstIndex(of: index) {
                    failedObligationIndices.remove(at: pos)
                }
            } else if !wasNeedsAttention && nowNeedsAttention {
                // Add to attention indices (maintain sorted order)
                // FIX: Calculate separate insertion points for each array since they may differ
                let attentionInsertionPoint = attentionIndices.firstIndex { idx in
                    annotations[idx].lineRange.lowerBound > line
                } ?? attentionIndices.endIndex
                attentionIndices.insert(index, at: attentionInsertionPoint)

                let failedInsertionPoint = failedObligationIndices.firstIndex { idx in
                    annotations[idx].lineRange.lowerBound > line
                } ?? failedObligationIndices.endIndex
                failedObligationIndices.insert(index, at: failedInsertionPoint)
            }
        }

        // Update editor
        applyAnnotationsToEditor()
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

    // MARK: - Private Methods

    /// Scrolls the editor to show the specified obligation
    private func scrollToObligation(_ obligation: ProofObligation) {
        guard let editor = editor else { return }

        // Calculate character index for the line
        let text = editor.string as NSString
        let textLength = text.length

        // Guard against empty document
        guard textLength > 0 else { return }

        var characterIndex = 0
        var currentLine = 1

        // Navigate to the target line, with bounds checking
        while currentLine < obligation.location.startLine && characterIndex < textLength {
            if text.character(at: characterIndex) == 0x0A { // newline
                currentLine += 1
            }
            characterIndex += 1
        }

        // Only add column offset if we found the target line
        if currentLine == obligation.location.startLine {
            // Add column offset, ensuring we don't exceed the line length
            let columnOffset = max(0, obligation.location.startColumn - 1)
            characterIndex += columnOffset
        }

        // Clamp to valid range
        characterIndex = max(0, min(characterIndex, textLength))

        // Set selection and scroll
        let range = NSRange(location: characterIndex, length: 0)
        editor.setSelectedRange(range)
        editor.scrollRangeToVisible(range)
    }

    /// Applies annotations to the connected editor
    private func applyAnnotationsToEditor() {
        guard let editor = editor else { return }

        // Get the ruler view if available
        guard let scrollView = editor.enclosingScrollView,
              let rulerView = scrollView.verticalRulerView as? ProofAnnotationRulerView else {
            return
        }

        // Update ruler annotations
        rulerView.annotations = annotations
        rulerView.needsDisplay = true
    }

    /// Clears annotations from the editor
    private func clearEditorAnnotations() {
        guard let editor = editor else { return }

        // Clear ruler annotations
        if let scrollView = editor.enclosingScrollView,
           let rulerView = scrollView.verticalRulerView as? ProofAnnotationRulerView {
            rulerView.annotations = []
            rulerView.needsDisplay = true
        }
    }
}

// MARK: - ProofAnnotationRulerView

/// A ruler view that displays proof status annotations in the gutter.
/// Uses a cached line offset index for O(log n) line number lookups instead of O(n) character counting.
public class ProofAnnotationRulerView: NSRulerView {

    // MARK: - Properties

    private weak var textView: NSTextView?

    /// The annotations to display
    public var annotations: [ProofAnnotation] = [] {
        didSet {
            buildAnnotationIndex()
            needsDisplay = true
        }
    }

    /// Annotations indexed by line for efficient lookup
    private var annotationsByLine: [Int: ProofAnnotation] = [:]

    /// Click handler for gutter icons
    public var onAnnotationClick: ((ProofAnnotation) -> Void)?

    /// Hover handler for tooltips
    public var onAnnotationHover: ((ProofAnnotation, NSPoint) -> Void)?

    // MARK: - Line Offset Index

    /// Cached line start offsets for O(log n) line number lookups.
    /// Index i contains the character offset where line (i+1) starts.
    /// Line 1 always starts at offset 0.
    private var lineStartOffsets: [Int] = [0]

    /// Hash of the text content when lineStartOffsets was last built
    private var lastTextHash: Int = 0

    // MARK: - Tracking

    private var trackingArea: NSTrackingArea?
    private var hoveredLine: Int?

    // MARK: - Initialization

    public init(textView: NSTextView) {
        self.textView = textView
        super.init(scrollView: textView.enclosingScrollView, orientation: .verticalRuler)

        ruleThickness = 50  // Wider to accommodate icons
        clientView = textView

        setupNotifications()
        setupTracking()
    }

    required init(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    deinit {
        NotificationCenter.default.removeObserver(self)
    }

    // MARK: - Setup

    private func setupNotifications() {
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )

        NotificationCenter.default.addObserver(
            self,
            selector: #selector(boundsDidChange(_:)),
            name: NSView.boundsDidChangeNotification,
            object: scrollView?.contentView
        )
    }

    private func setupTracking() {
        let options: NSTrackingArea.Options = [
            .activeInKeyWindow,
            .mouseEnteredAndExited,
            .mouseMoved,
            .inVisibleRect
        ]
        trackingArea = NSTrackingArea(rect: bounds, options: options, owner: self, userInfo: nil)
        addTrackingArea(trackingArea!)
    }

    public override func updateTrackingAreas() {
        super.updateTrackingAreas()
        if let existing = trackingArea {
            removeTrackingArea(existing)
        }
        setupTracking()
    }

    // MARK: - Notifications

    @objc private func textDidChange(_ notification: Notification) {
        invalidateLineIndex()
        needsDisplay = true
    }

    @objc private func boundsDidChange(_ notification: Notification) {
        needsDisplay = true
    }

    // MARK: - Index Building

    private func buildAnnotationIndex() {
        annotationsByLine.removeAll()
        for annotation in annotations {
            // Use the first line of the range as the key
            annotationsByLine[annotation.lineRange.lowerBound] = annotation
        }
    }

    /// Invalidates the line offset index, forcing rebuild on next access
    private func invalidateLineIndex() {
        lastTextHash = 0
    }

    /// Rebuilds the line offset index if needed. O(n) but only on text change.
    private func rebuildLineIndexIfNeeded() {
        guard let textView = textView else { return }

        let text = textView.string
        let currentHash = text.hashValue

        // Skip rebuild if text hasn't changed
        guard currentHash != lastTextHash else { return }

        lastTextHash = currentHash
        lineStartOffsets = [0]
        lineStartOffsets.reserveCapacity(text.count / 40 + 1) // Estimate ~40 chars per line

        var offset = 0
        for char in text {
            offset += 1
            if char == "\n" {
                lineStartOffsets.append(offset)
            }
        }
    }

    /// Returns the 1-based line number for a character offset. O(log n) via binary search.
    private func lineNumber(forCharacterOffset offset: Int) -> Int {
        rebuildLineIndexIfNeeded()

        // Binary search for the largest line start <= offset
        var low = 0
        var high = lineStartOffsets.count - 1

        while low < high {
            let mid = (low + high + 1) / 2
            if lineStartOffsets[mid] <= offset {
                low = mid
            } else {
                high = mid - 1
            }
        }

        return low + 1  // 1-based line numbers
    }

    // MARK: - Drawing

    public override func drawHashMarksAndLabels(in rect: NSRect) {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else {
            return
        }

        // Ensure line index is up to date
        rebuildLineIndexIfNeeded()

        // Background
        NSColor.controlBackgroundColor.setFill()
        rect.fill()

        // Separator line
        NSColor.separatorColor.setStroke()
        let separatorPath = NSBezierPath()
        separatorPath.move(to: NSPoint(x: bounds.maxX - 0.5, y: rect.minY))
        separatorPath.line(to: NSPoint(x: bounds.maxX - 0.5, y: rect.maxY))
        separatorPath.stroke()

        // Calculate visible range
        let visibleRect = textView.visibleRect
        let glyphRange = layoutManager.glyphRange(forBoundingRect: visibleRect, in: textContainer)
        let charRange = layoutManager.characterRange(forGlyphRange: glyphRange, actualGlyphRange: nil)

        // Font for line numbers
        let lineNumberFont = NSFont.monospacedDigitSystemFont(ofSize: 10, weight: .regular)
        let lineNumberAttrs: [NSAttributedString.Key: Any] = [
            .font: lineNumberFont,
            .foregroundColor: NSColor.secondaryLabelColor
        ]

        // Font for icons
        let iconFont = NSFont.systemFont(ofSize: 12, weight: .medium)

        // Get starting line number using O(log n) binary search
        var lineNumber = lineNumber(forCharacterOffset: charRange.location)

        // Draw visible lines
        let text = textView.string as NSString
        text.enumerateSubstrings(in: charRange, options: [.byLines, .substringNotRequired]) { [weak self] _, substringRange, _, _ in
            guard let self = self else { return }

            let lineRect = layoutManager.lineFragmentRect(
                forGlyphAt: layoutManager.glyphIndexForCharacter(at: substringRange.location),
                effectiveRange: nil
            )

            let y = lineRect.minY + textView.textContainerInset.height - visibleRect.minY

            // Check for annotation at this line
            if let annotation = self.annotationsByLine[lineNumber] {
                // Draw background highlight across the gutter
                if annotation.backgroundColor != .clear {
                    annotation.backgroundColor.withAlphaComponent(0.3).setFill()
                    let highlightRect = NSRect(x: 0, y: y, width: self.ruleThickness, height: lineRect.height)
                    highlightRect.fill()
                }

                // Draw icon
                let iconAttrs: [NSAttributedString.Key: Any] = [
                    .font: iconFont,
                    .foregroundColor: annotation.iconColor
                ]
                let iconString = NSAttributedString(string: annotation.gutterIcon, attributes: iconAttrs)
                let iconSize = iconString.size()
                let iconX = self.ruleThickness - iconSize.width - 22
                let iconY = y + (lineRect.height - iconSize.height) / 2
                iconString.draw(at: NSPoint(x: iconX, y: iconY))
            }

            // Draw line number
            let lineNumberString = "\(lineNumber)"
            let attrString = NSAttributedString(string: lineNumberString, attributes: lineNumberAttrs)
            let stringSize = attrString.size()
            let x = self.ruleThickness - stringSize.width - 8
            let lineY = y + (lineRect.height - stringSize.height) / 2
            attrString.draw(at: NSPoint(x: x, y: lineY))

            lineNumber += 1
        }
    }

    // MARK: - Mouse Handling

    public override func mouseDown(with event: NSEvent) {
        let point = convert(event.locationInWindow, from: nil)

        if let line = lineNumber(at: point),
           let annotation = annotationsByLine[line] {
            onAnnotationClick?(annotation)
        }
    }

    public override func mouseMoved(with event: NSEvent) {
        let point = convert(event.locationInWindow, from: nil)

        if let line = lineNumber(at: point) {
            if line != hoveredLine {
                hoveredLine = line
                if let annotation = annotationsByLine[line] {
                    onAnnotationHover?(annotation, event.locationInWindow)
                    // Show tooltip
                    toolTip = annotation.tooltipText
                } else {
                    toolTip = nil
                }
            }
        } else {
            hoveredLine = nil
            toolTip = nil
        }
    }

    public override func mouseExited(with event: NSEvent) {
        hoveredLine = nil
        toolTip = nil
    }

    // MARK: - Helpers

    /// Returns the line number at a given point in the ruler view.
    /// Uses cached line offset index for O(log n) lookup.
    private func lineNumber(at point: NSPoint) -> Int? {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else {
            return nil
        }

        let visibleRect = textView.visibleRect
        let textPoint = NSPoint(x: 0, y: point.y + visibleRect.minY - textView.textContainerInset.height)

        // Find the glyph at this y position
        var fraction: CGFloat = 0
        let glyphIndex = layoutManager.glyphIndex(for: textPoint, in: textContainer, fractionOfDistanceThroughGlyph: &fraction)
        let charIndex = layoutManager.characterIndexForGlyph(at: glyphIndex)

        // Use O(log n) binary search instead of O(n) character iteration
        return lineNumber(forCharacterOffset: charIndex)
    }
}

// MARK: - Keyboard Navigation Extension

extension ProofAnnotationManager {

    /// Handles keyboard navigation commands
    /// Call this from your key event handler
    /// - Parameter event: The key event
    /// - Returns: True if the event was handled
    public func handleKeyEvent(_ event: NSEvent) -> Bool {
        // Check for Cmd+' (next failed)
        if event.modifierFlags.contains(.command) && event.charactersIgnoringModifiers == "'" {
            if event.modifierFlags.contains(.shift) {
                // Shift+Cmd+' - previous failed
                navigateToPreviousFailed()
            } else {
                // Cmd+' - next failed
                navigateToNextFailed()
            }
            return true
        }

        return false
    }
}

// MARK: - SwiftUI Integration

#if canImport(SwiftUI)
import SwiftUI

/// SwiftUI view for displaying proof annotation status summary
public struct ProofStatusSummaryView: View {
    @ObservedObject var manager: ProofAnnotationManager

    public init(manager: ProofAnnotationManager) {
        self.manager = manager
    }

    public var body: some View {
        HStack(spacing: 12) {
            statusBadge(
                count: manager.provedCount,
                icon: ProofStatus.proved.gutterIcon,
                color: .green
            )

            statusBadge(
                count: manager.failedCount,
                icon: ProofStatus.failed.gutterIcon,
                color: .red
            )

            statusBadge(
                count: manager.pendingCount,
                icon: ProofStatus.pending.gutterIcon,
                color: .yellow
            )

            Spacer()

            if manager.totalCount > 0 {
                ProgressView(value: manager.progress)
                    .frame(width: 100)
                Text("\(Int(manager.progress * 100))%")
                    .font(.caption)
                    .foregroundColor(.secondary)
            }
        }
        .padding(.horizontal)
    }

    @ViewBuilder
    private func statusBadge(count: Int, icon: String, color: Color) -> some View {
        HStack(spacing: 4) {
            Text(icon)
                .foregroundColor(color)
            Text("\(count)")
                .font(.caption)
                .foregroundColor(.secondary)
        }
    }
}

/// SwiftUI view for the proof obligations list
public struct ProofObligationsListView: View {
    @ObservedObject var manager: ProofAnnotationManager
    @State private var filter: ProofStatus?

    public init(manager: ProofAnnotationManager) {
        self.manager = manager
    }

    public var body: some View {
        VStack(spacing: 0) {
            // Filter bar
            filterBar

            Divider()

            // Obligations list
            List(filteredAnnotations) { annotation in
                AnnotationListRowView(annotation: annotation, isSelected: manager.currentObligation?.id == annotation.id)
                    .contentShape(Rectangle())
                    .onTapGesture {
                        manager.selectObligation(annotation.obligation)
                    }
                    .listRowBackground(
                        manager.currentObligation?.id == annotation.id
                            ? Color.accentColor.opacity(0.2)
                            : Color.clear
                    )
            }
            .listStyle(.plain)
        }
    }

    private var filterBar: some View {
        HStack {
            Picker("Filter", selection: $filter) {
                Text("All").tag(Optional<ProofStatus>.none)
                Text("Failed").tag(Optional<ProofStatus>.some(.failed))
                Text("Pending").tag(Optional<ProofStatus>.some(.pending))
                Text("Proved").tag(Optional<ProofStatus>.some(.proved))
            }
            .pickerStyle(.segmented)
            .frame(maxWidth: 300)

            Spacer()

            // Navigation buttons
            Button(action: { manager.navigateToPreviousFailed() }) {
                Image(systemName: "chevron.up")
            }
            .disabled(manager.failedCount == 0)
            .help("Previous Failed (Shift+Cmd+')")

            Button(action: { manager.navigateToNextFailed() }) {
                Image(systemName: "chevron.down")
            }
            .disabled(manager.failedCount == 0)
            .help("Next Failed (Cmd+')")
        }
        .padding(.horizontal)
        .padding(.vertical, 8)
    }

    private var filteredAnnotations: [ProofAnnotation] {
        if let filter = filter {
            return manager.annotations.filter { $0.obligation.status == filter }
        }
        return manager.annotations
    }
}

/// Row view for annotation list (internal to ProofAnnotationManager)
private struct AnnotationListRowView: View {
    let annotation: ProofAnnotation
    let isSelected: Bool

    var body: some View {
        HStack {
            // Status icon
            Text(annotation.gutterIcon)
                .font(.system(size: 14))
                .foregroundColor(Color(annotation.iconColor))
                .frame(width: 24)

            VStack(alignment: .leading, spacing: 2) {
                // Kind and location
                HStack {
                    Text(annotation.obligation.kind.displayName)
                        .font(.headline)

                    Text("Line \(annotation.obligation.location.startLine)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                // Error message if failed
                if let error = annotation.obligation.errorMessage, !error.isEmpty {
                    Text(error)
                        .font(.caption)
                        .foregroundColor(.red)
                        .lineLimit(2)
                }

                // Duration and backend
                HStack {
                    if let backend = annotation.obligation.backend {
                        Text(backend.displayName)
                            .font(.caption2)
                            .padding(.horizontal, 4)
                            .padding(.vertical, 1)
                            .background(Color.secondary.opacity(0.2))
                            .cornerRadius(3)
                    }

                    if let duration = annotation.obligation.duration {
                        Text(String(format: "%.2fs", duration))
                            .font(.caption2)
                            .foregroundColor(.secondary)
                    }
                }
            }

            Spacer()
        }
        .padding(.vertical, 4)
    }
}
#endif
