import SwiftUI
import os

// MARK: - Proof Obligations Panel

private let logger = Log.logger(category: "ProofPanel")

/// Main panel for displaying TLAPM proof obligations in a hierarchical tree.
///
/// Features:
/// - Hierarchical display of proof obligations using disclosure groups
/// - Status icons showing proof state (proved, failed, pending, etc.)
/// - Filtering by status (All / Proved / Failed / Pending)
/// - Click to navigate to source location
/// - Backend prover badges
/// - Duration display for each obligation
/// - Toolbar with Check All, Check Selected, Stop, Clear Results buttons
/// - Progress bar during proof checking
/// - Summary statistics footer
struct ProofObligationsPanel: View {
    @ObservedObject var session: ProofSession
    @State private var filter: ObligationFilter = .all
    @State private var selectedObligationId: UUID?
    var onJumpToSource: ((ProofSourceLocation) -> Void)?

    var body: some View {
        VStack(spacing: 0) {
            // Toolbar
            toolbarView

            Divider()

            // Filter tabs
            filterTabsView

            Divider()

            // Progress bar (when running)
            if session.isRunning, let progress = session.progress {
                progressView(progress)
            }

            // Content
            if session.obligations.isEmpty && !session.isRunning {
                emptyStateView
            } else {
                obligationsListView
            }

            Divider()

            // Summary footer
            summaryFooterView
        }
    }

    // MARK: - Toolbar

    private var toolbarView: some View {
        HStack(spacing: 12) {
            // Run buttons
            if session.isRunning {
                Button(action: session.stop) {
                    Label("Stop", systemImage: "stop.fill")
                }
                .buttonStyle(.bordered)
                .tint(.red)
            } else {
                Button(action: session.start) {
                    Label("Check All", systemImage: "checkmark.shield")
                }
                .buttonStyle(.borderedProminent)

                Button(action: checkSelected) {
                    Label("Check Selected", systemImage: "checkmark.circle")
                }
                .buttonStyle(.bordered)
                .disabled(selectedObligationId == nil)
            }

            Spacer()

            // Clear button
            Button(action: session.clearResults) {
                Label("Clear Results", systemImage: "trash")
            }
            .buttonStyle(.bordered)
            .disabled(session.obligations.isEmpty)
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
        .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: - Filter Tabs

    private var filterTabsView: some View {
        Picker("Filter", selection: $filter) {
            Text("All").tag(ObligationFilter.all)
            Text("Proved").tag(ObligationFilter.proved)
            Text("Failed").tag(ObligationFilter.failed)
            Text("Pending").tag(ObligationFilter.pending)
        }
        .pickerStyle(.segmented)
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
    }

    // MARK: - Progress View

    private func progressView(_ progress: ProofProgress) -> some View {
        VStack(spacing: 4) {
            HStack {
                ProgressView()
                    .controlSize(.small)

                if let current = progress.currentObligation {
                    Text("Checking: \(current.kind.displayName)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                        .lineLimit(1)
                } else {
                    Text(progress.phase == .parsing ? "Parsing..." : "Checking proofs...")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                Spacer()

                let completed = progress.provedCount + progress.failedCount
                Text("\(completed)/\(progress.totalObligations)")
                    .font(.caption)
                    .monospacedDigit()
                    .foregroundColor(.secondary)
            }

            if progress.totalObligations > 0 {
                ProgressView(value: progress.completionPercentage)
                    .progressViewStyle(.linear)
            } else {
                ProgressView()
                    .progressViewStyle(.linear)
            }
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
        .background(Color.accentColor.opacity(0.1))
    }

    // MARK: - Empty State

    private var emptyStateView: some View {
        VStack(spacing: 16) {
            Image(systemName: "checkmark.shield")
                .font(.largeTitle)
                .foregroundColor(.secondary)

            Text("No Proof Obligations")
                .font(.headline)

            Text("Click 'Check All' to run TLAPM and verify proofs")
                .font(.callout)
                .foregroundColor(.secondary)
                .multilineTextAlignment(.center)

            if let error = session.error {
                Text(error.localizedDescription)
                    .font(.caption)
                    .foregroundColor(.red)
                    .padding()
                    .background(Color.red.opacity(0.1))
                    .cornerRadius(8)
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .padding()
    }

    // MARK: - Obligations List

    private var obligationsListView: some View {
        List(selection: $selectedObligationId) {
            ForEach(filteredObligationTrees) { tree in
                ObligationTreeRow(
                    tree: tree,
                    selectedId: $selectedObligationId,
                    filter: filter,
                    onJumpToSource: onJumpToSource
                )
            }
        }
        .listStyle(.sidebar)
    }

    private var filteredObligationTrees: [ObligationTree] {
        let trees = session.obligationTree
        return trees.compactMap { filterTree($0) }
    }

    private func filterTree(_ tree: ObligationTree) -> ObligationTree? {
        // Check if this tree node matches the filter
        let matchesSelf = filter.matches(tree.obligation.status)

        // Recursively filter children
        let filteredChildren = tree.children.compactMap { filterTree($0) }

        // Include if self matches or has matching children
        if matchesSelf || !filteredChildren.isEmpty {
            var filtered = tree
            filtered.children = filteredChildren
            return filtered
        }

        return nil
    }

    // MARK: - Summary Footer

    private var summaryFooterView: some View {
        HStack {
            // Status summary
            if let result = session.result {
                Image(systemName: result.success ? "checkmark.circle.fill" : "xmark.circle.fill")
                    .foregroundColor(result.success ? .green : .red)

                Text(session.summaryString)
                    .font(.caption)
            } else if session.isRunning {
                ProgressView()
                    .controlSize(.small)
                Text("Checking...")
                    .font(.caption)
                    .foregroundColor(.secondary)
            } else {
                Text(session.summaryString)
                    .font(.caption)
                    .foregroundColor(.secondary)
            }

            Spacer()

            // Duration
            if let result = session.result {
                Text(formatDuration(result.duration))
                    .font(.caption)
                    .foregroundColor(.secondary)
            }
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
        .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: - Actions

    private func checkSelected() {
        logger.debug("checkSelected: Called, selectedObligationId=\(String(describing: selectedObligationId))")
        guard let selectedId = selectedObligationId,
              let obligation = session.findObligation(by: selectedId) else {
            logger.debug("checkSelected: GUARD FAILED - no selection or obligation not found")
            return
        }
        logger.debug("checkSelected: Calling session.checkStep at line \(obligation.location.startLine)")
        session.checkStep(
            line: obligation.location.startLine,
            column: obligation.location.startColumn
        )
    }

    // MARK: - Formatting

    private func formatDuration(_ seconds: TimeInterval) -> String {
        if seconds < 1 {
            return String(format: "%.0fms", seconds * 1000)
        } else if seconds < 60 {
            return String(format: "%.1fs", seconds)
        } else if seconds < 3600 {
            let mins = Int(seconds / 60)
            let secs = Int(seconds.truncatingRemainder(dividingBy: 60))
            return "\(mins)m \(secs)s"
        } else {
            let hours = Int(seconds / 3600)
            let mins = Int((seconds.truncatingRemainder(dividingBy: 3600)) / 60)
            return "\(hours)h \(mins)m"
        }
    }
}

// MARK: - Obligation Filter

enum ObligationFilter: String, CaseIterable {
    case all
    case proved
    case failed
    case pending

    func matches(_ status: ProofStatus) -> Bool {
        switch self {
        case .all:
            return true
        case .proved:
            return status == .proved || status == .trivial
        case .failed:
            return status == .failed || status == .timeout
        case .pending:
            return status == .pending || status == .unknown || status == .omitted
        }
    }
}

// MARK: - Obligation Tree Row

/// A row in the proof obligations tree that can expand to show children.
struct ObligationTreeRow: View {
    let tree: ObligationTree
    @Binding var selectedId: UUID?
    let filter: ObligationFilter
    var onJumpToSource: ((ProofSourceLocation) -> Void)?

    @State private var isExpanded = true

    var body: some View {
        if tree.children.isEmpty {
            // Leaf node - just show the row
            ObligationRowView(
                obligation: tree.obligation,
                isSelected: selectedId == tree.obligation.id,
                onJumpToSource: onJumpToSource
            )
            .tag(tree.obligation.id)
        } else {
            // Parent node - show disclosure group
            DisclosureGroup(isExpanded: $isExpanded) {
                ForEach(tree.children) { child in
                    ObligationTreeRow(
                        tree: child,
                        selectedId: $selectedId,
                        filter: filter,
                        onJumpToSource: onJumpToSource
                    )
                }
            } label: {
                ObligationRowView(
                    obligation: tree.obligation,
                    isSelected: selectedId == tree.obligation.id,
                    onJumpToSource: onJumpToSource
                )
            }
            .tag(tree.obligation.id)
        }
    }
}

// MARK: - Obligation Row View

/// A single row displaying a proof obligation.
struct ObligationRowView: View {
    let obligation: ProofObligation
    let isSelected: Bool
    var onJumpToSource: ((ProofSourceLocation) -> Void)?

    var body: some View {
        HStack(spacing: 8) {
            // Status icon
            statusIcon
                .frame(width: 20)

            // Name and details
            VStack(alignment: .leading, spacing: 2) {
                Text(displayName)
                    .font(.system(.body, design: .monospaced))
                    .fontWeight(isSelected ? .semibold : .regular)
                    .lineLimit(1)

                if let message = obligation.errorMessage, !message.isEmpty {
                    Text(message)
                        .font(.caption)
                        .foregroundColor(.secondary)
                        .lineLimit(1)
                }
            }

            Spacer()

            // Backend badge
            if let backend = obligation.backend {
                BackendBadge(backend: backend)
            }

            // Duration
            if let duration = obligation.duration {
                Text(formatDuration(duration))
                    .font(.caption)
                    .foregroundColor(.secondary)
                    .monospacedDigit()
            }

            // Jump to source button
            Button {
                onJumpToSource?(obligation.location)
            } label: {
                Image(systemName: "arrow.right.circle")
                    .foregroundColor(.secondary)
            }
            .buttonStyle(.plain)
            .help("Jump to source")
        }
        .padding(.vertical, 4)
        .contentShape(Rectangle())
    }

    private var displayName: String {
        // Combine kind and location info for display
        let kindName = obligation.kind.displayName
        let line = obligation.location.startLine
        return "\(kindName) (line \(line))"
    }

    @ViewBuilder
    private var statusIcon: some View {
        switch obligation.status {
        case .proved:
            Text("\u{2713}")
                .foregroundColor(.green)
                .fontWeight(.bold)
        case .failed:
            Text("\u{2717}")
                .foregroundColor(.red)
                .fontWeight(.bold)
        case .pending, .unknown:
            Text("\u{22EF}")
                .foregroundColor(.yellow)
        case .timeout:
            Text("\u{23F0}")
                .foregroundColor(.orange)
        case .omitted:
            Text("\u{25CB}")
                .foregroundColor(.gray)
        case .trivial:
            Text("\u{2728}")
                .foregroundColor(.green)
        }
    }

    private func formatDuration(_ seconds: TimeInterval) -> String {
        if seconds < 1 {
            return String(format: "%.0fms", seconds * 1000)
        } else if seconds < 60 {
            return String(format: "%.1fs", seconds)
        } else {
            let mins = Int(seconds / 60)
            let secs = Int(seconds.truncatingRemainder(dividingBy: 60))
            return "\(mins)m \(secs)s"
        }
    }
}

// MARK: - Backend Badge

/// A small badge showing the prover backend.
struct BackendBadge: View {
    let backend: ProverBackend

    var body: some View {
        Text(backend.shortName)
            .font(.caption2)
            .fontWeight(.medium)
            .padding(.horizontal, 6)
            .padding(.vertical, 2)
            .background(backgroundColor)
            .foregroundColor(.white)
            .cornerRadius(4)
            .help(backend.displayName)
    }

    private var backgroundColor: Color {
        switch backend {
        case .auto:
            return .gray
        case .zenon:
            return .blue
        case .z3:
            return .orange
        case .isabelle:
            return .purple
        case .cvc5:
            return .teal
        case .spass:
            return .indigo
        case .ls4:
            return .green
        }
    }
}

// MARK: - Compact Proof Panel

/// Smaller version of the proof panel for embedding in a bottom bar or toolbar.
struct ProofPanelCompact: View {
    @ObservedObject var session: ProofSession

    var body: some View {
        HStack {
            // Status
            if session.isRunning {
                ProgressView()
                    .controlSize(.small)

                if let progress = session.progress {
                    let completed = progress.provedCount + progress.failedCount
                    Text("\(completed)/\(progress.totalObligations)")
                        .font(.caption)
                        .monospacedDigit()
                }

                Spacer()

                Button("Stop") {
                    session.stop()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
            } else if let result = session.result {
                Image(systemName: result.success ? "checkmark.circle.fill" : "xmark.circle.fill")
                    .foregroundColor(result.success ? .green : .red)

                Text(session.summaryString)
                    .font(.caption)

                Spacer()

                Button("Check Again") {
                    session.start()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
            } else {
                Text("Ready to check proofs")
                    .font(.caption)
                    .foregroundColor(.secondary)

                Spacer()

                Button("Check Proofs") {
                    session.start()
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.small)
            }
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
    }
}

// MARK: - Preview

#if DEBUG
struct ProofObligationsPanel_Previews: PreviewProvider {
    static var previews: some View {
        let session = ProofSession(specURL: URL(fileURLWithPath: "/tmp/test.tla"))

        return ProofObligationsPanel(session: session)
            .frame(width: 400, height: 500)
    }
}
#endif
