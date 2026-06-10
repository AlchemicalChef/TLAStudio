import AppKit
import SwiftUI

// MARK: - Bottom Panel

struct BottomPanel: View {
    @ObservedObject var document: TLADocument
    @State private var selectedTab = 0

    private var errorCount: Int {
        document.diagnostics.filter { $0.severity == .error }.count
    }

    private var warningCount: Int {
        document.diagnostics.filter { $0.severity == .warning }.count
    }

    var body: some View {
        VStack(spacing: 0) {
            // Tab bar
            HStack {
                // Problems tab with badge
                Button {
                    selectedTab = 0
                } label: {
                    HStack(spacing: 4) {
                        Text("Problems")
                        if errorCount > 0 || warningCount > 0 {
                            BadgeView(
                                count: errorCount + warningCount,
                                color: errorCount > 0 ? .red : .orange
                            )
                        }
                    }
                }
                .buttonStyle(.plain)
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(selectedTab == 0 ? Color.accentColor.opacity(0.2) : Color.clear)
                .cornerRadius(4)

                Button("Output") { selectedTab = 1 }
                    .buttonStyle(.plain)
                    .padding(.horizontal, 8)
                    .padding(.vertical, 4)
                    .background(selectedTab == 1 ? Color.accentColor.opacity(0.2) : Color.clear)
                    .cornerRadius(4)

                // Model Check tab with status indicator
                Button {
                    selectedTab = 2
                } label: {
                    HStack(spacing: 4) {
                        Text("Model Check")
                        if let session = document.tlcSession, session.isRunning {
                            ProgressView()
                                .controlSize(.mini)
                                .scaleEffect(0.7)
                        } else if let result = document.lastTLCResult {
                            Image(systemName: result.success ? "checkmark.circle.fill" : "xmark.circle.fill")
                                .font(.caption2)
                                .foregroundColor(result.success ? .green : .red)
                        }
                    }
                }
                .buttonStyle(.plain)
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(selectedTab == 2 ? Color.accentColor.opacity(0.2) : Color.clear)
                .cornerRadius(4)

                // Simulator tab with live indicator
                Button {
                    selectedTab = 3
                } label: {
                    HStack(spacing: 4) {
                        Text("Simulator")
                        if document.simulationSession != nil {
                            Image(systemName: "circle.fill")
                                .font(.system(size: 6))
                                .foregroundColor(.green)
                        }
                    }
                }
                .buttonStyle(.plain)
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(selectedTab == 3 ? Color.accentColor.opacity(0.2) : Color.clear)
                .cornerRadius(4)

                // References tab with result count
                Button {
                    selectedTab = 4
                } label: {
                    HStack(spacing: 4) {
                        Text("References")
                        if let results = document.referenceResults {
                            BadgeView(count: results.hits.count, color: .blue)
                        }
                    }
                }
                .buttonStyle(.plain)
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(selectedTab == 4 ? Color.accentColor.opacity(0.2) : Color.clear)
                .cornerRadius(4)

                Spacer()
            }
            .padding(4)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Content
            switch selectedTab {
            case 0:
                ProblemsPanelContent(diagnostics: document.diagnostics) { diagnostic in
                    let offset = document.offset(
                        forLine: Int(diagnostic.range.start.line),
                        column: Int(diagnostic.range.start.column)
                    )
                    document.selectedRange = NSRange(location: offset, length: 0)
                }
            case 1:
                OutputPanelContent()
            case 2:
                ModelCheckPanelContent(document: document)
            case 3:
                SimulatorPanelContent(document: document)
            case 4:
                ReferencesPanelContent(document: document)
            default:
                EmptyView()
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .showReferencesPanel)) { notification in
            guard (notification.object as? TLADocument) === document else { return }
            selectedTab = 4
        }
        .onReceiveDocumentNotification(.showOutputPanel, for: document) {
            selectedTab = 1
        }
        .onReceiveDocumentNotification(.showModelCheckPanel, for: document) {
            selectedTab = 2
        }
    }
}

// MARK: - Problems Panel

struct ProblemsPanelContent: View {
    let diagnostics: [TLADiagnostic]
    /// Called when a row is clicked (navigates the editor to the diagnostic).
    var onNavigate: ((TLADiagnostic) -> Void)?

    private enum SourceFilter: String, CaseIterable, Identifiable {
        case all = "All"
        case syntax = "Syntax"
        case semantic = "Semantic"

        var id: String { rawValue }
    }

    @State private var sourceFilter: SourceFilter = .all

    private var filteredDiagnostics: [TLADiagnostic] {
        switch sourceFilter {
        case .all: return diagnostics
        case .syntax: return diagnostics.filter { !$0.isSemantic }
        case .semantic: return diagnostics.filter { $0.isSemantic }
        }
    }

    var body: some View {
        VStack(spacing: 0) {
            HStack {
                Picker("Source", selection: $sourceFilter) {
                    ForEach(SourceFilter.allCases) { filter in
                        Text(filter.rawValue).tag(filter)
                    }
                }
                .pickerStyle(.segmented)
                .labelsHidden()
                .frame(width: 220)
                .help("Filter problems by source: syntax (tree-sitter) or semantic (SANY)")

                Spacer()
            }
            .padding(.horizontal, 8)
            .padding(.vertical, 4)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            List {
                if filteredDiagnostics.isEmpty {
                    Text("No problems")
                        .foregroundColor(.secondary)
                } else {
                    ForEach(filteredDiagnostics) { diagnostic in
                        HStack {
                            diagnosticIcon(for: diagnostic.severity)
                            Text(diagnostic.message)
                                .font(.system(.body, design: .monospaced))
                                .textSelection(.enabled)
                            if let code = diagnostic.code {
                                Text(code)
                                    .font(.caption2)
                                    .padding(.horizontal, 4)
                                    .padding(.vertical, 1)
                                    .background(Color.secondary.opacity(0.2))
                                    .cornerRadius(3)
                                    .foregroundColor(.secondary)
                            }
                            Spacer()
                            Text("Ln \(diagnostic.range.start.line + 1)")
                                .font(.caption)
                                .foregroundColor(.secondary)
                        }
                        .contentShape(Rectangle())
                        .onTapGesture {
                            onNavigate?(diagnostic)
                        }
                    }
                }
            }
        }
    }

    private func diagnosticIcon(for severity: TLADiagnosticSeverity) -> some View {
        Image(systemName: severity.iconName).foregroundColor(severity.color)
    }
}

// MARK: - References Panel

/// Navigable results of Find All References (symbol-aware, comments/strings
/// excluded; matches by name across the current + EXTENDS'd modules).
struct ReferencesPanelContent: View {
    @ObservedObject var document: TLADocument

    var body: some View {
        if let results = document.referenceResults {
            VStack(alignment: .leading, spacing: 0) {
                HStack(spacing: 6) {
                    Text("\(results.hits.count) reference\(results.hits.count == 1 ? "" : "s") to '\(results.symbolName)'")
                        .font(.callout)
                    Text("matches by name")
                        .font(.caption2)
                        .foregroundColor(.secondary)
                    if !results.searchedExtendedModules {
                        Text("current module only")
                            .font(.caption2)
                            .foregroundColor(.orange)
                    }
                    if results.truncated {
                        Text("truncated")
                            .font(.caption2)
                            .foregroundColor(.orange)
                    }
                    Spacer()
                }
                .padding(.horizontal, 8)
                .padding(.vertical, 4)
                .background(Color(NSColor.controlBackgroundColor))

                Divider()

                if results.hits.isEmpty {
                    VStack {
                        Spacer()
                        Text("No references found")
                            .foregroundColor(.secondary)
                        Spacer()
                    }
                    .frame(maxWidth: .infinity)
                } else {
                    List(results.hits) { hit in
                        HStack(spacing: 6) {
                            Image(systemName: hit.role == .definition
                                  ? "equal.square.fill" : "arrow.turn.down.right")
                                .foregroundColor(hit.role == .definition ? .indigo : .secondary)
                                .font(.caption)
                            Text(hit.lineText)
                                .font(.system(.body, design: .monospaced))
                                .lineLimit(1)
                                .truncationMode(.tail)
                            Spacer()
                            Text("\(hit.moduleName) · Ln \(hit.tlaRange.start.line + 1)")
                                .font(.caption)
                                .foregroundColor(.secondary)
                        }
                        .contentShape(Rectangle())
                        .onTapGesture {
                            navigate(to: hit)
                        }
                    }
                }
            }
        } else {
            VStack(spacing: 8) {
                Image(systemName: "magnifyingglass")
                    .font(.title2)
                    .foregroundColor(.secondary)
                Text("Place the cursor on a symbol and choose Find All References (⇧⌘R)")
                    .font(.callout)
                    .foregroundColor(.secondary)
                    .multilineTextAlignment(.center)
                    .frame(maxWidth: 380)
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }

    private func navigate(to hit: ReferenceHit) {
        if let fileURL = hit.fileURL {
            // Cross-file hit: open (or focus) the document, then select.
            DocumentNavigator.open(fileURL: fileURL, andSelect: hit.tlaRange)
        } else if let nsRange = hit.nsRange {
            document.selectedRange = nsRange
        }
    }
}

// MARK: - Output Panel

struct OutputPanelContent: View {
    @ObservedObject private var outputManager = OutputManager.shared
    @State private var autoScroll = true

    var body: some View {
        VStack(spacing: 0) {
            // Toolbar
            HStack(spacing: 8) {
                // Source filter
                Picker("Source", selection: $outputManager.selectedSource) {
                    Text("All").tag(Optional<OutputManager.OutputSource>.none)
                    ForEach(OutputManager.OutputSource.allCases, id: \.self) { source in
                        Text(source.rawValue).tag(Optional(source))
                    }
                }
                .pickerStyle(.menu)
                .frame(width: 100)

                Toggle("Errors Only", isOn: $outputManager.showErrorsOnly)
                    .toggleStyle(.checkbox)

                Spacer()

                Toggle("Auto-scroll", isOn: $autoScroll)
                    .toggleStyle(.checkbox)

                Button(action: { outputManager.clear() }) {
                    Image(systemName: "trash")
                }
                .buttonStyle(.borderless)
                .help("Clear Output")
            }
            .padding(.horizontal, 8)
            .padding(.vertical, 4)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Output content
            if outputManager.filteredEntries.isEmpty {
                VStack {
                    Spacer()
                    Text("No output")
                        .foregroundColor(.secondary)
                    Spacer()
                }
            } else {
                SelectableOutputView(
                    entries: outputManager.filteredEntries,
                    autoScroll: autoScroll
                )
            }
        }
    }
}

// MARK: - Selectable Output View

/// A text view that allows selecting text across multiple lines
struct SelectableOutputView: NSViewRepresentable {
    let entries: [OutputManager.OutputEntry]
    let autoScroll: Bool

    func makeNSView(context: Context) -> NSScrollView {
        let scrollView = NSScrollView()
        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = false
        scrollView.autohidesScrollers = true

        let textView = NSTextView()
        textView.isEditable = false
        textView.isSelectable = true
        textView.backgroundColor = .clear
        textView.drawsBackground = false
        textView.font = NSFont.monospacedSystemFont(ofSize: 11, weight: .regular)
        textView.textContainerInset = NSSize(width: 8, height: 4)
        textView.autoresizingMask = [.width]
        textView.isVerticallyResizable = true
        textView.isHorizontallyResizable = false
        textView.textContainer?.widthTracksTextView = true
        textView.textContainer?.containerSize = NSSize(width: CGFloat.greatestFiniteMagnitude, height: CGFloat.greatestFiniteMagnitude)

        scrollView.documentView = textView
        return scrollView
    }

    func updateNSView(_ scrollView: NSScrollView, context: Context) {
        guard let textView = scrollView.documentView as? NSTextView else { return }

        let attributedString = NSMutableAttributedString()

        for entry in entries {
            // Timestamp
            let timestamp = NSAttributedString(
                string: entry.formattedTimestamp + "  ",
                attributes: [
                    .font: NSFont.monospacedSystemFont(ofSize: 10, weight: .regular),
                    .foregroundColor: NSColor.secondaryLabelColor
                ]
            )
            attributedString.append(timestamp)

            // Source
            let sourceColor: NSColor = {
                switch entry.source {
                case .tlc: return .systemBlue
                case .tlapm: return .systemPurple
                case .parser: return .systemGreen
                case .system: return .systemGray
                }
            }()
            let source = NSAttributedString(
                string: "[\(entry.source.rawValue)]  ",
                attributes: [
                    .font: NSFont.monospacedSystemFont(ofSize: 10, weight: .medium),
                    .foregroundColor: sourceColor
                ]
            )
            attributedString.append(source)

            // Message
            let message = NSAttributedString(
                string: entry.message + "\n",
                attributes: [
                    .font: NSFont.monospacedSystemFont(ofSize: 11, weight: .regular),
                    .foregroundColor: entry.isError ? NSColor.systemRed : NSColor.textColor
                ]
            )
            attributedString.append(message)
        }

        textView.textStorage?.setAttributedString(attributedString)

        // Auto-scroll to bottom
        if autoScroll && !entries.isEmpty {
            textView.scrollToEndOfDocument(nil)
        }
    }
}

// MARK: - Output Entry Row

struct OutputEntryRow: View {
    let entry: OutputManager.OutputEntry

    var body: some View {
        HStack(alignment: .top, spacing: 8) {
            Text(entry.formattedTimestamp)
                .font(.system(size: 10, design: .monospaced))
                .foregroundColor(.secondary)
                .frame(width: 60, alignment: .leading)

            Text("[\(entry.source.rawValue)]")
                .font(.system(size: 10, weight: .medium, design: .monospaced))
                .foregroundColor(sourceColor(entry.source))
                .frame(width: 50, alignment: .leading)

            Text(entry.message)
                .font(.system(size: 11, design: .monospaced))
                .foregroundColor(entry.isError ? .red : .primary)
                .textSelection(.enabled)

            Spacer()
        }
        .padding(.vertical, 1)
    }

    private func sourceColor(_ source: OutputManager.OutputSource) -> Color {
        switch source {
        case .tlc: return .blue
        case .tlapm: return .purple
        case .parser: return .orange
        case .system: return .gray
        }
    }
}

// MARK: - Model Check Panel

struct ModelCheckPanelContent: View {
    @ObservedObject var document: TLADocument

    var body: some View {
        // The FULL panel: trace explorer, state graph, coverage, checkpoints,
        // and the proof workbench. The compact summary previously mounted here
        // left the counterexample trace unreachable (platform review C1).
        ModelCheckPanel(document: document)
    }
}

// MARK: - Badge View

/// A small badge showing a count, typically for notifications/errors
struct BadgeView: View {
    let count: Int
    let color: Color

    var body: some View {
        Text("\(count)")
            .font(.system(size: 10, weight: .bold))
            .foregroundColor(.white)
            .padding(.horizontal, 5)
            .padding(.vertical, 1)
            .background(color)
            .clipShape(Capsule())
    }
}
