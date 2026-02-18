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

                Spacer()
            }
            .padding(4)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Content
            switch selectedTab {
            case 0:
                ProblemsPanelContent(diagnostics: document.diagnostics)
            case 1:
                OutputPanelContent()
            case 2:
                ModelCheckPanelContent(document: document)
            default:
                EmptyView()
            }
        }
    }
}

// MARK: - Problems Panel

struct ProblemsPanelContent: View {
    let diagnostics: [TLADiagnostic]

    var body: some View {
        List {
            if diagnostics.isEmpty {
                Text("No problems")
                    .foregroundColor(.secondary)
            } else {
                ForEach(diagnostics) { diagnostic in
                    HStack {
                        diagnosticIcon(for: diagnostic.severity)
                        Text(diagnostic.message)
                            .font(.system(.body, design: .monospaced))
                            .textSelection(.enabled)
                        Spacer()
                        Text("Ln \(diagnostic.range.start.line + 1)")
                            .font(.caption)
                            .foregroundColor(.secondary)
                    }
                }
            }
        }
    }

    @ViewBuilder
    private func diagnosticIcon(for severity: TLADiagnosticSeverity) -> some View {
        switch severity {
        case .error:
            Image(systemName: "xmark.circle.fill").foregroundColor(.red)
        case .warning:
            Image(systemName: "exclamationmark.triangle.fill").foregroundColor(.yellow)
        case .information:
            Image(systemName: "info.circle.fill").foregroundColor(.blue)
        case .hint:
            Image(systemName: "lightbulb.fill").foregroundColor(.green)
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
        ModelCheckPanelCompact(document: document)
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
