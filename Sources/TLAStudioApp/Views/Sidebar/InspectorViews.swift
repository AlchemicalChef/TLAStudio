import SwiftUI

// MARK: - Enhanced Inspector Sidebar

/// Enhanced inspector sidebar with document info, model checking, and proofs
struct EnhancedInspectorSidebar: View {
    @ObservedObject var document: TLADocument
    @State private var selectedTab = 0

    // Computed badge counts
    private var modelCheckBadge: (count: Int, color: Color)? {
        if let session = document.tlcSession, session.isRunning {
            return nil // Show spinner instead
        }
        if let result = document.lastTLCResult, !result.success {
            return (1, .red)
        }
        return nil
    }

    private var proofBadge: (count: Int, color: Color)? {
        if let result = document.lastProofResult {
            if result.failedCount > 0 {
                return (result.failedCount, .red)
            } else if result.provedCount > 0 {
                return (result.provedCount, .green)
            }
        }
        return nil
    }

    var body: some View {
        VStack(spacing: 0) {
            // Custom tab bar with badges
            HStack(spacing: 4) {
                // Info tab
                TabButton(
                    icon: "info.circle",
                    isSelected: selectedTab == 0,
                    badge: nil,
                    action: { selectedTab = 0 }
                )
                .help("Document Info")

                // Model Check tab
                TabButton(
                    icon: "play.rectangle",
                    isSelected: selectedTab == 1,
                    badge: modelCheckBadge,
                    isRunning: document.tlcSession?.isRunning ?? false,
                    action: { selectedTab = 1 }
                )
                .help("Model Check (⌘R)")

                // Proof tab
                TabButton(
                    icon: "checkmark.seal",
                    isSelected: selectedTab == 2,
                    badge: proofBadge,
                    isRunning: document.proofSession?.isRunning ?? false,
                    action: { selectedTab = 2 }
                )
                .help("Proofs (⇧⌘P)")
            }
            .padding(8)

            Divider()

            // Tab content
            switch selectedTab {
            case 0:
                DocumentInfoView(document: document)
            case 1:
                ModelCheckInspector(document: document)
            case 2:
                ProofInspector(document: document)
            default:
                EmptyView()
            }
        }
    }
}

// MARK: - Tab Button with Badge

private struct TabButton: View {
    let icon: String
    let isSelected: Bool
    var badge: (count: Int, color: Color)?
    var isRunning: Bool = false
    let action: () -> Void

    var body: some View {
        Button(action: action) {
            ZStack(alignment: .topTrailing) {
                Image(systemName: icon)
                    .font(.system(size: 14))
                    .frame(width: 28, height: 28)
                    .background(isSelected ? Color.accentColor.opacity(0.2) : Color.clear)
                    .cornerRadius(6)

                // Running indicator
                if isRunning {
                    Circle()
                        .fill(Color.orange)
                        .frame(width: 8, height: 8)
                        .overlay(
                            Circle()
                                .stroke(Color(NSColor.controlBackgroundColor), lineWidth: 1)
                        )
                        .offset(x: 2, y: -2)
                }
                // Badge
                else if let badge = badge {
                    Text("\(badge.count)")
                        .font(.system(size: 9, weight: .bold))
                        .foregroundColor(.white)
                        .padding(.horizontal, 4)
                        .padding(.vertical, 1)
                        .background(badge.color)
                        .clipShape(Capsule())
                        .offset(x: 4, y: -4)
                }
            }
        }
        .buttonStyle(.plain)
    }
}

// MARK: - Document Info View

struct DocumentInfoView: View {
    @ObservedObject var document: TLADocument

    private var lineCount: Int {
        document.content.components(separatedBy: "\n").count
    }

    private var characterCount: Int {
        document.content.count
    }

    private var wordCount: Int {
        document.content.split(whereSeparator: { $0.isWhitespace || $0.isNewline }).count
    }

    var body: some View {
        List {
            // File Info Section
            Section("Document") {
                LabeledContent("File") {
                    if let url = document.fileURL {
                        Text(url.lastPathComponent)
                            .font(.caption)
                            .foregroundColor(.secondary)
                    } else {
                        Text("Untitled")
                            .font(.caption)
                            .foregroundColor(.secondary)
                            .italic()
                    }
                }

                LabeledContent("Encoding") {
                    Text(document.encoding == .utf8 ? "UTF-8" : "Windows-1252")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                LabeledContent("Line Endings") {
                    Text(lineEndingName)
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
            }

            // Statistics Section
            Section("Statistics") {
                LabeledContent("Lines") {
                    Text("\(lineCount)")
                        .font(.caption.monospacedDigit())
                        .foregroundColor(.secondary)
                }

                LabeledContent("Characters") {
                    Text("\(characterCount)")
                        .font(.caption.monospacedDigit())
                        .foregroundColor(.secondary)
                }

                LabeledContent("Words") {
                    Text("\(wordCount)")
                        .font(.caption.monospacedDigit())
                        .foregroundColor(.secondary)
                }
            }

            // Symbols Section
            Section("Symbols") {
                symbolsSummary
            }

            // Diagnostics Section
            Section("Diagnostics") {
                diagnosticsSummary
            }

            // Cursor Position Section
            Section("Cursor") {
                cursorPositionView
            }
        }
        .listStyle(.sidebar)
    }

    private var lineEndingName: String {
        switch document.lineEnding {
        case .lf: return "Unix (LF)"
        case .crlf: return "Windows (CRLF)"
        case .cr: return "Classic Mac (CR)"
        }
    }

    @ViewBuilder
    private var symbolsSummary: some View {
        let symbols = document.symbols
        let total = countSymbols(symbols)
        let byKind = groupSymbolsByKind(symbols)

        LabeledContent("Total") {
            Text("\(total)")
                .font(.caption.monospacedDigit())
                .foregroundColor(.secondary)
        }

        ForEach(Array(byKind.keys.sorted(by: { $0.displayName < $1.displayName })), id: \.self) { kind in
            LabeledContent(kind.pluralDisplayName) {
                Text("\(byKind[kind] ?? 0)")
                    .font(.caption.monospacedDigit())
                    .foregroundColor(.secondary)
            }
        }
    }

    @ViewBuilder
    private var diagnosticsSummary: some View {
        let errors = document.diagnostics.filter { $0.severity == .error }.count
        let warnings = document.diagnostics.filter { $0.severity == .warning }.count
        let hints = document.diagnostics.filter { $0.severity == .hint || $0.severity == .information }.count

        HStack {
            Image(systemName: "xmark.circle.fill")
                .foregroundColor(.red)
            Text("Errors")
            Spacer()
            Text("\(errors)")
                .font(.caption.monospacedDigit())
                .foregroundColor(errors > 0 ? .red : .secondary)
        }

        HStack {
            Image(systemName: "exclamationmark.triangle.fill")
                .foregroundColor(.yellow)
            Text("Warnings")
            Spacer()
            Text("\(warnings)")
                .font(.caption.monospacedDigit())
                .foregroundColor(warnings > 0 ? .orange : .secondary)
        }

        HStack {
            Image(systemName: "lightbulb.fill")
                .foregroundColor(.blue)
            Text("Hints")
            Spacer()
            Text("\(hints)")
                .font(.caption.monospacedDigit())
                .foregroundColor(.secondary)
        }
    }

    private var cursorPositionView: some View {
        let (line, column) = document.lineAndColumn(for: document.selectedRange.location)

        return Group {
            LabeledContent("Line") {
                Text("\(line + 1)")
                    .font(.caption.monospacedDigit())
                    .foregroundColor(.secondary)
            }

            LabeledContent("Column") {
                Text("\(column + 1)")
                    .font(.caption.monospacedDigit())
                    .foregroundColor(.secondary)
            }

            if document.selectedRange.length > 0 {
                LabeledContent("Selection") {
                    Text("\(document.selectedRange.length) chars")
                        .font(.caption.monospacedDigit())
                        .foregroundColor(.secondary)
                }
            }
        }
    }

    private func countSymbols(_ symbols: [TLASymbol]) -> Int {
        symbols.reduce(0) { count, symbol in
            count + 1 + countSymbols(symbol.children)
        }
    }

    private func groupSymbolsByKind(_ symbols: [TLASymbol]) -> [TLASymbolKind: Int] {
        var counts: [TLASymbolKind: Int] = [:]

        func count(_ symbols: [TLASymbol]) {
            for symbol in symbols {
                counts[symbol.kind, default: 0] += 1
                count(symbol.children)
            }
        }

        count(symbols)
        return counts
    }
}

// MARK: - Model Check Inspector

struct ModelCheckInspector: View {
    @ObservedObject var document: TLADocument

    var body: some View {
        List {
            // Status Section
            Section("Status") {
                statusView
            }

            // Configuration Section
            Section("Configuration") {
                configurationView
            }

            // Results Section
            if let result = document.lastTLCResult {
                Section("Last Result") {
                    resultSummaryView(result)
                }
            }

            // Actions Section
            Section {
                actionButtonsView
            }
        }
        .listStyle(.sidebar)
    }

    @ViewBuilder
    private var statusView: some View {
        if let session = document.tlcSession, session.isRunning {
            HStack {
                ProgressView()
                    .controlSize(.small)
                Text("Running...")
                    .foregroundColor(.secondary)
            }

            if let progress = session.progress {
                LabeledContent("States") {
                    Text("\(progress.distinctStates)")
                        .font(.caption.monospacedDigit())
                }

                LabeledContent("Remaining") {
                    Text("\(progress.statesLeft)")
                        .font(.caption.monospacedDigit())
                }
            }
        } else if document.lastTLCResult != nil {
            HStack {
                Image(systemName: document.lastTLCResult!.success ? "checkmark.circle.fill" : "xmark.circle.fill")
                    .foregroundColor(document.lastTLCResult!.success ? .green : .red)
                Text(document.lastTLCResult!.success ? "Passed" : "Failed")
            }
        } else {
            HStack {
                Image(systemName: "circle.dashed")
                    .foregroundColor(.secondary)
                Text("Not Run")
                    .foregroundColor(.secondary)
            }
        }
    }

    @ViewBuilder
    private var configurationView: some View {
        if let session = document.tlcSession {
            LabeledContent("Workers") {
                Text("\(session.config.workers)")
                    .font(.caption.monospacedDigit())
            }

            LabeledContent("Invariants") {
                Text("\(session.config.invariants.count)")
                    .font(.caption.monospacedDigit())
            }
        } else {
            Text("No configuration")
                .foregroundColor(.secondary)
                .font(.caption)
        }
    }

    @ViewBuilder
    private func resultSummaryView(_ result: ModelCheckResult) -> some View {
        LabeledContent("Duration") {
            Text(formatDuration(result.duration))
                .font(.caption.monospacedDigit())
        }

        LabeledContent("States Found") {
            Text("\(result.distinctStates)")
                .font(.caption.monospacedDigit())
        }

        if let error = result.errorTrace {
            HStack {
                Image(systemName: "exclamationmark.triangle.fill")
                    .foregroundColor(.orange)
                Text("Error trace: \(error.states.count) states")
                    .font(.caption)
            }
        }
    }

    @ViewBuilder
    private var actionButtonsView: some View {
        if let session = document.tlcSession, session.isRunning {
            Button(role: .destructive) {
                document.stopModelCheck()
            } label: {
                Label("Stop", systemImage: "stop.fill")
            }
        } else {
            Button {
                document.runModelCheck()
            } label: {
                Label("Run TLC", systemImage: "play.fill")
            }
            .buttonStyle(.borderedProminent)
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

// MARK: - Proof Inspector

struct ProofInspector: View {
    @ObservedObject var document: TLADocument
    @State private var selectedObligationId: UUID?

    var body: some View {
        List {
            // Status Section
            Section("Status") {
                proofStatusView
            }

            // Obligations Summary
            if let session = document.proofSession {
                Section("Obligations") {
                    obligationsSummaryView(session)
                }

                // Individual obligations list
                if !session.obligations.isEmpty {
                    Section("Obligation Details") {
                        ForEach(session.obligations, id: \.id) { obligation in
                            HStack {
                                Text(obligation.status.icon)
                                    .frame(width: 20)
                                Text("Line \(obligation.location.startLine)")
                                Spacer()
                                Text(obligation.status.displayName)
                                    .font(.caption)
                                    .foregroundColor(obligation.status.color)
                            }
                            .contentShape(Rectangle())
                            .onTapGesture {
                                selectedObligationId = obligation.id
                            }
                            .background(selectedObligationId == obligation.id ? Color.accentColor.opacity(0.2) : Color.clear)
                        }
                    }
                }
            }

            // Results Section
            if let result = document.lastProofResult {
                Section("Last Result") {
                    proofResultSummaryView(result)
                }
            }

            // Actions Section
            Section {
                proofActionsView
            }
        }
        .listStyle(.sidebar)
    }

    @ViewBuilder
    private var proofStatusView: some View {
        if let session = document.proofSession, session.isRunning {
            HStack {
                ProgressView()
                    .controlSize(.small)
                Text("Checking...")
                    .foregroundColor(.secondary)
            }

            if let progress = session.progress {
                ProgressView(value: progress.completionPercentage)
                    .progressViewStyle(.linear)

                Text("\(progress.provedCount + progress.failedCount) / \(progress.totalObligations)")
                    .font(.caption.monospacedDigit())
                    .foregroundColor(.secondary)
            }
        } else if document.lastProofResult != nil {
            HStack {
                if document.lastProofResult!.obligations.isEmpty {
                    Image(systemName: "doc.text")
                        .foregroundColor(.secondary)
                    Text("No Proofs Found")
                        .foregroundColor(.secondary)
                } else if document.lastProofResult!.success {
                    Image(systemName: "checkmark.seal.fill")
                        .foregroundColor(.green)
                    Text("All \(document.lastProofResult!.provedCount) Proved")
                } else {
                    Image(systemName: "xmark.seal.fill")
                        .foregroundColor(.red)
                    Text("\(document.lastProofResult!.failedCount) Failed")
                }
            }
        } else {
            HStack {
                Image(systemName: "seal")
                    .foregroundColor(.secondary)
                Text("Not Checked")
                    .foregroundColor(.secondary)
            }
        }
    }

    @ViewBuilder
    private func obligationsSummaryView(_ session: ProofSession) -> some View {
        let obligations = session.obligations

        LabeledContent("Total") {
            Text("\(obligations.count)")
                .font(.caption.monospacedDigit())
        }

        HStack {
            Image(systemName: "checkmark.circle.fill")
                .foregroundColor(.green)
            Text("Proved")
            Spacer()
            Text("\(obligations.filter { $0.status == .proved || $0.status == .trivial }.count)")
                .font(.caption.monospacedDigit())
        }

        HStack {
            Image(systemName: "xmark.circle.fill")
                .foregroundColor(.red)
            Text("Failed")
            Spacer()
            Text("\(obligations.filter { $0.status == .failed }.count)")
                .font(.caption.monospacedDigit())
        }

        HStack {
            Image(systemName: "clock.fill")
                .foregroundColor(.orange)
            Text("Pending")
            Spacer()
            Text("\(obligations.filter { $0.status == .pending || $0.status == .unknown }.count)")
                .font(.caption.monospacedDigit())
        }
    }

    @ViewBuilder
    private func proofResultSummaryView(_ result: ProofCheckResult) -> some View {
        LabeledContent("Duration") {
            Text(formatDuration(result.duration))
                .font(.caption.monospacedDigit())
        }

        LabeledContent("Proved") {
            Text("\(result.provedCount)")
                .font(.caption.monospacedDigit())
                .foregroundColor(.green)
        }

        LabeledContent("Failed") {
            Text("\(result.failedCount)")
                .font(.caption.monospacedDigit())
                .foregroundColor(result.failedCount > 0 ? .red : .secondary)
        }
    }

    @ViewBuilder
    private var proofActionsView: some View {
        if let session = document.proofSession, session.isRunning {
            Button(role: .destructive) {
                document.stopProofCheck()
            } label: {
                Label("Stop", systemImage: "stop.fill")
            }
        } else {
            Button {
                document.runProofCheck()
            } label: {
                Label("Check Proofs", systemImage: "checkmark.seal")
            }
            .buttonStyle(.borderedProminent)

            Button {
                document.checkSelectionProofStep()
            } label: {
                Label("Check Selection", systemImage: "scope")
            }

            // Check Selected obligation
            if let session = document.proofSession, !session.obligations.isEmpty {
                Divider()

                Picker("Obligation", selection: $selectedObligationId) {
                    Text("Select...").tag(nil as UUID?)
                    ForEach(session.obligations, id: \.id) { obligation in
                        Text("Line \(obligation.location.startLine)")
                            .tag(obligation.id as UUID?)
                    }
                }
                .pickerStyle(.menu)

                Button {
                    checkSelectedObligation()
                } label: {
                    Label("Check Selected", systemImage: "checkmark.circle")
                }
                .disabled(selectedObligationId == nil)
            }
        }
    }

    private func checkSelectedObligation() {
        guard let session = document.proofSession,
              let selectedId = selectedObligationId,
              let obligation = session.obligations.first(where: { $0.id == selectedId }) else {
            return
        }
        session.checkStep(
            line: obligation.location.startLine,
            column: obligation.location.startColumn
        )
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

// MARK: - Preview

#if DEBUG
struct InspectorViews_Previews: PreviewProvider {
    static var previews: some View {
        EnhancedInspectorSidebar(document: TLADocument())
            .frame(width: 280, height: 600)
    }
}
#endif
