import SwiftUI

/// Precomputed assist data for the selected obligation (computed by the
/// embedding view, which has document context).
struct ProofObligationAssist {
    var byDefSuggestions: [String] = []
    var byDefInsertion: ProofAssist.ByDefInsertion?
    var invariantCandidates: [String] = []
}

/// The failed-proof workbench: shows the actual goal TLAPM generated for the
/// selected obligation, plus retry / BY DEF / model-check actions.
struct ObligationInspectorView: View {
    let obligation: ProofObligation
    @ObservedObject var session: ProofSession
    var assist: ProofObligationAssist = ProofObligationAssist()
    var onApplyByDef: ((ProofAssist.ByDefInsertion) -> Void)?
    var onModelCheckInvariant: ((String) -> Void)?
    var onJumpToSource: ((ProofSourceLocation) -> Void)?

    private var needsAttention: Bool {
        obligation.status == .failed || obligation.status == .timeout
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            header

            if let error = obligation.errorMessage, !error.isEmpty {
                Text(error)
                    .font(.system(.caption, design: .monospaced))
                    .foregroundColor(.red)
                    .textSelection(.enabled)
                    .fixedSize(horizontal: false, vertical: true)
            }

            if !obligation.obligationText.isEmpty {
                goalView
            }

            if needsAttention {
                retryActions
            }

            if needsAttention, !assist.byDefSuggestions.isEmpty {
                byDefSection
            }

            if needsAttention, !assist.invariantCandidates.isEmpty, onModelCheckInvariant != nil {
                modelCheckSection
            }
        }
        .padding(10)
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    // MARK: - Sections

    private var header: some View {
        HStack(spacing: 6) {
            statusIcon
            Text(obligation.kind.displayName)
                .font(.headline)
            Text("Ln \(obligation.location.startLine)")
                .font(.caption)
                .foregroundColor(.secondary)
            if let backend = obligation.backend {
                BackendBadge(backend: backend)
            }
            if let duration = obligation.duration {
                Text(String(format: "%.1fs", duration))
                    .font(.caption)
                    .foregroundColor(.secondary)
            }
            Spacer()
            Button {
                onJumpToSource?(obligation.location)
            } label: {
                Image(systemName: "arrow.right.circle")
            }
            .buttonStyle(.borderless)
            .help("Jump to source")
            Button {
                NotificationCenter.default.post(name: .showOutputPanel, object: nil)
            } label: {
                Image(systemName: "terminal")
            }
            .buttonStyle(.borderless)
            .help("Show raw TLAPM output")
        }
    }

    /// The actual sequent TLAPM is trying to prove — previously parsed but
    /// never shown anywhere.
    private var goalView: some View {
        VStack(alignment: .leading, spacing: 2) {
            Text("Goal")
                .font(.caption2)
                .foregroundColor(.secondary)
            ScrollView {
                Text(obligation.obligationText)
                    .font(.system(.caption, design: .monospaced))
                    .textSelection(.enabled)
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .padding(6)
            }
            .frame(maxHeight: 130)
            .background(Color(NSColor.textBackgroundColor))
            .cornerRadius(4)
        }
    }

    private var retryActions: some View {
        HStack(spacing: 8) {
            Button("Retry") {
                session.retryObligation(obligation)
            }
            Button("Retry 2× timeout") {
                session.retryObligation(obligation, timeoutMultiplier: 2)
            }
            Menu("Retry with…") {
                ForEach(retryBackends, id: \.self) { backend in
                    Button(backend.displayName) {
                        session.retryObligation(obligation, backend: backend, timeoutMultiplier: 2)
                    }
                }
            }
            .frame(maxWidth: 130)
        }
        .controlSize(.small)
        .disabled(session.isRunning)
    }

    private var retryBackends: [ProverBackend] {
        [.zenon, .z3, .cvc5, .isabelle, .spass, .ls4]
    }

    private var byDefSection: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text("Definitions referenced by the goal but not expanded:")
                .font(.caption2)
                .foregroundColor(.secondary)
            HStack(spacing: 6) {
                Text(assist.byDefSuggestions.joined(separator: ", "))
                    .font(.system(.caption, design: .monospaced))
                    .textSelection(.enabled)
                    .lineLimit(2)
                Spacer()
                if let insertion = assist.byDefInsertion, let onApplyByDef {
                    Button("Add BY DEF") {
                        onApplyByDef(insertion)
                    }
                    .controlSize(.small)
                    .disabled(session.isRunning)
                    .help("Append these definitions to the step's BY clause")
                } else {
                    Text("(no BY leaf found — add manually)")
                        .font(.caption2)
                        .foregroundColor(.secondary)
                }
            }
        }
    }

    private var modelCheckSection: some View {
        HStack(spacing: 6) {
            Menu("Model-check…") {
                ForEach(assist.invariantCandidates, id: \.self) { name in
                    Button(name) {
                        onModelCheckInvariant?(name)
                    }
                }
            }
            .frame(maxWidth: 150)
            .controlSize(.small)
            Text("A TLC counterexample means the property is false; a clean run means the proof needs work.")
                .font(.caption2)
                .foregroundColor(.secondary)
                .fixedSize(horizontal: false, vertical: true)
        }
    }

    private var statusIcon: some View {
        Image(systemName: obligation.status.iconName)
            .foregroundColor(obligation.status.color)
    }
}
