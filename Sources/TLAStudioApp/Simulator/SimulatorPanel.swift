import SwiftUI

// MARK: - Simulator Panel

/// Bottom-panel tab hosting the interactive simulator: manually step through
/// the spec's actions, inspect the current state, and evaluate expressions —
/// a hands-on way to explore (and teach) a spec's state space.
struct SimulatorPanelContent: View {
    @ObservedObject var document: TLADocument

    var body: some View {
        if let session = document.simulationSession {
            SimulatorSessionView(session: session, document: document)
        } else {
            VStack(spacing: 10) {
                Image(systemName: "figure.walk")
                    .font(.title)
                    .foregroundColor(.secondary)
                Text("Interactive Simulator")
                    .font(.headline)
                Text("Step through the spec by hand: pick an initial state, choose an enabled action, watch variables change, and evaluate expressions in the current state.")
                    .font(.callout)
                    .foregroundColor(.secondary)
                    .multilineTextAlignment(.center)
                    .frame(maxWidth: 440)
                if let error = document.simulationError {
                    Text(error)
                        .font(.callout)
                        .foregroundColor(.red)
                        .multilineTextAlignment(.center)
                        .frame(maxWidth: 440)
                }
                Button("Start Simulation") {
                    document.startSimulation()
                }
                .keyboardShortcut(.defaultAction)
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }
}

// MARK: - Session View

struct SimulatorSessionView: View {
    @ObservedObject var session: SimulationSession
    let document: TLADocument

    @State private var expressionText = ""

    var body: some View {
        VStack(spacing: 0) {
            toolbar
            Divider()
            content
        }
    }

    // MARK: Toolbar

    private var toolbar: some View {
        HStack(spacing: 8) {
            Button {
                document.startSimulation()
            } label: {
                Label("Restart", systemImage: "arrow.counterclockwise")
            }
            .help("Restart the simulation from the current spec and model config")

            Button {
                session.stepBack()
            } label: {
                Label("Back", systemImage: "chevron.left")
            }
            .disabled(session.trace.count < 2)
            .help("Step back to the previous state")

            Button {
                session.reset()
            } label: {
                Label("Reset", systemImage: "backward.end")
            }
            .disabled(session.trace.count < 2 && session.phase != .choosingInitialState)
            .help("Return to the initial state")

            Spacer()

            switch session.phase {
            case .loadingInitialStates:
                ProgressView().controlSize(.small)
                Text("Computing initial states…").foregroundColor(.secondary)
            case .working:
                ProgressView().controlSize(.small)
                Text("Running TLC…").foregroundColor(.secondary)
            case .ready:
                Text("Step \(max(0, session.trace.count - 1))")
                    .foregroundColor(.secondary)
                    .monospacedDigit()
            case .choosingInitialState, .failed:
                EmptyView()
            }
        }
        .buttonStyle(.borderless)
        .controlSize(.small)
        .padding(.horizontal, 8)
        .padding(.vertical, 4)
        .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: Content

    @ViewBuilder
    private var content: some View {
        switch session.phase {
        case .loadingInitialStates:
            placeholder("Computing initial states…", spinning: true)
        case .failed(let message):
            VStack(spacing: 8) {
                Image(systemName: "exclamationmark.triangle")
                    .foregroundColor(.orange)
                Text(message)
                    .font(.system(.callout, design: .monospaced))
                    .textSelection(.enabled)
                    .frame(maxWidth: 520)
                Button("Retry") { session.start() }
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
        case .choosingInitialState:
            initialStatePicker
        case .ready, .working:
            explorer
        }
    }

    private func placeholder(_ text: String, spinning: Bool = false) -> some View {
        VStack(spacing: 8) {
            if spinning { ProgressView() }
            Text(text).foregroundColor(.secondary)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private var initialStatePicker: some View {
        VStack(alignment: .leading, spacing: 0) {
            Text("\(session.initialStates.count) initial states — choose one to begin")
                .font(.callout)
                .foregroundColor(.secondary)
                .padding(8)
            Divider()
            List(Array(session.initialStates.enumerated()), id: \.offset) { _, state in
                Button {
                    session.chooseInitialState(state)
                } label: {
                    Text(summary(of: state))
                        .font(.system(.body, design: .monospaced))
                        .lineLimit(1)
                        .truncationMode(.tail)
                }
                .buttonStyle(.plain)
            }
        }
    }

    private var explorer: some View {
        VStack(spacing: 0) {
            HSplitView {
                traceColumn
                    .frame(minWidth: 160, idealWidth: 220)
                stateColumn
                    .frame(minWidth: 220, idealWidth: 320)
                successorColumn
                    .frame(minWidth: 220, idealWidth: 320)
            }
            Divider()
            evaluationBar
        }
    }

    // MARK: Columns

    private var traceColumn: some View {
        VStack(alignment: .leading, spacing: 0) {
            columnHeader("Trace")
            List(session.trace) { entry in
                HStack(spacing: 6) {
                    Text("\(stepNumber(of: entry))")
                        .foregroundColor(.secondary)
                        .monospacedDigit()
                        .frame(width: 24, alignment: .trailing)
                    Text(entry.actionLabel ?? "Initial state")
                        .font(.system(.body, design: .monospaced))
                        .lineLimit(1)
                        .truncationMode(.tail)
                }
                .listRowBackground(
                    entry.id == session.trace.last?.id
                        ? Color.accentColor.opacity(0.15)
                        : Color.clear
                )
            }
        }
    }

    private func stepNumber(of entry: SimulationSession.TraceEntry) -> Int {
        session.trace.firstIndex(of: entry) ?? 0
    }

    private var stateColumn: some View {
        VStack(alignment: .leading, spacing: 0) {
            columnHeader("Current State")
            if let state = session.currentState {
                let changed = session.lastChangedVariables
                List(state.variables) { variable in
                    HStack(alignment: .firstTextBaseline, spacing: 6) {
                        Text(variable.name)
                            .font(.system(.body, design: .monospaced))
                            .fontWeight(changed.contains(variable.name) ? .bold : .regular)
                            .foregroundColor(changed.contains(variable.name) ? .orange : .primary)
                        Text("=").foregroundColor(.secondary)
                        Text(variable.rawValue)
                            .font(.system(.body, design: .monospaced))
                            .textSelection(.enabled)
                    }
                }
            } else {
                placeholder("No state selected")
            }
        }
    }

    private var successorColumn: some View {
        VStack(alignment: .leading, spacing: 0) {
            columnHeader("Enabled Actions")
            if session.phase == .working {
                placeholder("Running TLC…", spinning: true)
            } else if session.successors.isEmpty {
                placeholder("No enabled actions — deadlock")
            } else {
                if session.successorsTruncated {
                    Text("Successor list truncated")
                        .font(.caption)
                        .foregroundColor(.orange)
                        .padding(.horizontal, 8)
                        .padding(.top, 4)
                }
                List(session.successors) { successor in
                    Button {
                        session.step(successor)
                    } label: {
                        VStack(alignment: .leading, spacing: 2) {
                            HStack(spacing: 4) {
                                Image(systemName: "arrow.right.circle")
                                    .foregroundColor(.accentColor)
                                Text(successor.actionLabel)
                                    .font(.system(.body, design: .monospaced))
                                    .lineLimit(1)
                                    .truncationMode(.tail)
                            }
                            Text(diffSummary(to: successor.state))
                                .font(.system(.caption, design: .monospaced))
                                .foregroundColor(.secondary)
                                .lineLimit(1)
                                .truncationMode(.tail)
                        }
                        .contentShape(Rectangle())
                    }
                    .buttonStyle(.plain)
                }
            }
        }
    }

    private func columnHeader(_ title: String) -> some View {
        Text(title)
            .font(.caption)
            .fontWeight(.semibold)
            .foregroundColor(.secondary)
            .padding(.horizontal, 8)
            .padding(.vertical, 4)
            .frame(maxWidth: .infinity, alignment: .leading)
            .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: Evaluation

    private var evaluationBar: some View {
        VStack(spacing: 0) {
            HStack(spacing: 6) {
                Image(systemName: "function")
                    .foregroundColor(.secondary)
                TextField("Evaluate expression in current state (e.g. Cardinality(s) or guard of an action)", text: $expressionText)
                    .textFieldStyle(.plain)
                    .font(.system(.body, design: .monospaced))
                    .onSubmit(submitExpression)
                Button("Evaluate", action: submitExpression)
                    .disabled(expressionText.trimmingCharacters(in: .whitespaces).isEmpty
                              || session.currentState == nil)
            }
            .padding(.horizontal, 8)
            .padding(.vertical, 6)

            if !session.evaluations.isEmpty {
                Divider()
                ScrollView {
                    VStack(alignment: .leading, spacing: 2) {
                        ForEach(session.evaluations) { entry in
                            HStack(alignment: .firstTextBaseline, spacing: 6) {
                                Text("S\(entry.stateIndex)")
                                    .font(.caption)
                                    .foregroundColor(.secondary)
                                    .frame(width: 28, alignment: .trailing)
                                Text(entry.expression)
                                    .font(.system(.callout, design: .monospaced))
                                    .lineLimit(1)
                                    .truncationMode(.tail)
                                Text("=").foregroundColor(.secondary)
                                switch entry.result {
                                case .success(let value):
                                    Text(value)
                                        .font(.system(.callout, design: .monospaced))
                                        .textSelection(.enabled)
                                case .failure(let error):
                                    Text(error.localizedDescription)
                                        .font(.system(.caption, design: .monospaced))
                                        .foregroundColor(.red)
                                        .lineLimit(2)
                                        .textSelection(.enabled)
                                }
                                Spacer()
                            }
                        }
                    }
                    .padding(.horizontal, 8)
                    .padding(.vertical, 4)
                }
                .frame(maxHeight: 90)
            }
        }
    }

    private func submitExpression() {
        let expression = expressionText.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !expression.isEmpty else { return }
        session.evaluate(expression)
        expressionText = ""
    }

    // MARK: Formatting

    private func summary(of state: SimState) -> String {
        state.variables
            .map { "\($0.name) = \($0.rawValue)" }
            .joined(separator: "  ·  ")
    }

    private func diffSummary(to state: SimState) -> String {
        guard let current = session.currentState else { return summary(of: state) }
        let changed = state.changedVariableNames(from: current)
        guard !changed.isEmpty else { return "(no variable changes)" }
        return state.variables
            .filter { changed.contains($0.name) }
            .map { "\($0.name) = \($0.rawValue)" }
            .joined(separator: "  ·  ")
    }
}
