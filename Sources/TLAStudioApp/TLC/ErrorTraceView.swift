import SwiftUI

// MARK: - Error Trace View

/// Displays a TLC counterexample/error trace
struct ErrorTraceView: View {
    let trace: ErrorTrace
    @State private var selectedStateId: Int = 0
    @State private var showDiff = true
    @State private var showGraphSheet = false
    var onJumpToSource: ((SourceLocation) -> Void)?

    var body: some View {
        HSplitView {
            // State list (left panel)
            stateListView
                .frame(minWidth: 200, maxWidth: 300)

            // State detail (right panel)
            stateDetailView
                .frame(minWidth: 300)
        }
        .toolbar {
            ToolbarItemGroup {
                Toggle("Show Changes", isOn: $showDiff)

                Button(action: previousState) {
                    Image(systemName: "chevron.up")
                }
                .disabled(selectedStateId == 0)
                .help("Previous State")

                Button(action: nextState) {
                    Image(systemName: "chevron.down")
                }
                .disabled(selectedStateId >= trace.states.count - 1)
                .help("Next State")

                Divider()

                Button {
                    showGraphSheet = true
                } label: {
                    Label("View as Graph", systemImage: "point.3.connected.trianglepath.dotted")
                }
                .help("View trace as interactive graph")
            }
        }
        .sheet(isPresented: $showGraphSheet) {
            StateGraphSheetView(trace: trace)
        }
    }

    // MARK: - State List

    var stateListView: some View {
        VStack(alignment: .leading, spacing: 0) {
            // Header
            VStack(alignment: .leading, spacing: 4) {
                HStack {
                    Image(systemName: errorIcon)
                        .foregroundColor(.red)
                    Text(trace.type.displayName)
                        .font(.headline)
                }

                Text(trace.message)
                    .font(.caption)
                    .foregroundColor(.secondary)
                    .lineLimit(2)

                if let property = trace.violatedProperty {
                    Text("Property: \(property)")
                        .font(.caption)
                        .foregroundColor(.orange)
                }
            }
            .padding()
            .background(Color.red.opacity(0.1))

            Divider()

            // State list
            List(selection: $selectedStateId) {
                ForEach(trace.states) { state in
                    StateRowView(
                        state: state,
                        isSelected: state.id == selectedStateId,
                        isLoopStart: trace.loopStart == state.id,
                        changedVars: showDiff ? state.changedVariables(from: previousState(for: state.id)) : []
                    )
                    .tag(state.id)
                }
            }
            .listStyle(.sidebar)
        }
    }

    // MARK: - State Detail

    var stateDetailView: some View {
        VStack(alignment: .leading, spacing: 0) {
            if let state = selectedState {
                // State header
                HStack {
                    Text(state.displayName)
                        .font(.headline)

                    Spacer()

                    if let location = state.location {
                        Button("Jump to Source") {
                            onJumpToSource?(location)
                        }
                        .buttonStyle(.link)
                    }
                }
                .padding()
                .background(Color(NSColor.controlBackgroundColor))

                Divider()

                // Variables
                ScrollView {
                    LazyVStack(alignment: .leading, spacing: 8) {
                        ForEach(state.variables.keys.sorted(), id: \.self) { name in
                            if let value = state.variables[name] {
                                VariableRow(
                                    name: name,
                                    value: value,
                                    isChanged: showDiff && changedVariables.contains(name)
                                )
                            }
                        }
                    }
                    .padding()
                }
            } else {
                Text("Select a state to view details")
                    .foregroundColor(.secondary)
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
            }
        }
    }

    // MARK: - Helpers

    var selectedState: TraceState? {
        trace.states.first { $0.id == selectedStateId }
    }

    var changedVariables: Set<String> {
        guard let state = selectedState else { return [] }
        return state.changedVariables(from: previousState(for: state.id))
    }

    func previousState(for id: Int) -> TraceState? {
        guard id > 0 else { return nil }
        return trace.states.first { $0.id == id - 1 }
    }

    func previousState() {
        if selectedStateId > 0 {
            selectedStateId -= 1
        }
    }

    func nextState() {
        if selectedStateId < trace.states.count - 1 {
            selectedStateId += 1
        }
    }

    var errorIcon: String {
        switch trace.type {
        case .invariantViolation:
            return "exclamationmark.triangle.fill"
        case .deadlock:
            return "hand.raised.fill"
        case .livenessViolation:
            return "clock.badge.exclamationmark.fill"
        case .assertionFailure:
            return "xmark.octagon.fill"
        case .evaluationError:
            return "exclamationmark.circle.fill"
        case .temporal:
            return "clock.fill"
        }
    }
}

// MARK: - State Row View

struct StateRowView: View {
    let state: TraceState
    let isSelected: Bool
    let isLoopStart: Bool
    let changedVars: Set<String>

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            HStack {
                if isLoopStart {
                    Image(systemName: "arrow.counterclockwise")
                        .foregroundColor(.orange)
                        .font(.caption)
                }

                Text(state.displayName)
                    .fontWeight(isSelected ? .semibold : .regular)

                Spacer()

                if !changedVars.isEmpty {
                    Text("\(changedVars.count) changed")
                        .font(.caption2)
                        .foregroundColor(.secondary)
                }
            }

            if let action = state.action, state.id > 0 {
                Text(action)
                    .font(.caption)
                    .foregroundColor(.secondary)
                    .lineLimit(1)
            }
        }
        .padding(.vertical, 4)
        .contentShape(Rectangle())
    }
}

// MARK: - Variable Row

struct VariableRow: View {
    let name: String
    let value: StateValue
    let isChanged: Bool

    @State private var isExpanded = false

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            HStack {
                if isChanged {
                    Circle()
                        .fill(Color.orange)
                        .frame(width: 6, height: 6)
                }

                Text(name)
                    .font(.system(.body, design: .monospaced))
                    .fontWeight(.medium)
                    .foregroundColor(isChanged ? .orange : .primary)

                Text("=")
                    .foregroundColor(.secondary)

                if isComplexValue {
                    Button(action: { isExpanded.toggle() }) {
                        Image(systemName: isExpanded ? "chevron.down" : "chevron.right")
                            .font(.caption)
                    }
                    .buttonStyle(.plain)
                }

                if !isComplexValue || !isExpanded {
                    Text(value.displayString)
                        .font(.system(.body, design: .monospaced))
                        .foregroundColor(.secondary)
                        .lineLimit(isExpanded ? nil : 1)
                }

                Spacer()
            }

            if isExpanded && isComplexValue {
                expandedValueView
                    .padding(.leading, 20)
            }
        }
        .padding(.vertical, 4)
        .padding(.horizontal, 8)
        .background(isChanged ? Color.orange.opacity(0.1) : Color.clear)
        .cornerRadius(4)
    }

    var isComplexValue: Bool {
        switch value {
        case .set(let s) where s.count > 3:
            return true
        case .sequence(let s) where s.count > 3:
            return true
        case .record(let r) where r.count > 2:
            return true
        case .function(let f) where f.count > 2:
            return true
        default:
            return false
        }
    }

    @ViewBuilder
    var expandedValueView: some View {
        switch value {
        case .set(let values):
            VStack(alignment: .leading, spacing: 2) {
                Text("{")
                    .font(.system(.body, design: .monospaced))
                ForEach(Array(values.map { $0.value }).indices, id: \.self) { index in
                    HStack {
                        Text("  ")
                        Text(Array(values)[index].value.displayString)
                            .font(.system(.body, design: .monospaced))
                    }
                }
                Text("}")
                    .font(.system(.body, design: .monospaced))
            }

        case .sequence(let values):
            VStack(alignment: .leading, spacing: 2) {
                Text("<<")
                    .font(.system(.body, design: .monospaced))
                ForEach(values.indices, id: \.self) { index in
                    HStack {
                        Text("  [\(index + 1)]")
                            .foregroundColor(.secondary)
                        Text(values[index].displayString)
                            .font(.system(.body, design: .monospaced))
                    }
                }
                Text(">>")
                    .font(.system(.body, design: .monospaced))
            }

        case .record(let fields):
            VStack(alignment: .leading, spacing: 2) {
                Text("[")
                    .font(.system(.body, design: .monospaced))
                ForEach(fields.keys.sorted(), id: \.self) { key in
                    HStack {
                        Text("  \(key) |-> ")
                            .font(.system(.body, design: .monospaced))
                        Text(fields[key]?.displayString ?? "")
                            .font(.system(.body, design: .monospaced))
                    }
                }
                Text("]")
                    .font(.system(.body, design: .monospaced))
            }

        case .function(let mapping):
            VStack(alignment: .leading, spacing: 2) {
                ForEach(Array(mapping.keys), id: \.self) { key in
                    HStack {
                        Text(key.value.displayString)
                            .font(.system(.body, design: .monospaced))
                        Text(":>")
                            .foregroundColor(.secondary)
                        Text(mapping[key]?.displayString ?? "")
                            .font(.system(.body, design: .monospaced))
                    }
                }
            }

        default:
            Text(value.displayString)
                .font(.system(.body, design: .monospaced))
        }
    }
}

// MARK: - Compact Error Trace

/// Compact error trace for embedding in other views
struct CompactErrorTraceView: View {
    let trace: ErrorTrace
    var onExpand: (() -> Void)?

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack {
                Image(systemName: "exclamationmark.triangle.fill")
                    .foregroundColor(.red)

                VStack(alignment: .leading) {
                    Text(trace.type.displayName)
                        .font(.headline)
                    Text("\(trace.states.count) states in trace")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                Spacer()

                if let onExpand = onExpand {
                    Button("View Trace") {
                        onExpand()
                    }
                    .buttonStyle(.link)
                }
            }

            Text(trace.message)
                .font(.callout)
                .lineLimit(2)
        }
        .padding()
        .background(Color.red.opacity(0.1))
        .cornerRadius(8)
    }
}

// MARK: - State Graph Sheet

/// Sheet view for displaying the state graph in a modal
struct StateGraphSheetView: View {
    let trace: ErrorTrace
    @Environment(\.dismiss) private var dismiss

    var body: some View {
        VStack(spacing: 0) {
            // Header
            HStack {
                Text("State Graph")
                    .font(.headline)

                Spacer()

                Button("Done") {
                    dismiss()
                }
                .keyboardShortcut(.escape)
            }
            .padding()
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Graph view
            StateGraphView(trace: trace)
        }
        .frame(minWidth: 700, minHeight: 500)
    }
}
