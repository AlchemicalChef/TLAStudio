import SwiftUI

// MARK: - Error Trace View

/// Displays a TLC counterexample/error trace
struct ErrorTraceView: View {
    let trace: ErrorTrace
    @State private var selectedStateId: Int = 0
    @State private var showDiff = true
    @State private var showGraphSheet = false
    @State private var explorerQueries: [TraceExplorerQuery] = []
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
                    Spacer()
                    Text("\(trace.states.count) states")
                        .font(.caption)
                        .foregroundColor(.secondary)
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
                ForEach(Array(trace.states.enumerated()), id: \.element.id) { index, state in
                    StateRowView(
                        state: state,
                        isSelected: state.id == selectedStateId,
                        isLoopStart: trace.loopStart == state.id,
                        changedVars: showDiff ? state.changedVariables(from: previousState(at: index)) : []
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
                    VStack(alignment: .leading, spacing: 4) {
                        HStack(spacing: 8) {
                            Text(state.displayName)
                                .font(.headline)

                            if trace.loopStart == state.id {
                                TraceBadge(title: "Loop Start", color: .orange)
                            }

                            if showDiff && !changedVariables.isEmpty {
                                TraceBadge(title: "\(changedVariables.count) changed", color: .orange)
                            }
                        }

                        HStack(spacing: 8) {
                            Text("State \(state.id + 1) of \(trace.states.count)")
                                .font(.caption)
                                .foregroundColor(.secondary)

                            if let location = state.location {
                                Text(location.displayString)
                                    .font(.caption)
                                    .foregroundColor(.secondary)
                            }
                        }
                    }

                    Spacer()

                    if let location = state.location {
                        Button {
                            onJumpToSource?(location)
                        } label: {
                            Label("Jump to Source", systemImage: "arrow.turn.down.right")
                        }
                        .buttonStyle(.bordered)
                    }
                }
                .padding()
                .background(Color(NSColor.controlBackgroundColor))

                Divider()

                // Variables
                ScrollView {
                    LazyVStack(alignment: .leading, spacing: 8) {
                        TraceExplorerSection(
                            state: state,
                            previousState: previousState(for: state.id),
                            queries: $explorerQueries
                        )

                        Divider()
                            .padding(.vertical, 4)

                        ForEach(state.sortedVariableNames, id: \.self) { name in
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

    var selectedStateIndex: Int? {
        if trace.states.indices.contains(selectedStateId), trace.states[selectedStateId].id == selectedStateId {
            return selectedStateId
        }
        return trace.states.firstIndex { $0.id == selectedStateId }
    }

    var selectedState: TraceState? {
        guard let selectedStateIndex else { return nil }
        return trace.states[selectedStateIndex]
    }

    var changedVariables: Set<String> {
        guard let selectedStateIndex else { return [] }
        let state = trace.states[selectedStateIndex]
        return state.changedVariables(from: previousState(at: selectedStateIndex))
    }

    func previousState(for id: Int) -> TraceState? {
        guard let index = stateIndex(for: id) else { return nil }
        return previousState(at: index)
    }

    func previousState(at index: Int) -> TraceState? {
        guard index > 0, trace.states.indices.contains(index - 1) else { return nil }
        return trace.states[index - 1]
    }

    func stateIndex(for id: Int) -> Int? {
        if trace.states.indices.contains(id), trace.states[id].id == id {
            return id
        }
        return trace.states.firstIndex { $0.id == id }
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

private struct TraceExplorerQuery: Identifiable, Equatable {
    let id: UUID
    var expression: String

    init(id: UUID = UUID(), expression: String = "") {
        self.id = id
        self.expression = expression
    }
}

private struct TraceExplorerResult {
    let displayString: String
    let isError: Bool
    let didChange: Bool
}

private struct TraceExplorerSection: View {
    let state: TraceState
    let previousState: TraceState?
    @Binding var queries: [TraceExplorerQuery]

    var body: some View {
        GroupBox {
            VStack(alignment: .leading, spacing: 12) {
                HStack {
                    Text("Evaluate expressions against the selected state.")
                        .font(.caption)
                        .foregroundColor(.secondary)

                    Spacer()

                    if !queries.isEmpty {
                        Button("Clear") {
                            queries.removeAll()
                        }
                        .buttonStyle(.borderless)
                    }

                    Button {
                        queries.append(TraceExplorerQuery())
                    } label: {
                        Label("Add Expression", systemImage: "plus")
                    }
                    .buttonStyle(.bordered)
                    .help("Add trace explorer expression")
                }

                if !sampleExpressions.isEmpty {
                    VStack(alignment: .leading, spacing: 6) {
                        Text("Examples")
                            .font(.caption.weight(.medium))
                            .foregroundColor(.secondary)

                        HStack(spacing: 8) {
                            ForEach(sampleExpressions, id: \.self) { example in
                                Button(example) {
                                    queries.append(TraceExplorerQuery(expression: example))
                                }
                                .buttonStyle(.borderless)
                                .font(.system(.caption, design: .monospaced))
                                .padding(.horizontal, 8)
                                .padding(.vertical, 4)
                                .background(Color.accentColor.opacity(0.08))
                                .clipShape(Capsule())
                            }
                        }
                    }
                }

                if queries.isEmpty {
                    Text("Add one or more expressions to inspect derived values, lengths, and state-local formulas while you step through the trace.")
                        .font(.callout)
                        .foregroundColor(.secondary)
                } else {
                    ForEach(Array($queries.enumerated()), id: \.element.id) { index, $query in
                        VStack(alignment: .leading, spacing: 8) {
                            HStack(alignment: .firstTextBaseline, spacing: 8) {
                                Text("\(index + 1).")
                                    .font(.caption.weight(.semibold))
                                    .foregroundColor(.secondary)
                                    .frame(width: 18, alignment: .leading)

                                TextField("Expression", text: $query.expression)
                                    .textFieldStyle(.roundedBorder)
                                    .font(.system(.body, design: .monospaced))

                                Button(role: .destructive) {
                                    removeQuery(id: query.id)
                                } label: {
                                    Image(systemName: "minus.circle.fill")
                                        .foregroundColor(.red)
                                }
                                .buttonStyle(.plain)
                                .help("Remove expression")
                            }

                            if let result = evaluate(query.expression) {
                                HStack(alignment: .top, spacing: 8) {
                                    Image(systemName: result.isError ? "exclamationmark.triangle.fill" : "equal.circle.fill")
                                        .foregroundColor(result.isError ? .red : .secondary)
                                        .font(.caption)
                                        .frame(width: 14, alignment: .center)

                                    Text(result.displayString)
                                        .font(.system(.callout, design: .monospaced))
                                        .foregroundColor(result.isError ? .red : .secondary)
                                        .textSelection(.enabled)

                                    if result.didChange {
                                        TraceBadge(title: "Changed", color: .orange)
                                    }
                                }
                            }
                        }
                        .padding(10)
                        .frame(maxWidth: .infinity, alignment: .leading)
                        .background(Color(NSColor.controlBackgroundColor))
                        .clipShape(RoundedRectangle(cornerRadius: 8))
                    }
                }
            }
        } label: {
            Label("Trace Explorer", systemImage: "function")
        }
    }

    private var sampleExpressions: [String] {
        var examples: [String] = []

        func appendIfNeeded(_ example: String?) {
            guard let example, !examples.contains(example) else { return }
            examples.append(example)
        }

        if let firstVariable = state.sortedVariableNames.first {
            appendIfNeeded(firstVariable)
        }

        if let lengthCandidate = state.sortedVariableNames.first(where: { candidate in
            guard let value = state.variables[candidate] else { return false }
            switch value {
            case .sequence, .tuple, .string, .set:
                return true
            default:
                return false
            }
        }) {
            appendIfNeeded("Len(\(lengthCandidate))")
        }

        if let domainCandidate = state.sortedVariableNames.first(where: { candidate in
            guard let value = state.variables[candidate] else { return false }
            switch value {
            case .record, .function, .sequence, .tuple:
                return true
            default:
                return false
            }
        }) {
            appendIfNeeded(domainExample(for: domainCandidate))
        }

        if let fieldCandidate = state.sortedVariableNames.first(where: { candidate in
            guard case .record(let fields)? = state.variables[candidate] else { return false }
            return !fields.isEmpty
        }) {
            appendIfNeeded(recordFieldExample(for: fieldCandidate))
        }

        return Array(examples.prefix(3))
    }

    private func evaluate(_ expression: String) -> TraceExplorerResult? {
        let trimmed = expression.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return nil }

        do {
            let value = try TraceExplorerExpressionEngine.evaluate(trimmed, with: state.variables)
            let previousValue = try previousState.map {
                try TraceExplorerExpressionEngine.evaluate(trimmed, with: $0.variables)
            }

            return TraceExplorerResult(
                displayString: value.displayString,
                isError: false,
                didChange: previousValue.map { $0 != value } ?? false
            )
        } catch {
            return TraceExplorerResult(
                displayString: error.localizedDescription,
                isError: true,
                didChange: false
            )
        }
    }

    private func removeQuery(id: UUID) {
        queries.removeAll { $0.id == id }
    }

    private func domainExample(for candidate: String) -> String {
        guard let value = state.variables[candidate] else {
            return "DOMAIN \(candidate)"
        }

        switch value {
        case .sequence, .tuple:
            return "\(candidate)[1]"
        default:
            return "DOMAIN \(candidate)"
        }
    }

    private func recordFieldExample(for candidate: String) -> String? {
        guard case .record(let fields)? = state.variables[candidate],
              let firstField = fields.keys.sorted().first else {
            return nil
        }

        if firstField.range(of: #"^[A-Za-z_][A-Za-z0-9_]*$"#, options: .regularExpression) != nil {
            return "\(candidate).\(firstField)"
        }

        return "\(candidate)[\"\(firstField)\"]"
    }
}

private struct TraceBadge: View {
    let title: String
    let color: Color

    var body: some View {
        Text(title)
            .font(.caption2.weight(.semibold))
            .padding(.horizontal, 8)
            .padding(.vertical, 3)
            .foregroundColor(color)
            .background(color.opacity(0.12))
            .clipShape(Capsule())
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
