import Foundation

// MARK: - DOT Generator

/// Generates Graphviz DOT format from error traces
struct DOTGenerator {

    // MARK: - Configuration

    struct Configuration {
        var direction: Direction = .topToBottom
        var showVariables: Bool = true
        var maxVariablesPerNode: Int = 5
        var nodeShape: NodeShape = .box
        var fontSize: Int = 12

        enum Direction: String, CaseIterable {
            case topToBottom = "TB"
            case leftToRight = "LR"
            case bottomToTop = "BT"
            case rightToLeft = "RL"

            var displayName: String {
                switch self {
                case .topToBottom: return "Top to Bottom"
                case .leftToRight: return "Left to Right"
                case .bottomToTop: return "Bottom to Top"
                case .rightToLeft: return "Right to Left"
                }
            }
        }

        enum NodeShape: String {
            case box
            case ellipse
            case rectangle
            case roundedBox = "box, style=rounded"
        }
    }

    let configuration: Configuration

    init(configuration: Configuration = Configuration()) {
        self.configuration = configuration
    }

    // MARK: - Generation

    /// Generate DOT format string from an error trace
    func generate(from trace: ErrorTrace) -> String {
        var lines: [String] = []

        // Graph header
        lines.append("digraph ErrorTrace {")
        lines.append("  // Graph settings")
        lines.append("  rankdir=\(configuration.direction.rawValue);")
        lines.append("  node [fontname=\"Helvetica\", fontsize=\(configuration.fontSize)];")
        lines.append("  edge [fontname=\"Helvetica\", fontsize=\(configuration.fontSize - 2)];")
        lines.append("")

        // Generate nodes
        lines.append("  // States")
        for (index, state) in trace.states.enumerated() {
            let nodeStyle = nodeStyle(for: state, at: index, in: trace)
            let label = nodeLabel(for: state, at: index, in: trace)
            lines.append("  \(nodeId(for: index)) [\(nodeStyle), label=\(label)];")
        }
        lines.append("")

        // Generate edges
        lines.append("  // Transitions")
        if trace.states.count > 1 {
            for index in 0..<(trace.states.count - 1) {
                let nextState = trace.states[index + 1]
                let actionLabel = nextState.action ?? ""
                let escapedLabel = escapeForDOT(actionLabel)
                lines.append("  \(nodeId(for: index)) -> \(nodeId(for: index + 1)) [label=\"\(escapedLabel)\"];")
            }
        }

        // Handle liveness loop (back-edge)
        if let loopStart = trace.loopStart,
           !trace.states.isEmpty,
           loopStart < trace.states.count {
            let lastIndex = trace.states.count - 1
            lines.append("")
            lines.append("  // Liveness loop back-edge")
            lines.append("  \(nodeId(for: lastIndex)) -> \(nodeId(for: loopStart)) [style=dashed, color=red, constraint=false, label=\"loop\"];")
        }

        lines.append("}")

        return lines.joined(separator: "\n")
    }

    // MARK: - Node Helpers

    private func nodeId(for index: Int) -> String {
        return "state\(index)"
    }

    private func nodeStyle(for state: TraceState, at index: Int, in trace: ErrorTrace) -> String {
        var styles: [String] = []

        // Determine node color based on state type
        if index == 0 {
            // Initial state - green
            styles.append("fillcolor=\"#d4edda\"")
            styles.append("style=filled")
        } else if index == trace.states.count - 1 && trace.loopStart == nil {
            // Final error state (non-liveness) - red
            styles.append("fillcolor=\"#f8d7da\"")
            styles.append("style=filled")
        } else if trace.loopStart == index {
            // Loop start state (liveness) - orange
            styles.append("fillcolor=\"#fff3cd\"")
            styles.append("style=filled")
        } else if index == trace.states.count - 1 && trace.loopStart != nil {
            // Last state before loop back - red
            styles.append("fillcolor=\"#f8d7da\"")
            styles.append("style=filled")
        }

        // Node shape
        styles.append("shape=\(configuration.nodeShape.rawValue)")

        return styles.joined(separator: ", ")
    }

    private func nodeLabel(for state: TraceState, at index: Int, in trace: ErrorTrace) -> String {
        var labelLines: [String] = []

        // State header
        let header: String
        if index == 0 {
            header = "Initial State"
        } else if index == trace.states.count - 1 && trace.loopStart == nil {
            header = "State \(index) (Error)"
        } else if trace.loopStart == index {
            header = "State \(index) (Loop Start)"
        } else {
            header = "State \(index)"
        }
        labelLines.append(header)

        // Variables (if enabled)
        if configuration.showVariables && !state.variables.isEmpty {
            labelLines.append("─────────")

            let sortedVars = state.variables.keys.sorted()
            let varsToShow = sortedVars.prefix(configuration.maxVariablesPerNode)
            let previousState: TraceState? = index > 0 ? trace.states[index - 1] : nil
            let changedVars = state.changedVariables(from: previousState)

            for varName in varsToShow {
                if let value = state.variables[varName] {
                    let displayValue = truncateValue(value.displayString, maxLength: 30)
                    let prefix = changedVars.contains(varName) ? "• " : "  "
                    labelLines.append("\(prefix)\(varName) = \(displayValue)")
                }
            }

            if sortedVars.count > configuration.maxVariablesPerNode {
                let remaining = sortedVars.count - configuration.maxVariablesPerNode
                labelLines.append("  ... +\(remaining) more")
            }
        }

        let escapedLabel = labelLines.map { escapeForDOT($0) }.joined(separator: "\\n")
        return "\"\(escapedLabel)\""
    }

    // MARK: - String Helpers

    private func escapeForDOT(_ string: String) -> String {
        return string
            .replacingOccurrences(of: "\\", with: "\\\\")
            .replacingOccurrences(of: "\"", with: "\\\"")
            .replacingOccurrences(of: "\n", with: "\\n")
            .replacingOccurrences(of: "\r", with: "")
            .replacingOccurrences(of: "<", with: "\\<")
            .replacingOccurrences(of: ">", with: "\\>")
            .replacingOccurrences(of: "{", with: "\\{")
            .replacingOccurrences(of: "}", with: "\\}")
            .replacingOccurrences(of: "|", with: "\\|")
    }

    private func truncateValue(_ value: String, maxLength: Int) -> String {
        if value.count <= maxLength {
            return value
        }
        return String(value.prefix(maxLength - 3)) + "..."
    }
}

// MARK: - Export Format

enum GraphExportFormat: String, CaseIterable {
    case svg
    case png
    case pdf
    case dot

    var fileExtension: String {
        return rawValue
    }

    var displayName: String {
        switch self {
        case .svg: return "SVG (Vector)"
        case .png: return "PNG (Image)"
        case .pdf: return "PDF (Document)"
        case .dot: return "DOT (Source)"
        }
    }

    var graphvizFormat: String {
        return rawValue
    }
}
