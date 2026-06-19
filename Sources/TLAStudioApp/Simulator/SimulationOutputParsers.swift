import Foundation

// MARK: - Dot Graph Parser

/// Parses TLC's `-dump dot,actionlabels` output into simulation states.
///
/// Format pinned against TLC 2.20 / tlc-native:
/// ```
/// strict digraph DiskGraph {
/// 8007788729609353837 [label="/\\ tlaStudioSimDepth = 0\n/\\ x = 1\n/\\ y = <<0>>",style = filled]
/// 8007788729609353837 -> -2230938646893362569 [label="TLAStudioSimAction1",color="black",...];
/// -2230938646893362569 [label="/\\ tlaStudioSimDepth = 1\n/\\ x = 2\n/\\ y = <<0>>",tooltip="…"];
/// ```
/// Node labels hold the full state as `/\ name = value` conjuncts joined by
/// dot-escaped `\n`; values are single-line. The auxiliary depth variable
/// classifies nodes (0 = origin, 1 = successor) and is stripped from states.
enum SimulationDotParser {

    struct ParsedGraph: Equatable {
        let origins: [SimState]
        let successors: [SimSuccessor]
        let truncated: Bool
    }

    static let maxStates = 256

    private static let nodeRegex = try! NSRegularExpression(
        pattern: #"^\s*(-?\d+)\s+\[label="((?:[^"\\]|\\.)*)""#
    )
    private static let edgeRegex = try! NSRegularExpression(
        pattern: #"^\s*(-?\d+)\s+->\s+(-?\d+)\s+\[label="((?:[^"\\]|\\.)*)""#
    )

    /// - Parameters:
    ///   - dotText: Contents of the `.dot` dump.
    ///   - actionLabels: Maps generated action operator names
    ///     (`TLAStudioSimActionN`) to user-facing labels.
    static func parse(dotText: String, actionLabels: [String: String]) -> ParsedGraph {
        var nodes: [String: (depth: Int?, state: SimState)] = [:]
        var originOrder: [String] = []
        var edges: [(from: String, to: String, label: String)] = []
        var truncated = false

        for line in dotText.components(separatedBy: "\n") {
            let range = NSRange(line.startIndex..., in: line)

            // Edge lines also start with a node id, so try edges first.
            if let match = edgeRegex.firstMatch(in: line, range: range) {
                // Bound retained edges like nodes: a huge fan-out otherwise
                // accumulates an edge list far beyond what the state cap keeps.
                guard edges.count < maxStates * 8 else {
                    truncated = true
                    continue
                }
                edges.append((
                    from: capture(match, 1, in: line),
                    to: capture(match, 2, in: line),
                    label: unescape(capture(match, 3, in: line))
                ))
                continue
            }

            if let match = nodeRegex.firstMatch(in: line, range: range) {
                let id = capture(match, 1, in: line)
                guard nodes[id] == nil else { continue }
                guard nodes.count < maxStates * 2 else {
                    truncated = true
                    continue
                }
                let (depth, state) = parseStateLabel(unescape(capture(match, 2, in: line)))
                nodes[id] = (depth, state)
                if depth == 0 {
                    originOrder.append(id)
                }
            }
        }

        var origins: [SimState] = []
        for id in originOrder {
            if origins.count >= maxStates {
                truncated = true
                break
            }
            if let node = nodes[id] {
                origins.append(node.state)
            }
        }

        var successors: [SimSuccessor] = []
        var seen = Set<String>()
        for edge in edges {
            guard let from = nodes[edge.from], from.depth == 0,
                  let to = nodes[edge.to], to.depth == 1 else { continue }
            if successors.count >= maxStates {
                truncated = true
                break
            }
            let label = actionLabels[edge.label] ?? edge.label
            let successor = SimSuccessor(actionLabel: label, state: to.state)
            if seen.insert(successor.id).inserted {
                successors.append(successor)
            }
        }

        return ParsedGraph(origins: origins, successors: successors, truncated: truncated)
    }

    /// Split an unescaped state label (`/\ a = 1\n/\ b = {2}`) into the depth
    /// value and the user-visible state.
    private static func parseStateLabel(_ label: String) -> (depth: Int?, state: SimState) {
        var depth: Int?
        var variables: [SimVariable] = []

        for rawLine in label.components(separatedBy: "\n") {
            var line = rawLine.trimmingCharacters(in: .whitespaces)
            guard !line.isEmpty else { continue }
            if line.hasPrefix("/\\ ") {
                line = String(line.dropFirst(3))
            }
            // Values are TLC-printed and single-line; the variable name is the
            // identifier before the first ` = `.
            guard let separator = line.range(of: " = ") else { continue }
            let name = String(line[..<separator.lowerBound]).trimmingCharacters(in: .whitespaces)
            let value = String(line[separator.upperBound...])
            guard name.range(of: #"^[A-Za-z_][A-Za-z0-9_]*$"#, options: .regularExpression) != nil else {
                continue
            }
            if name == SimulationModuleBuilder.depthVariable {
                depth = Int(value.trimmingCharacters(in: .whitespaces))
            } else {
                variables.append(SimVariable(name: name, rawValue: value))
            }
        }
        return (depth, SimState(variables: variables))
    }

    /// Undo graphviz label escaping: `\n` → newline, `\"` → `"`, `\\` → `\`.
    static func unescape(_ text: String) -> String {
        var result = ""
        result.reserveCapacity(text.count)
        var iterator = text.makeIterator()
        while let character = iterator.next() {
            guard character == "\\", let escaped = iterator.next() else {
                result.append(character)
                continue
            }
            switch escaped {
            case "n": result.append("\n")
            default: result.append(escaped)
            }
        }
        return result
    }

    private static func capture(_ match: NSTextCheckingResult, _ index: Int, in line: String) -> String {
        guard let range = Swift.Range(match.range(at: index), in: line) else { return "" }
        return String(line[range])
    }
}

// MARK: - Evaluation Output Parser

/// Extracts the PrintT'd value (or the TLC error) from an evaluation run.
enum SimulationEvalParser {

    /// TLC prints string values quoted, so the marker lines appear as
    /// `"TLASTUDIO_EVAL_BEGIN"` / `"TLASTUDIO_EVAL_END"`.
    static func parse(output: String) -> Result<String, SimulationError> {
        let begin = "\"\(SimulationModuleBuilder.evalBeginMarker)\""
        let end = "\"\(SimulationModuleBuilder.evalEndMarker)\""

        var valueLines: [String] = []
        var inValue = false
        var sawBegin = false

        for rawLine in output.components(separatedBy: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespaces)
            if line == begin {
                inValue = true
                sawBegin = true
                continue
            }
            if line == end {
                guard sawBegin else { continue }
                let value = valueLines.joined(separator: "\n").trimmingCharacters(in: .whitespacesAndNewlines)
                return .success(value)
            }
            if inValue {
                valueLines.append(rawLine)
            }
        }

        return .failure(.tlcFailed(SimulationTLCErrorExtractor.extract(from: output)
            ?? "TLC did not produce a value for the expression."))
    }
}

// MARK: - TLC Error Extraction

/// Pulls a readable error summary out of raw TLC output.
enum SimulationTLCErrorExtractor {

    /// Returns the first `Error: …` block (the error line plus immediate
    /// continuation lines), or nil when no error line is present.
    static func extract(from output: String) -> String? {
        var collected: [String] = []
        var inError = false

        for rawLine in output.components(separatedBy: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespaces)
            if !inError {
                if line.hasPrefix("Error:") || line == "***Parse Error***" {
                    inError = true
                    collected.append(line)
                }
                continue
            }
            // Stop at the position-stack trailer or at blank separation.
            if line.isEmpty
                || line.hasPrefix("The error occurred when TLC")
                || line.range(of: #"^\d+\. Line \d+"#, options: .regularExpression) != nil {
                break
            }
            collected.append(line)
            if collected.count >= 8 { break }
        }

        return collected.isEmpty ? nil : collected.joined(separator: "\n")
    }
}
