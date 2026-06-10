import Foundation

/// Generates TLAPS proof skeletons for theorems ("Decompose Proof").
///
/// Recognized goal shapes:
/// - `Spec => []Inv` — the canonical invariance skeleton (init step, inductive
///   step, PTL QED), with `BY DEF` hints that often discharge immediately on
///   small specs.
/// - Top-level conjunction `A /\ B /\ …` — one step per conjunct plus a QED
///   citing them.
/// - Universal `\A x \in S : P` — a `TAKE` step plus QED.
///
/// Purely textual: input is the document content + parsed symbols, output is
/// the lines to insert after the theorem. Theorems that already have a proof
/// are refused.
enum ProofSkeletonGenerator {

    struct Insertion: Equatable {
        /// 0-based line index of the theorem's last line; skeleton lines are
        /// inserted immediately after it.
        let insertAfterLine: Int
        let lines: [String]
    }

    static func skeleton(forTheoremAtLine line: Int, content: String, symbols: [TLASymbol]) -> Insertion? {
        let lines = content.components(separatedBy: "\n")
        guard let theorem = theoremRange(atLine: line, lines: lines) else { return nil }
        guard !hasExistingProof(after: theorem.endLine, lines: lines) else { return nil }

        let goal = goalText(from: lines[theorem.startLine...theorem.endLine].joined(separator: " "))
        guard !goal.isEmpty else { return nil }

        let skeletonLines: [String]?
        if let invariance = invarianceSkeleton(goal: goal, symbols: symbols) {
            skeletonLines = invariance
        } else if let conjunction = conjunctionSkeleton(goal: goal) {
            skeletonLines = conjunction
        } else if let universal = universalSkeleton(goal: goal) {
            skeletonLines = universal
        } else {
            skeletonLines = nil
        }

        guard let skeletonLines else { return nil }
        return Insertion(insertAfterLine: theorem.endLine, lines: skeletonLines)
    }

    // MARK: - Theorem location

    private static let theoremKeyword = #"^\s*(THEOREM|LEMMA|PROPOSITION|COROLLARY)\b"#

    /// The theorem statement containing (or starting at) `line`: scan up to
    /// the THEOREM/LEMMA line, then extend through indented continuations.
    private static func theoremRange(atLine line: Int, lines: [String]) -> (startLine: Int, endLine: Int)? {
        guard !lines.isEmpty else { return nil }
        let cursorLine = min(max(0, line), lines.count - 1)

        var startLine: Int?
        for candidate in stride(from: cursorLine, through: max(0, cursorLine - 10), by: -1) {
            if lines[candidate].range(of: theoremKeyword, options: .regularExpression) != nil {
                startLine = candidate
                break
            }
        }
        guard let startLine else { return nil }

        var endLine = startLine
        var index = startLine + 1
        while index < lines.count {
            let candidate = lines[index]
            let trimmed = candidate.trimmingCharacters(in: .whitespaces)
            // Continuation: non-empty, indented, and not the start of a proof.
            guard !trimmed.isEmpty,
                  candidate.first == " " || candidate.first == "\t",
                  !isProofStart(trimmed) else { break }
            endLine = index
            index += 1
        }

        // The cursor must be within the statement we found.
        guard cursorLine >= startLine && cursorLine <= endLine else { return nil }
        return (startLine, endLine)
    }

    private static func isProofStart(_ trimmed: String) -> Bool {
        trimmed.hasPrefix("PROOF")
            || trimmed.hasPrefix("BY")
            || trimmed.hasPrefix("OBVIOUS")
            || trimmed.hasPrefix("OMITTED")
            || trimmed.hasPrefix("<")
    }

    private static func hasExistingProof(after endLine: Int, lines: [String]) -> Bool {
        var index = endLine + 1
        while index < lines.count {
            let trimmed = lines[index].trimmingCharacters(in: .whitespaces)
            if trimmed.isEmpty {
                index += 1
                continue
            }
            return isProofStart(trimmed)
        }
        return false
    }

    /// Strip the THEOREM keyword and optional `Name ==` prefix; collapse
    /// whitespace.
    private static func goalText(from statement: String) -> String {
        var text = statement
        if let keywordRange = text.range(of: theoremKeyword, options: .regularExpression) {
            text = String(text[keywordRange.upperBound...])
        }
        if let nameRange = text.range(of: #"^\s*[A-Za-z0-9_]+\s*==\s*"#, options: .regularExpression) {
            text = String(text[nameRange.upperBound...])
        }
        return text
            .components(separatedBy: .whitespacesAndNewlines)
            .filter { !$0.isEmpty }
            .joined(separator: " ")
    }

    // MARK: - Shapes

    /// `Spec => []Inv`
    private static func invarianceSkeleton(goal: String, symbols: [TLASymbol]) -> [String]? {
        let pattern = #"^([A-Za-z0-9_]+)\s*=>\s*\[\]\s*([A-Za-z0-9_]+)$"#
        guard let match = goal.range(of: pattern, options: .regularExpression),
              match == goal.startIndex..<goal.endIndex else { return nil }

        let parts = goal.components(separatedBy: "=>").map { $0.trimmingCharacters(in: .whitespaces) }
        guard parts.count == 2 else { return nil }
        let spec = parts[0]
        let invariant = parts[1].replacingOccurrences(of: "[]", with: "").trimmingCharacters(in: .whitespaces)

        // Use the spec's own vars tuple when one is defined.
        let subscriptText = symbolExists(named: "vars", in: symbols) ? "vars" : varsTuple(from: symbols)

        return [
            "PROOF",
            "<1>1. Init => \(invariant)",
            "  BY DEF Init, \(invariant)",
            "<1>2. \(invariant) /\\ [Next]_\(subscriptText) => \(invariant)'",
            "  BY DEF \(invariant), Next" + (subscriptText == "vars" ? ", vars" : ""),
            "<1>3. QED",
            "  BY <1>1, <1>2, PTL DEF \(spec)"
        ]
    }

    /// Top-level conjunction `A /\ B [/\ C …]`
    private static func conjunctionSkeleton(goal: String) -> [String]? {
        let conjuncts = splitTopLevel(goal, separator: "/\\")
        guard conjuncts.count >= 2 else { return nil }

        var lines = ["PROOF"]
        for (index, conjunct) in conjuncts.enumerated() {
            lines.append("<1>\(index + 1). \(conjunct)")
        }
        let citations = (1...conjuncts.count).map { "<1>\($0)" }.joined(separator: ", ")
        lines.append("<1>\(conjuncts.count + 1). QED")
        lines.append("  BY \(citations)")
        return lines
    }

    /// `\A x \in S : P`
    private static func universalSkeleton(goal: String) -> [String]? {
        guard goal.hasPrefix("\\A ") else { return nil }
        guard let colonIndex = topLevelColonIndex(in: goal) else { return nil }
        let bound = String(goal[goal.index(goal.startIndex, offsetBy: 3)..<colonIndex])
            .trimmingCharacters(in: .whitespaces)
        guard !bound.isEmpty else { return nil }

        return [
            "PROOF",
            "<1> TAKE \(bound)",
            "<1> QED"
        ]
    }

    // MARK: - Helpers

    private static func symbolExists(named name: String, in symbols: [TLASymbol]) -> Bool {
        symbols.firstInTree { $0.name == name } != nil
    }

    private static func varsTuple(from symbols: [TLASymbol]) -> String {
        let variables = symbols.flattened()
            .filter { $0.kind == .variable }
            .map(\.name)
        return variables.isEmpty ? "vars" : "<<\(variables.joined(separator: ", "))>>"
    }

    /// Split at a separator occurring at bracket depth 0 (outside (), [], {},
    /// << >>, strings, and comments). Uses the shared `TLATopLevelScanner`.
    private static func splitTopLevel(_ text: String, separator: String) -> [String] {
        let separatorChars = Array(separator)
        guard !separatorChars.isEmpty else { return [text] }

        var parts: [String] = []
        var scanner = TLATopLevelScanner(text: text)
        var currentStart = text.startIndex

        while let (character, index) = scanner.next() {
            guard scanner.depth == 0, character == separatorChars[0] else { continue }

            // The first separator character was just consumed; the rest must
            // follow immediately.
            let remainder = separatorChars.dropFirst()
            let matches = remainder.enumerated().allSatisfy { offset, expected in
                scanner.peek(offset: offset) == expected
            }
            guard matches else { continue }

            let part = String(text[currentStart..<index]).trimmingCharacters(in: .whitespaces)
            if !part.isEmpty { parts.append(part) }
            scanner.skip(remainder.count)
            currentStart = scanner.index
        }

        let last = String(text[currentStart...]).trimmingCharacters(in: .whitespaces)
        if !last.isEmpty { parts.append(last) }
        return parts
    }

    /// Index of the first `:` at bracket depth 0 (outside (), [], {}, << >>,
    /// strings, and comments). Uses the shared `TLATopLevelScanner`.
    private static func topLevelColonIndex(in text: String) -> String.Index? {
        var scanner = TLATopLevelScanner(text: text)
        while let (character, index) = scanner.next() {
            if scanner.depth == 0, character == ":" {
                return index
            }
        }
        return nil
    }
}
