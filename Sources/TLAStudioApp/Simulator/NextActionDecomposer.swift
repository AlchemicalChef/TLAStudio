import Foundation

/// Splits the body of a next-state definition (`Next == A \/ B \/ …`) into its
/// top-level disjuncts so the simulator can attribute each successor state to a
/// named action.
///
/// This is a *textual* decomposition, deliberately conservative: it only splits
/// when the top-level structure is recognizably a disjunction, and otherwise
/// reports "no decomposition" so the caller falls back to treating Next as one
/// action. Correctness backstop: disjunction is associative, so re-joining the
/// pieces with `\/` in the generated module preserves semantics for any split
/// this lexer performs; a syntactically bad split fails TLC's parser, which the
/// runner detects and retries un-decomposed.
///
/// Split rules (tokens are scanned outside strings/comments at bracket depth 0):
/// - No top-level `\/` → no decomposition.
/// - Single-line body → split at every top-level `\/` (TLA+ precedence: `/\`
///   binds tighter, so the pieces are exactly the disjuncts).
/// - Multi-line body → split only at top-level `\/` tokens in the *leftmost*
///   column occupied by a `\/`; if any top-level `/\` sits left of that column,
///   the top level is a conjunction (`/\`-bulleted list containing nested
///   `\/`-bullets) and decomposition is refused.
enum NextActionDecomposer {

    private struct TopLevelToken {
        let isDisjunction: Bool   // `\/` vs `/\`
        let index: String.Index   // start of token
        let endIndex: String.Index
        let line: Int
        let column: Int
    }

    static func decompose(nextBody body: String, bodyStartColumn: Int = 0) -> [SimActionDefinition]? {
        let tokens = topLevelJunctionTokens(in: body)
        let disjunctions = tokens.filter(\.isDisjunction)
        guard !disjunctions.isEmpty else { return nil }

        let isSingleLine = !body.trimmingCharacters(in: .whitespacesAndNewlines).contains("\n")

        let splitPoints: [TopLevelToken]
        if isSingleLine {
            splitPoints = disjunctions
        } else {
            let minColumn = disjunctions.map(\.column).min() ?? 0
            // A `/\` left of (or at) the leftmost `\/` means the bulleted top
            // level is a conjunction — refuse to split.
            if tokens.contains(where: { !$0.isDisjunction && $0.column <= minColumn }) {
                return nil
            }
            splitPoints = disjunctions.filter { $0.column == minColumn }
        }
        guard !splitPoints.isEmpty else { return nil }

        // Each piece keeps its first line's *original* column (restored as a
        // space prefix) so the whole block can be shifted uniformly — TLA+
        // junction lists align by absolute column, so only uniform shifts of a
        // block are meaning-preserving.
        var pieces: [(text: String, firstLineColumn: Int)] = []
        var start = body.startIndex
        var column = bodyStartColumn
        for token in splitPoints {
            pieces.append((String(body[start..<token.index]), column))
            start = token.endIndex
            column = token.column + 2   // content begins after the 2-char `\/`
        }
        pieces.append((String(body[start...]), column))

        let actions = pieces
            .map { normalize($0.text, firstLineColumn: $0.firstLineColumn) }
            .filter { !$0.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty }
            .map { SimActionDefinition(label: label(for: $0), expression: $0) }

        // A bullet-style body yields an empty leading piece (dropped above);
        // anything that collapses to fewer than 2 pieces isn't a useful split.
        return actions.count >= 2 ? actions : nil
    }

    /// Extract the definition body to the right of the first top-level `==`,
    /// along with the column (in the original text) where the body starts —
    /// needed to preserve junction-list alignment of the first body line.
    /// Returns nil if no `==` is found.
    static func body(ofDefinition text: String) -> (body: String, startColumn: Int)? {
        var scanner = TLATopLevelScanner(text: text)
        while let (character, index) = scanner.next() {
            if scanner.depth == 0, character == "=", scanner.peek() == "=" {
                // Skip both '=' and return the remainder. Guard against `===`
                // style tokens by requiring the third char not be another '='.
                let after = text.index(index, offsetBy: 2)
                if after == text.endIndex || text[after] != "=" {
                    return (String(text[after...]), scanner.column + 2)
                }
            }
        }
        return nil
    }

    // MARK: - Labels

    private static func label(for expression: String) -> String {
        let collapsed = expression
            .components(separatedBy: .whitespacesAndNewlines)
            .filter { !$0.isEmpty }
            .joined(separator: " ")
        if collapsed.count <= 48 {
            return collapsed
        }
        return collapsed.prefix(45) + "…"
    }

    /// Shift a multi-line piece so its minimum indentation is zero while
    /// preserving *relative* columns. The first line followed the `\/` token on
    /// its original line, so its true column (`firstLineColumn`) is restored as
    /// a space prefix before the uniform shift — otherwise its alignment
    /// relative to the continuation lines would be lost.
    private static func normalize(_ piece: String, firstLineColumn: Int) -> String {
        var lines = piece.components(separatedBy: "\n")
        guard !lines.isEmpty else { return "" }
        lines[0] = String(repeating: " ", count: max(0, firstLineColumn)) + lines[0]

        // Drop leading/trailing all-blank lines.
        while let first = lines.first, first.trimmingCharacters(in: .whitespaces).isEmpty {
            lines.removeFirst()
        }
        while let last = lines.last, last.trimmingCharacters(in: .whitespaces).isEmpty {
            lines.removeLast()
        }
        guard lines.count > 1 else {
            return lines.first?.trimmingCharacters(in: .whitespaces) ?? ""
        }

        let minIndent = lines
            .filter { !$0.trimmingCharacters(in: .whitespaces).isEmpty }
            .map { $0.prefix { $0 == " " }.count }
            .min() ?? 0

        return lines
            .map { line in
                line.trimmingCharacters(in: .whitespaces).isEmpty
                    ? ""
                    : String(line.dropFirst(min(minIndent, line.prefix { $0 == " " }.count)))
            }
            .joined(separator: "\n")
    }

    // MARK: - Lexing

    private static func topLevelJunctionTokens(in text: String) -> [TopLevelToken] {
        var tokens: [TopLevelToken] = []
        var scanner = TLATopLevelScanner(text: text)

        while let (character, index) = scanner.next() {
            guard scanner.depth == 0 else { continue }
            let line = scanner.line
            let column = scanner.column

            if character == "\\", scanner.peek() == "/" {
                let end = text.index(index, offsetBy: 2)
                tokens.append(TopLevelToken(
                    isDisjunction: true, index: index, endIndex: end, line: line, column: column
                ))
                scanner.skip()
            } else if character == "/", scanner.peek() == "\\" {
                let end = text.index(index, offsetBy: 2)
                tokens.append(TopLevelToken(
                    isDisjunction: false, index: index, endIndex: end, line: line, column: column
                ))
                scanner.skip()
            }
        }
        return tokens
    }

    // The TLA+-aware top-level scanner lives in Language/TLATopLevelScanner.swift
    // (shared with ProofSkeletonGenerator).
}
