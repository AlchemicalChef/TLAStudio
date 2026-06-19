import Foundation

/// Pure helpers behind the failed-proof workbench: `BY DEF` suggestions for a
/// failed obligation, the textual edit that applies them, and candidate
/// invariants for the proof→TLC bridge. All inputs are values; everything is
/// unit-testable without a session or editor.
enum ProofAssist {

    private static let identifierRegex = try! NSRegularExpression(pattern: "[A-Za-z_][A-Za-z0-9_]*")

    /// Conventional spec-structure operators that are never useful invariant
    /// candidates (and rarely useful DEF suggestions on their own).
    private static let structuralNames: Set<String> = ["Init", "Next", "Spec", "vars"]

    // MARK: - BY DEF suggestions

    /// Definitions referenced by the failed obligation's goal that TLAPM was
    /// NOT told to expand — the classic missing-`BY DEF` failure. Ordered by
    /// first appearance in the goal, capped at 8.
    static func byDefSuggestions(
        for obligation: ProofObligation,
        content: String,
        symbols: [TLASymbol],
        crossModuleSymbols: [ModuleSymbol] = []
    ) -> [String] {
        guard !obligation.obligationText.isEmpty else { return [] }

        var definitionNames = Set<String>()
        for symbol in symbols.flattened()
        where symbol.kind == .operator || symbol.kind == .definition {
            definitionNames.insert(symbol.name)
        }
        for moduleSymbol in crossModuleSymbols
        where moduleSymbol.symbol.kind == .operator || moduleSymbol.symbol.kind == .definition {
            definitionNames.insert(moduleSymbol.symbol.name)
        }

        let alreadyExpanded = existingDefNames(near: obligation, content: content)

        var seen = Set<String>()
        var suggestions: [String] = []
        for identifier in identifiers(in: obligation.obligationText) {
            guard suggestions.count < 8 else { break }
            guard seen.insert(identifier).inserted else { continue }
            guard definitionNames.contains(identifier),
                  !alreadyExpanded.contains(identifier),
                  !TLAIdentifierValidator.reservedWords.contains(identifier) else { continue }
            suggestions.append(identifier)
        }
        return suggestions
    }

    // MARK: - BY DEF insertion

    /// A planned single-line edit applying `BY DEF` names to a proof leaf.
    struct ByDefInsertion: Equatable {
        /// 0-based line index in the document.
        let lineIndex: Int
        let originalLine: String
        let updatedLine: String
    }

    /// Plan the edit that adds `names` to the proof leaf of the failed step:
    /// `OBVIOUS` becomes `BY DEF …`; `BY …` gains ` DEF …`; an existing
    /// `BY … DEF a, b` gains `, …`. Returns nil when no proof leaf is found
    /// near the step (structured proofs are not modified — the UI then offers
    /// the suggestions as copyable text only).
    static func planByDefInsertion(
        names: [String],
        for obligation: ProofObligation,
        content: String
    ) -> ByDefInsertion? {
        guard !names.isEmpty else { return nil }
        let lines = content.components(separatedBy: "\n")
        let stepStart = max(0, obligation.location.startLine - 1)   // TLAPM is 1-based
        guard stepStart < lines.count else { return nil }

        let rawEnd = min(lines.count - 1, max(stepStart, obligation.location.endLine - 1) + 2)
        let windowEnd = clampedWindowEnd(stepStart: stepStart, rawEnd: rawEnd, lines: lines)
        let joined = names.joined(separator: ", ")

        // A BY clause can span lines (`BY Z3,` … `DEF Inv` on a continuation).
        // If ANY line in the window already carries DEF, extend THAT line —
        // appending a second `DEF` to the BY line would be a parse error.
        for lineIndex in stepStart...windowEnd {
            let line = lines[lineIndex]
            let (code, comment) = splitLineComment(line)
            if code.range(of: #"\bDEF\b"#, options: .regularExpression) != nil {
                let trimmedCode = trimmingTrailingWhitespace(code)
                // A DEF list ending in a comma continues onto the next physical
                // line. We can only rewrite ONE line, so appending here would
                // orphan that continuation (`…Inv, New` on this line; the old tail
                // token with no separating comma on the next) — itself a parse
                // error. Refuse, like the BY branch below, and leave placement to
                // the user (suggestions stay copyable) (e2e M4).
                guard !trimmedCode.hasSuffix(",") else { return nil }
                return ByDefInsertion(
                    lineIndex: lineIndex,
                    originalLine: line,
                    updatedLine: trimmedCode + ", \(joined)" + comment
                )
            }
        }

        for lineIndex in stepStart...windowEnd {
            let line = lines[lineIndex]
            // Edit only the code portion; a trailing \* comment is reattached
            // after the insertion so the new names can't get commented out.
            let (code, comment) = splitLineComment(line)

            if let obviousRange = code.range(of: #"\bOBVIOUS\b"#, options: .regularExpression) {
                var updated = code
                updated.replaceSubrange(obviousRange, with: "BY DEF \(joined)")
                return ByDefInsertion(
                    lineIndex: lineIndex,
                    originalLine: line,
                    updatedLine: updated + comment
                )
            }

            if code.range(of: #"\bBY\b"#, options: .regularExpression) != nil {
                // A trailing comma means the BY list continues on the next
                // line — appending DEF here would split the clause. Bail and
                // let the user place it (suggestions stay copyable).
                let trimmedCode = trimmingTrailingWhitespace(code)
                guard !trimmedCode.hasSuffix(",") else { return nil }
                return ByDefInsertion(
                    lineIndex: lineIndex,
                    originalLine: line,
                    updatedLine: trimmedCode + " DEF \(joined)" + comment
                )
            }
        }
        return nil
    }

    // MARK: - TLC bridge candidates

    /// Zero-parameter user definitions referenced by the failed obligation —
    /// candidates for "model-check this as an invariant". Invariant-looking
    /// names (Inv/TypeOK/Safe…) rank first; conventional structure operators
    /// (Init/Next/Spec/vars) are excluded. Capped at 5.
    static func invariantCandidates(
        for obligation: ProofObligation,
        symbols: [TLASymbol]
    ) -> [String] {
        var statePredicates = Set<String>()
        for symbol in symbols.flattened()
        where (symbol.kind == .operator || symbol.kind == .definition)
            && symbol.parameters.isEmpty
            && !structuralNames.contains(symbol.name) {
            statePredicates.insert(symbol.name)
        }

        var seen = Set<String>()
        var candidates: [String] = []
        for identifier in identifiers(in: obligation.obligationText)
        where seen.insert(identifier).inserted && statePredicates.contains(identifier) {
            candidates.append(identifier)
        }

        let looksInvariant: (String) -> Bool = {
            $0.contains("Inv") || $0.contains("TypeOK") || $0.contains("Safe")
        }
        let ranked = candidates.filter(looksInvariant) + candidates.filter { !looksInvariant($0) }
        return Array(ranked.prefix(5))
    }

    // MARK: - Internals

    private static func identifiers(in text: String) -> [String] {
        let nsText = text as NSString
        let matches = identifierRegex.matches(
            in: text,
            range: NSRange(location: 0, length: nsText.length)
        )
        return matches.map { nsText.substring(with: $0.range) }
    }

    /// Names already listed after `DEF` on lines near the failed step.
    private static func existingDefNames(near obligation: ProofObligation, content: String) -> Set<String> {
        let lines = content.components(separatedBy: "\n")
        let stepStart = max(0, obligation.location.startLine - 1)
        guard stepStart < lines.count else { return [] }
        let rawEnd = min(lines.count - 1, max(stepStart, obligation.location.endLine - 1) + 2)
        // Share the planner's step-boundary clamp so "already expanded" detection
        // and the insertion planner agree on this step's region — otherwise a
        // `BY … DEF Foo` in the NEXT step (within the +2 spill) could wrongly
        // suppress a valid suggestion for THIS step (e2e Low).
        let windowEnd = clampedWindowEnd(stepStart: stepStart, rawEnd: rawEnd, lines: lines)

        var names = Set<String>()
        for line in lines[stepStart...windowEnd] {
            let (code, _) = splitLineComment(line)
            guard let defRange = code.range(of: #"\bDEF\b"#, options: .regularExpression) else { continue }
            for name in identifiers(in: String(code[defRange.upperBound...])) {
                names.insert(name)
            }
        }
        return names
    }

    /// Clamp a look-ahead window so it never spills into the NEXT proof step: a
    /// line that begins with a `<level>` step marker (number or `*`/`+`, NOT a
    /// `<<…>>` tuple literal) ends this step's region. Returns the last line index
    /// that still belongs to the step starting at `stepStart`.
    private static func clampedWindowEnd(stepStart: Int, rawEnd: Int, lines: [String]) -> Int {
        guard stepStart + 1 <= rawEnd else { return rawEnd }
        for lineIndex in (stepStart + 1)...rawEnd {
            let trimmed = lines[lineIndex].trimmingCharacters(in: .whitespaces)
            if trimmed.range(of: #"^<[0-9*+]"#, options: .regularExpression) != nil {
                return lineIndex - 1
            }
        }
        return rawEnd
    }

    private static func splitLineComment(_ line: String) -> (code: String, comment: String) {
        guard let commentRange = line.range(of: "\\*") else { return (line, "") }
        return (String(line[..<commentRange.lowerBound]), String(line[commentRange.lowerBound...]))
    }

    private static func trimmingTrailingWhitespace(_ text: String) -> String {
        var result = text
        while let last = result.last, last == " " || last == "\t" {
            result.removeLast()
        }
        return result
    }
}
