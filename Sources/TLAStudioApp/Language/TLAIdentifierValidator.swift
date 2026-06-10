import Foundation

/// Validates candidate TLA+ identifiers for rename.
enum TLAIdentifierValidator {

    /// The TLA+ reserved words (superset of the completion keyword list —
    /// includes the proof-language keywords).
    static let reservedWords: Set<String> = [
        "ACTION", "ASSUME", "ASSUMPTION", "AXIOM", "BOOLEAN", "BY", "CASE",
        "CHOOSE", "CONSTANT", "CONSTANTS", "COROLLARY", "DEF", "DEFINE",
        "DEFS", "DOMAIN", "ELSE", "ENABLED", "EXCEPT", "EXTENDS", "FALSE",
        "HAVE", "HIDE", "IF", "IN", "INSTANCE", "LAMBDA", "LEMMA", "LET",
        "LOCAL", "MODULE", "NEW", "OBVIOUS", "OMITTED", "ONLY", "OTHER",
        "PICK", "PROOF", "PROPOSITION", "PROVE", "QED", "RECURSIVE", "STATE",
        "STRING", "SUBSET", "SUFFICES", "TAKE", "TEMPORAL", "THEN", "THEOREM",
        "TRUE", "UNCHANGED", "UNION", "USE", "VARIABLE", "VARIABLES", "WITH",
        "WITNESS"
    ]

    enum ValidationError: Equatable {
        case empty
        case invalidCharacters
        case noLetter
        case reservedWord
        case fairnessPrefix
        case unchanged

        var message: String {
            switch self {
            case .empty: return "Name is empty"
            case .invalidCharacters: return "Only letters, digits, and _ are allowed"
            case .noLetter: return "Name must contain at least one letter"
            case .reservedWord: return "Reserved TLA+ keyword"
            case .fairnessPrefix: return "Names starting with WF_ or SF_ are reserved for fairness operators"
            case .unchanged: return "Same as the current name"
            }
        }
    }

    /// nil ⇒ valid.
    static func validate(_ candidate: String, original: String) -> ValidationError? {
        if candidate.isEmpty { return .empty }
        if candidate == original { return .unchanged }
        if candidate.range(of: #"^[A-Za-z0-9_]+$"#, options: .regularExpression) == nil {
            return .invalidCharacters
        }
        if !candidate.contains(where: \.isLetter) { return .noLetter }
        if candidate.hasPrefix("WF_") || candidate.hasPrefix("SF_") { return .fairnessPrefix }
        if reservedWords.contains(candidate) { return .reservedWord }
        return nil
    }
}
