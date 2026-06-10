import Foundation

/// Minimal TLA+-aware scanner for top-level structure: tracks bracket depth
/// (`()`, `[]`, `{}`, `<< >>`), skips strings (`"…"` with `\"` escapes), line
/// comments (`\* …`), and nested block comments (`(* … *)`), while tracking
/// the line/column of the character most recently returned.
///
/// Shared by `NextActionDecomposer` (top-level `\/` splitting) and
/// `ProofSkeletonGenerator` (top-level `/\` and `:` scanning).
///
/// Note: `CallContextScanner` is intentionally NOT built on this — it is a
/// *backwards* prefix scan that mirrors the Rust core's
/// `find_enclosing_call_from_source` 1:1 (the duplication is the parity
/// contract). `BracketMatcher` (SourceEditor) is also separate: an
/// editor-gesture matcher in NSRange domain with its own perf cache.
struct TLATopLevelScanner {
    let text: String
    private(set) var index: String.Index
    private(set) var depth = 0
    private(set) var line = 0
    /// Column of the character most recently returned.
    private(set) var column = -1

    init(text: String) {
        self.text = text
        self.index = text.startIndex
    }

    func peek(offset: Int = 0) -> Character? {
        guard let i = text.index(index, offsetBy: offset, limitedBy: text.endIndex),
              i < text.endIndex else { return nil }
        return text[i]
    }

    mutating func skip(_ count: Int = 1) {
        for _ in 0..<count where index < text.endIndex {
            advancePosition(text[index])
            index = text.index(after: index)
        }
    }

    private mutating func advancePosition(_ character: Character) {
        // `isNewline` also matches the single "\r\n" grapheme cluster —
        // a bare `== "\n"` comparison would miss CRLF content entirely.
        if character.isNewline {
            line += 1
            column = -1
        } else {
            column += 1
        }
    }

    /// Returns the next significant character (outside strings/comments)
    /// and its index, updating depth for brackets.
    mutating func next() -> (Character, String.Index)? {
        while index < text.endIndex {
            let character = text[index]
            let characterIndex = index
            advancePosition(character)
            index = text.index(after: index)

            switch character {
            case "\"":
                skipString()
                continue
            case "\\" where peekAt(characterIndex, offset: 1) == "*":
                skipLineComment()
                continue
            case "(" where peekAt(characterIndex, offset: 1) == "*":
                skipBlockComment()
                continue
            case "(", "[", "{":
                depth += 1
            case ")", "]", "}":
                depth -= 1
            case "<" where peekAt(characterIndex, offset: 1) == "<":
                depth += 1
                skip()
            case ">" where peekAt(characterIndex, offset: 1) == ">":
                depth -= 1
                skip()
            default:
                break
            }
            return (character, characterIndex)
        }
        return nil
    }

    private func peekAt(_ base: String.Index, offset: Int) -> Character? {
        guard let i = text.index(base, offsetBy: offset, limitedBy: text.endIndex),
              i < text.endIndex else { return nil }
        return text[i]
    }

    private mutating func skipString() {
        while index < text.endIndex {
            let character = text[index]
            advancePosition(character)
            index = text.index(after: index)
            if character == "\\" {
                // Skip the escaped character (e.g. \" or \\).
                if index < text.endIndex {
                    advancePosition(text[index])
                    index = text.index(after: index)
                }
            } else if character == "\"" {
                return
            }
        }
    }

    private mutating func skipLineComment() {
        // Stop at any newline grapheme (including "\r\n") — comparing
        // against "\n" alone would swallow the rest of a CRLF file.
        while index < text.endIndex, !text[index].isNewline {
            advancePosition(text[index])
            index = text.index(after: index)
        }
    }

    private mutating func skipBlockComment() {
        // Already consumed `(`; consume the `*` then scan for matching `*)`,
        // handling nesting.
        var nesting = 1
        skip()   // the `*`
        while index < text.endIndex, nesting > 0 {
            let character = text[index]
            advancePosition(character)
            index = text.index(after: index)
            if character == "(", index < text.endIndex, text[index] == "*" {
                nesting += 1
                skip()
            } else if character == "*", index < text.endIndex, text[index] == ")" {
                nesting -= 1
                skip()
            }
        }
    }
}
