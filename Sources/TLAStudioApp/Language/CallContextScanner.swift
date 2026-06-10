import Foundation

/// Finds the operator call enclosing a cursor position by scanning the line
/// prefix backwards — Swift port of the Rust core's
/// `find_enclosing_call_from_source`, used for the cross-module signature-help
/// fallback (the Rust path only knows stdlib + current-document operators).
enum CallContextScanner {

    struct Call: Equatable {
        let operatorName: String
        /// Zero-based index of the parameter under the cursor (commas at
        /// bracket depth 0 between the opening paren and the cursor).
        let activeParameter: Int
    }

    /// - Parameter position: line/column in Character units (the same
    ///   coordinates `TextCoordinateMapper.position` produces).
    static func enclosingCall(in text: String, at position: TLAPosition) -> Call? {
        let lines = text.components(separatedBy: "\n")
        let row = Int(position.line)
        guard row >= 0, row < lines.count else { return nil }

        let characters = Array(lines[row])
        let column = min(Int(position.column), characters.count)
        let prefix = Array(characters[0..<column])

        var parenDepth = 0
        for index in stride(from: prefix.count - 1, through: 0, by: -1) {
            switch prefix[index] {
            case ")":
                parenDepth += 1
            case "(":
                if parenDepth > 0 {
                    parenDepth -= 1
                    continue
                }
                // Opening paren of the enclosing call; the operator name
                // immediately precedes it (allowing whitespace).
                var nameEnd = index
                while nameEnd > 0 && prefix[nameEnd - 1].isWhitespace {
                    nameEnd -= 1
                }
                var nameStart = nameEnd
                while nameStart > 0,
                      prefix[nameStart - 1].isLetter
                        || prefix[nameStart - 1].isNumber
                        || prefix[nameStart - 1] == "_" {
                    nameStart -= 1
                }
                guard nameStart < nameEnd else { return nil }

                let name = String(prefix[nameStart..<nameEnd])
                var commaCount = 0
                var depth = 0
                for character in prefix[(index + 1)...] {
                    switch character {
                    case "(", "[", "{":
                        depth += 1
                    case ")", "]", "}":
                        depth = max(0, depth - 1)
                    case "," where depth == 0:
                        commaCount += 1
                    default:
                        break
                    }
                }
                return Call(operatorName: name, activeParameter: commaCount)
            default:
                break
            }
        }
        return nil
    }
}
