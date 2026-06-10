import Foundation

/// Result of fuzzy-matching a query against a completion candidate.
struct FuzzyMatch: Equatable {
    /// Higher is better. Tier bases keep classes ordered regardless of bonuses:
    /// exact 1000 > prefix 800 > word-boundary subsequence 600 > substring 400
    /// > plain subsequence 200.
    let score: Int
    /// Matched character index ranges in the candidate (for bold highlighting).
    let matchedRanges: [Swift.Range<Int>]
}

/// Pure fuzzy matcher for the completion popup. Replaces plain substring
/// filtering so `tinv` finds `TypeInvariant` and `\cu` ranks `\cup` first.
///
/// Word boundaries: candidate start, after `_` or any non-alphanumeric
/// (including `\`, so TLA+ operator names like `\cup` boundary-match), and
/// lower→Upper camelCase transitions.
enum FuzzyCompletionScorer {

    static func match(query: String, candidate: String) -> FuzzyMatch? {
        guard !query.isEmpty else { return nil }
        let queryChars = Array(query)
        let candidateChars = Array(candidate)
        guard queryChars.count <= candidateChars.count else { return nil }

        let queryLower = queryChars.map(lowercase)
        let candidateLower = candidateChars.map(lowercase)

        // Exact (case-insensitive)
        if candidateLower == queryLower {
            let ranges = [0..<candidateChars.count]
            return FuzzyMatch(
                score: 1000 + caseBonus(queryChars, candidateChars, matched: Array(0..<queryChars.count)),
                matchedRanges: ranges
            )
        }

        // Prefix
        if Array(candidateLower[0..<queryChars.count]) == queryLower {
            let matched = Array(0..<queryChars.count)
            return FuzzyMatch(
                score: 800 + caseBonus(queryChars, candidateChars, matched: matched)
                    - lengthPenalty(candidateChars.count),
                matchedRanges: [0..<queryChars.count]
            )
        }

        let boundaries = boundaryFlags(for: candidateChars)

        // Subsequence, preferring word-boundary anchors; falls back to a plain
        // greedy pass (boundary-first can overshoot and miss valid matches).
        let matched = subsequence(queryLower, in: candidateLower, boundaries: boundaries, boundaryFirst: true)
            ?? subsequence(queryLower, in: candidateLower, boundaries: boundaries, boundaryFirst: false)
        guard let matched else { return nil }

        let ranges = compress(matched)
        let allRunsOnBoundaries = ranges.allSatisfy { boundaries[$0.lowerBound] }
        let isContiguous = ranges.count == 1

        let base: Int
        if allRunsOnBoundaries {
            base = 600
        } else if isContiguous {
            base = 400  // substring
        } else {
            base = 200
        }

        var score = base
        score += caseBonus(queryChars, candidateChars, matched: matched)
        score += consecutiveBonus(matched)
        score -= min(2 * (matched.first ?? 0), 40)
        score -= lengthPenalty(candidateChars.count)

        return FuzzyMatch(score: score, matchedRanges: ranges)
    }

    // MARK: - Internals

    private static func lowercase(_ character: Character) -> Character {
        guard character.isUppercase else { return character }
        return Character(String(character).lowercased())
    }

    private static func boundaryFlags(for characters: [Character]) -> [Bool] {
        var flags = [Bool](repeating: false, count: characters.count)
        for index in characters.indices {
            if index == 0 {
                flags[index] = true
                continue
            }
            let previous = characters[index - 1]
            if !previous.isLetter && !previous.isNumber {
                flags[index] = true
            } else if previous.isLowercase && characters[index].isUppercase {
                flags[index] = true
            }
        }
        return flags
    }

    private static func subsequence(
        _ query: [Character],
        in candidate: [Character],
        boundaries: [Bool],
        boundaryFirst: Bool
    ) -> [Int]? {
        var matched: [Int] = []
        matched.reserveCapacity(query.count)
        var position = 0

        for queryChar in query {
            var found = -1
            if boundaryFirst {
                var index = position
                while index < candidate.count {
                    if boundaries[index] && candidate[index] == queryChar {
                        found = index
                        break
                    }
                    index += 1
                }
            }
            if found == -1 {
                var index = position
                while index < candidate.count {
                    if candidate[index] == queryChar {
                        found = index
                        break
                    }
                    index += 1
                }
            }
            guard found >= 0 else { return nil }
            matched.append(found)
            position = found + 1
        }
        return matched
    }

    private static func compress(_ indices: [Int]) -> [Swift.Range<Int>] {
        var ranges: [Swift.Range<Int>] = []
        var start = indices[0]
        var end = indices[0] + 1
        for index in indices.dropFirst() {
            if index == end {
                end += 1
            } else {
                ranges.append(start..<end)
                start = index
                end = index + 1
            }
        }
        ranges.append(start..<end)
        return ranges
    }

    private static func caseBonus(_ query: [Character], _ candidate: [Character], matched: [Int]) -> Int {
        for (queryIndex, candidateIndex) in matched.enumerated()
        where query[queryIndex] != candidate[candidateIndex] {
            return 0
        }
        return 10
    }

    private static func consecutiveBonus(_ matched: [Int]) -> Int {
        var bonus = 0
        for pairIndex in 1..<matched.count where matched[pairIndex] == matched[pairIndex - 1] + 1 {
            bonus += 8
        }
        return bonus
    }

    private static func lengthPenalty(_ candidateLength: Int) -> Int {
        min(candidateLength, 60) / 3
    }
}
