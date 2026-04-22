import Foundation

enum PlusCalNavigationTarget {
    case algorithm
    case translation
}

struct PlusCalSourceRanges: Equatable {
    let algorithm: NSRange
    let translation: NSRange?
}

enum PlusCalSourceMapping {
    private static let algorithmStartPattern = #"\(\*--(?:fair\s+)?algorithm\b|--(?:fair\s+)?algorithm\b"#
    private static let algorithmEndPattern = #"end algorithm;(\s*\*\))?"#
    private static let translationStartPattern = #"\\\* BEGIN TRANSLATION"#
    private static let translationEndPattern = #"\\\* END TRANSLATION"#

    static func ranges(in content: String) -> PlusCalSourceRanges? {
        let nsContent = content as NSString

        guard let algorithmStart = firstMatch(
            pattern: algorithmStartPattern,
            in: content,
            searchRange: NSRange(location: 0, length: nsContent.length)
        ) else {
            return nil
        }

        guard let algorithmEnd = firstMatch(
            pattern: algorithmEndPattern,
            in: content,
            searchRange: NSRange(
                location: algorithmStart.location,
                length: nsContent.length - algorithmStart.location
            )
        ) else {
            return nil
        }

        let algorithmRange = NSRange(
            location: algorithmStart.location,
            length: algorithmEnd.location + algorithmEnd.length - algorithmStart.location
        )
        let translationRange: NSRange?
        if let translationStart = firstMatch(
            pattern: translationStartPattern,
            in: content,
            searchRange: NSRange(location: 0, length: nsContent.length)
        ), let translationEnd = firstMatch(
            pattern: translationEndPattern,
            in: content,
            searchRange: NSRange(
                location: translationStart.location,
                length: nsContent.length - translationStart.location
            )
        ) {
            translationRange = NSRange(
                location: translationStart.location,
                length: translationEnd.location + translationEnd.length - translationStart.location
            )
        } else {
            translationRange = nil
        }

        return PlusCalSourceRanges(algorithm: algorithmRange, translation: translationRange)
    }

    static func range(for target: PlusCalNavigationTarget, in content: String) -> NSRange? {
        guard let ranges = ranges(in: content) else { return nil }
        switch target {
        case .algorithm:
            return ranges.algorithm
        case .translation:
            return ranges.translation
        }
    }

    static func remapSelection(_ selection: NSRange, from oldContent: String, to newContent: String) -> NSRange? {
        guard let oldRanges = ranges(in: oldContent),
              let newRanges = ranges(in: newContent) else {
            return clamped(selection, in: newContent)
        }

        if contains(selection.location, in: oldRanges.algorithm) {
            return mapped(selection, from: oldRanges.algorithm, to: newRanges.algorithm, in: newContent)
        }

        if let oldTranslation = oldRanges.translation,
           let newTranslation = newRanges.translation,
           contains(selection.location, in: oldTranslation) {
            return mapped(selection, from: oldTranslation, to: newTranslation, in: newContent)
        }

        return clamped(selection, in: newContent)
    }

    private static func mapped(_ selection: NSRange, from oldRange: NSRange, to newRange: NSRange, in content: String) -> NSRange {
        let relativeLocation = max(0, selection.location - oldRange.location)
        let newLocation = newRange.location + min(relativeLocation, newRange.length)
        let maxLength = max(0, (content as NSString).length - newLocation)
        return NSRange(location: newLocation, length: min(selection.length, maxLength))
    }

    private static func clamped(_ selection: NSRange, in content: String) -> NSRange {
        let contentLength = (content as NSString).length
        let location = min(max(0, selection.location), contentLength)
        let maxLength = max(0, contentLength - location)
        return NSRange(location: location, length: min(selection.length, maxLength))
    }

    private static func contains(_ location: Int, in range: NSRange) -> Bool {
        NSLocationInRange(location, range)
    }

    private static func firstMatch(pattern: String, in content: String, searchRange: NSRange) -> NSRange? {
        guard let regex = try? NSRegularExpression(pattern: pattern) else {
            return nil
        }

        return regex.firstMatch(in: content, range: searchRange)?.range
    }
}
