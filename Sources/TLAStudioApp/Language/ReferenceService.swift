import AppKit
import Foundation

// MARK: - Models

/// One occurrence of a symbol, in the current document or an EXTENDS'd module.
struct ReferenceHit: Identifiable, Equatable {
    let id = UUID()
    /// nil ⇒ the (possibly unsaved) current document.
    let fileURL: URL?
    let moduleName: String
    /// UTF-16 range — only for current-document hits (drives selection).
    let nsRange: NSRange?
    /// tree-sitter coordinates (0-based rows, byte columns).
    let tlaRange: TLARange
    /// Trimmed source-line preview.
    let lineText: String
    let role: TLAIdentifierOccurrence.Role

    static func == (lhs: ReferenceHit, rhs: ReferenceHit) -> Bool {
        lhs.fileURL == rhs.fileURL
            && lhs.moduleName == rhs.moduleName
            && lhs.tlaRange == rhs.tlaRange
            && lhs.role == rhs.role
    }
}

struct ReferenceResults: Equatable {
    let symbolName: String
    /// Current module's hits first, then per extended module.
    let hits: [ReferenceHit]
    let truncated: Bool
    /// false ⇒ the cross-module index had nothing to search (UI shows
    /// "current module only").
    let searchedExtendedModules: Bool
}

// MARK: - Reference Service

/// Symbol-aware find-references: identifier occurrences only (comments and
/// strings excluded by the tree-sitter grammar), across the current document
/// and the files of its indexed EXTENDS closure.
///
/// Matching is by NAME, not binding resolution — same-named shadowed/LET
/// bindings are all listed (the panel says so).
@MainActor
enum ReferenceService {

    static let maxExtendedFiles = 16
    static let maxHits = 5000

    static func findReferences(to name: String, in document: TLADocument) async -> ReferenceResults {
        var hits: [ReferenceHit] = []
        var truncated = false

        // 1. Current document (live buffer).
        let content = document.content
        hits.append(contentsOf: await occurrences(
            ofName: name,
            inContent: content,
            moduleName: document.moduleName,
            fileURL: nil,
            computeNSRanges: true
        ))

        // 2. Files of the indexed EXTENDS closure (unique, BFS-ordered).
        var searchedFiles: Set<URL> = []
        var orderedFiles: [(url: URL, moduleName: String)] = []
        for moduleSymbol in document.crossModuleProvider.symbols
        where searchedFiles.insert(moduleSymbol.fileURL).inserted {
            orderedFiles.append((moduleSymbol.fileURL, moduleSymbol.moduleName))
        }
        if orderedFiles.count > maxExtendedFiles {
            orderedFiles = Array(orderedFiles.prefix(maxExtendedFiles))
            truncated = true
        }

        for file in orderedFiles {
            guard hits.count < maxHits else {
                truncated = true
                break
            }
            // Prefer an open document's live buffer over the on-disk content.
            let fileContent: String
            if let openDocument = NSDocumentController.shared.document(for: file.url) as? TLADocument {
                fileContent = openDocument.content
            } else if let diskContent = try? String(contentsOf: file.url, encoding: .utf8) {
                fileContent = diskContent
            } else {
                continue
            }
            hits.append(contentsOf: await occurrences(
                ofName: name,
                inContent: fileContent,
                moduleName: file.moduleName,
                fileURL: file.url,
                computeNSRanges: false
            ))
        }

        if hits.count > maxHits {
            hits = Array(hits.prefix(maxHits))
            truncated = true
        }

        return ReferenceResults(
            symbolName: name,
            hits: hits,
            truncated: truncated,
            searchedExtendedModules: !orderedFiles.isEmpty
        )
    }

    private static func occurrences(
        ofName name: String,
        inContent content: String,
        moduleName: String,
        fileURL: URL?,
        computeNSRanges: Bool
    ) async -> [ReferenceHit] {
        guard let parseResult = try? await TLACoreWrapper.shared.parse(content) else {
            return []
        }
        let found = await TLACoreWrapper.shared.findIdentifierOccurrences(
            in: parseResult,
            name: name
        )
        guard !found.isEmpty else { return [] }

        let lines = content.components(separatedBy: "\n")
        let converter = computeNSRanges
            ? TextCoordinateMapper.TreeSitterRangeConverter(text: content)
            : nil

        return found.map { occurrence in
            let lineIndex = Int(occurrence.range.start.line)
            let preview = lineIndex < lines.count
                ? lines[lineIndex].trimmingCharacters(in: .whitespaces)
                : ""
            return ReferenceHit(
                fileURL: fileURL,
                moduleName: moduleName,
                nsRange: converter?.utf16Range(for: occurrence.range),
                tlaRange: occurrence.range,
                lineText: preview,
                role: occurrence.role
            )
        }
    }
}
