import AppKit
import Foundation

/// Scope-aware rename for the current document, built on the same
/// identifier-occurrence pipeline as Find All References (comments and strings
/// are never touched; matching is by name, so same-named shadowed bindings
/// rename too — the sheet says so).
///
/// v1 deliberately renames the current document only; when the symbol is
/// defined in an EXTENDS'd module, the sheet warns instead of editing other
/// files.
@MainActor
enum RenameService {

    struct Plan: Identifiable {
        let id = UUID()
        let originalName: String
        /// UTF-16 ranges in the document, in document order.
        let occurrences: [NSRange]
        /// The symbol's definition in an EXTENDS'd module, when it is NOT
        /// defined locally — renaming here won't touch that file.
        let externalDefinition: ModuleSymbol?
        /// Buffer must be unchanged between prepare and apply.
        let contentSnapshotHash: Int
    }

    /// Collect the rename plan for the symbol named `name`. nil when there is
    /// nothing to rename.
    static func prepare(name: String, document: TLADocument) async -> Plan? {
        let content = document.content
        guard let parseResult = try? await TLACoreWrapper.shared.parse(content) else {
            return nil
        }
        let occurrences = await TLACoreWrapper.shared.findIdentifierOccurrences(
            in: parseResult,
            name: name
        )
        guard !occurrences.isEmpty else { return nil }

        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: content)
        let ranges = occurrences.compactMap { converter.utf16Range(for: $0.range) }
        guard !ranges.isEmpty else { return nil }

        let definedLocally = TLACoreWrapper.shared.findDefinition(named: name, in: document.symbols) != nil
        let externalDefinition = definedLocally ? nil : document.crossModuleDefinitionTarget(for: name)

        return Plan(
            originalName: name,
            occurrences: ranges,
            externalDefinition: externalDefinition,
            contentSnapshotHash: content.hashValue
        )
    }

    /// An existing user symbol the new name would collide with.
    static func collision(newName: String, in symbols: [TLASymbol]) -> TLASymbol? {
        symbols.firstInTree { $0.name == newName }
    }

    /// Whether the new name shadows a builtin / stdlib operator.
    static func shadowsBuiltin(_ newName: String) -> Bool {
        TLADocumentation.builtins[newName] != nil
    }

    /// Apply the rename in a single undo group. Returns the number of
    /// occurrences replaced (0 on validation failure or stale buffer).
    @discardableResult
    static func apply(
        _ plan: Plan,
        newName: String,
        document: TLADocument,
        textView: NSTextView?
    ) -> Int {
        guard TLAIdentifierValidator.validate(newName, original: plan.originalName) == nil else {
            return 0
        }
        // Staleness guard: the buffer must match what `prepare` saw.
        guard document.content.hashValue == plan.contentSnapshotHash else { return 0 }

        let length = (document.content as NSString).length
        let ranges = plan.occurrences.sorted { $0.location > $1.location }
        guard ranges.allSatisfy({ $0.location >= 0 && NSMaxRange($0) <= length }) else {
            return 0
        }

        // Full content equality, not just length: the snapshot hash guards the
        // document model, but the editor buffer is a separate store that could
        // in principle drift (sync timing) — never splice into text we haven't
        // verified. O(n) once per user-confirmed rename is fine.
        if let textView, let textStorage = textView.textStorage, textView.string == document.content {
            // The plural shouldChangeText registers ONE undo group for all
            // ranges; one didChangeText closes it.
            let rangeValues = ranges.map { NSValue(range: $0) }
            let replacements = Array(repeating: newName, count: ranges.count)
            guard textView.shouldChangeText(inRanges: rangeValues, replacementStrings: replacements) else {
                return 0
            }
            textStorage.beginEditing()
            for range in ranges {
                textStorage.replaceCharacters(in: range, with: newName)
            }
            textStorage.endEditing()
            textView.didChangeText()
            textView.undoManager?.setActionName("Rename \(plan.originalName) to \(newName)")
        } else {
            // Headless fallback (no editor attached, e.g. tests): one content
            // assignment keeps the document pipeline consistent.
            let updated = NSMutableString(string: document.content)
            for range in ranges {
                updated.replaceCharacters(in: range, with: newName)
            }
            document.content = updated as String
        }
        return ranges.count
    }
}
