import Foundation

// MARK: - Completion Merger

/// Merges cross-module symbols into the Rust core's completion list.
///
/// Pure logic: context gating (module-name contexts like `EXTENDS <cursor>`
/// must not be polluted with operator symbols), shadowing (anything already in
/// the base list — local symbols, stdlib — wins by label), priority placement
/// (16+ sorts cross-module items below local symbols at 15 but the list stays
/// unified), and the 2000-item cap matching the Rust `MAX_COMPLETIONS`.
enum CrossModuleCompletionMerger {

    static let maxItems = 2000
    /// Local expression symbols use 15 in the Rust core; cross-module items
    /// sit just below them.
    static let basePriority: UInt32 = 16

    static func shouldMerge(into context: TLACompletionContext) -> Bool {
        switch context {
        case .afterExtends, .afterInstance, .afterWith:
            return false
        case .topLevel, .inExpression, .inProof, .afterSetOperator, .inLetDef, .unknown:
            return true
        }
    }

    static func merge(
        base: [TLADetailedCompletionItem],
        crossModule: [ModuleSymbol],
        context: TLACompletionContext,
        maxItems: Int = CrossModuleCompletionMerger.maxItems
    ) -> [TLADetailedCompletionItem] {
        guard shouldMerge(into: context), !crossModule.isEmpty else { return base }

        var seenLabels = Set(base.map(\.label))
        var merged = base
        for moduleSymbol in crossModule where seenLabels.insert(moduleSymbol.symbol.name).inserted {
            merged.append(completionItem(for: moduleSymbol))
        }

        merged.sort { a, b in
            a.sortPriority != b.sortPriority ? a.sortPriority < b.sortPriority : a.label < b.label
        }
        return merged.count > maxItems ? Array(merged.prefix(maxItems)) : merged
    }

    static func completionItem(for moduleSymbol: ModuleSymbol) -> TLADetailedCompletionItem {
        let symbol = moduleSymbol.symbol

        // Mirrors the Rust core's symbols_to_completions kind mapping.
        let kind: TLACompletionKind
        let priorityOffset: UInt32
        let kindDescription: String
        switch symbol.kind {
        case .operator, .definition:
            kind = .function
            priorityOffset = 0
            kindDescription = "Operator"
        case .variable:
            kind = .variable
            priorityOffset = 1
            kindDescription = "Variable"
        case .constant:
            kind = .constant
            priorityOffset = 2
            kindDescription = "Constant"
        case .theorem:
            kind = .theorem
            priorityOffset = 5
            kindDescription = "Theorem"
        case .module, .instance:
            kind = .module
            priorityOffset = 10
            kindDescription = "Module"
        case .assumption:
            kind = .constant
            priorityOffset = 8
            kindDescription = "Assumption"
        }

        let signature = symbol.parameters.isEmpty
            ? nil
            : "\(symbol.name)(\(symbol.parameters.joined(separator: ", ")))"

        return TLADetailedCompletionItem(
            label: symbol.name,
            kind: kind,
            detail: "from \(moduleSymbol.moduleName)",
            documentation: "\(kindDescription) defined in module \(moduleSymbol.moduleName)",
            insertText: nil,
            filterText: nil,
            sortPriority: basePriority + priorityOffset,
            signature: signature
        )
    }
}

// MARK: - Shared Coordinator Facade

/// Shared completion / signature-help implementation for both editor
/// representables (`TLAEditorView` and `TLAEditorViewWithFindReplace`) — the
/// Rust core result plus cross-module enrichment, in one place.
@MainActor
enum CrossModuleIntelliSense {

    static func detailedCompletions(
        text: String,
        utf16Position: Int,
        crossModuleSymbols: [ModuleSymbol]
    ) async -> [TLADetailedCompletionItem] {
        let tlaPosition = TextCoordinateMapper.position(forUTF16Offset: utf16Position, in: text)
        do {
            let parseResult = try await TLACoreWrapper.shared.parse(text)
            let base = await TLACoreWrapper.shared.getDetailedCompletions(
                from: parseResult,
                at: tlaPosition
            )
            guard !crossModuleSymbols.isEmpty else { return base }

            let context = await TLACoreWrapper.shared.analyzeContext(from: parseResult, at: tlaPosition)
            return CrossModuleCompletionMerger.merge(
                base: base,
                crossModule: crossModuleSymbols,
                context: context
            )
        } catch {
            return []
        }
    }

    static func signatureHelp(
        text: String,
        utf16Position: Int,
        crossModuleSymbols: [ModuleSymbol]
    ) async -> TLASignatureHelp? {
        let tlaPosition = TextCoordinateMapper.position(forUTF16Offset: utf16Position, in: text)

        // The Rust core covers stdlib + current-document operators; it wins.
        if let parseResult = try? await TLACoreWrapper.shared.parse(text),
           let rustHelp = await TLACoreWrapper.shared.getSignatureHelp(from: parseResult, at: tlaPosition) {
            return rustHelp
        }

        // Fallback: an operator defined in an EXTENDS'd module.
        guard let call = CallContextScanner.enclosingCall(in: text, at: tlaPosition),
              let moduleSymbol = crossModuleSymbols.first(where: {
                  $0.symbol.name == call.operatorName && !$0.symbol.parameters.isEmpty
              }) else {
            return nil
        }

        let parameters = moduleSymbol.symbol.parameters
        return TLASignatureHelp(
            signatures: [TLASignatureInfo(
                label: "\(moduleSymbol.symbol.name)(\(parameters.joined(separator: ", ")))",
                documentation: "Operator defined in \(moduleSymbol.moduleName)",
                parameters: parameters.map { TLAParameterInfo(label: $0, documentation: nil) }
            )],
            activeSignature: 0,
            activeParameter: UInt32(min(call.activeParameter, max(0, parameters.count - 1)))
        )
    }
}
