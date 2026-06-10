import Foundation
import SwiftUI

// MARK: - Centralized Notification Names

extension Notification.Name {

    // MARK: View Commands

    static let goToLine = Notification.Name("TLAGoToLine")
    static let foldAll = Notification.Name("TLAFoldAll")
    static let unfoldAll = Notification.Name("TLAUnfoldAll")
    static let toggleFold = Notification.Name("TLAToggleFold")
    static let toggleSymbolOutline = Notification.Name("TLAToggleSymbolOutline")
    static let toggleNavigatorSidebar = Notification.Name("TLAToggleNavigatorSidebar")
    static let toggleInspectorSidebar = Notification.Name("TLAToggleInspectorSidebar")

    // MARK: TLA+ Commands

    static let translatePlusCal = Notification.Name("TLATranslatePlusCal")
    static let goToPlusCalAlgorithm = Notification.Name("TLAGoToPlusCalAlgorithm")
    static let goToPlusCalTranslation = Notification.Name("TLAGoToPlusCalTranslation")
    static let goToDefinition = Notification.Name("TLAGoToDefinition")
    static let findReferences = Notification.Name("TLAFindReferences")

    // MARK: Language Intelligence

    /// Posted by ModuleSymbolIndex after entries are invalidated/re-indexed;
    /// per-document providers re-query their snapshot.
    static let moduleSymbolIndexDidUpdate = Notification.Name("TLAModuleSymbolIndexDidUpdate")

    /// Posted (with the document as object) when reference results are ready;
    /// the bottom panel switches to the References tab.
    static let showReferencesPanel = Notification.Name("TLAShowReferencesPanel")

    /// Rename the symbol at the cursor (opens the rename sheet).
    static let renameSymbol = Notification.Name("TLARenameSymbol")

    /// Generate a proof skeleton for the theorem at the cursor.
    static let decomposeProof = Notification.Name("TLADecomposeProof")

    /// Switch the bottom panel to the Output tab.
    static let showOutputPanel = Notification.Name("TLAShowOutputPanel")

    /// Switch the bottom panel to the Model Check tab.
    static let showModelCheckPanel = Notification.Name("TLAShowModelCheckPanel")

    // MARK: Model Checking

    static let runModelCheck = Notification.Name("TLARunModelCheck")
    static let stopModelCheck = Notification.Name("TLAStopModelCheck")
    static let editModelConfig = Notification.Name("TLAEditModelConfig")

    // MARK: Proofs

    static let checkCurrentStep = Notification.Name("TLACheckCurrentStep")
    static let stopProofCheck = Notification.Name("TLAStopProofCheck")
    static let goToNextFailed = Notification.Name("TLAGoToNextFailed")

    // MARK: Find/Replace

    static let findNext = Notification.Name("TLAFindNext")
    static let findPrevious = Notification.Name("TLAFindPrevious")
    static let useSelectionForFind = Notification.Name("TLAUseSelectionForFind")
    static let showFindReplace = Notification.Name("TLAShowFindReplace")
    static let hideFindReplace = Notification.Name("TLAHideFindReplace")
    static let toggleFindReplace = Notification.Name("TLAToggleFindReplace")
    static let findReplacePanelHeightChanged = Notification.Name("TLAFindReplacePanelHeightChanged")
    static let findReplaceFocusSearchField = Notification.Name("TLAFindReplaceFocusSearchField")
    static let findReplaceFocusReplaceField = Notification.Name("TLAFindReplaceFocusReplaceField")

    // MARK: Editor

    static let editorColorSchemeDidChange = Notification.Name("editorColorSchemeDidChange")

    // MARK: Document

    static let documentWillClose = Notification.Name("TLADocumentWillClose")
}

// MARK: - Document-Scoped Notification Receiving

extension View {
    /// `.onReceive` for a document-scoped notification.
    ///
    /// Fires when the notification's object is `nil` (broadcast, e.g. from a
    /// menu command) or identical to `document` (targeted, e.g. from a
    /// toolbar button or another view of the same document).
    func onReceiveDocumentNotification(
        _ name: Notification.Name,
        for document: TLADocument,
        perform action: @escaping () -> Void
    ) -> some View {
        onReceiveDocumentNotification(name, for: document) { _ in action() }
    }

    /// Variant passing the `Notification` through for `userInfo` consumers.
    func onReceiveDocumentNotification(
        _ name: Notification.Name,
        for document: TLADocument,
        perform action: @escaping (Notification) -> Void
    ) -> some View {
        onReceive(NotificationCenter.default.publisher(for: name)) { notification in
            guard notification.object == nil
                    || (notification.object as? TLADocument) === document else { return }
            action(notification)
        }
    }
}
