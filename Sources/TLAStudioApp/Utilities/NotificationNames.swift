import Foundation

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
    static let goToDefinition = Notification.Name("TLAGoToDefinition")
    static let findReferences = Notification.Name("TLAFindReferences")

    // MARK: Model Checking

    static let runModelCheck = Notification.Name("TLARunModelCheck")
    static let stopModelCheck = Notification.Name("TLAStopModelCheck")
    static let editModelConfig = Notification.Name("TLAEditModelConfig")

    // MARK: Proofs

    static let checkAllProofs = Notification.Name("TLACheckAllProofs")
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
