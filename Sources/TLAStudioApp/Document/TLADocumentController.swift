import AppKit
import UniformTypeIdentifiers

// MARK: - TLADocumentController

/// Custom document controller for TLA+ specific behaviors.
/// See Docs/architecture/01-document-management.md for specification.
final class TLADocumentController: NSDocumentController {

    // MARK: - Document Type Constants

    static let tlaTypeName = "TLA+ Specification"
    static let tlaUTI = "com.tlaplus.specification"
    static let cfgTypeName = "TLA+ Configuration"
    static let cfgUTI = "com.tlaplus.configuration"

    // MARK: - Initialization

    override init() {
        super.init()
    }

    required init?(coder: NSCoder) {
        super.init(coder: coder)
    }

    // MARK: - Document Type Registration

    override var documentClassNames: [String] {
        ["TLADocument"]
    }

    override var defaultType: String? {
        Self.tlaTypeName
    }

    override func documentClass(forType typeName: String) -> AnyClass? {
        TLADocument.self
    }

    override func typeForContents(of url: URL) throws -> String {
        let ext = url.pathExtension.lowercased()
        switch ext {
        case "tla":
            return Self.tlaTypeName
        case "cfg":
            return Self.cfgTypeName
        default:
            return Self.tlaTypeName
        }
    }

    override func displayName(forType typeName: String) -> String {
        switch typeName {
        case Self.tlaTypeName, Self.tlaUTI:
            return "TLA+ Specification"
        case Self.cfgTypeName, Self.cfgUTI:
            return "TLA+ Configuration"
        default:
            return typeName
        }
    }

    // MARK: - New Document

    override func newDocument(_ sender: Any?) {
        let document = TLADocument()
        document.makeWindowControllers()
        document.showWindows()
        addDocument(document)
    }

    override func makeUntitledDocument(ofType typeName: String) throws -> NSDocument {
        let document = TLADocument()
        return document
    }

    override func makeDocument(withContentsOf url: URL, ofType typeName: String) throws -> NSDocument {
        let document = TLADocument()
        try document.read(from: url, ofType: typeName)
        document.fileURL = url
        return document
    }

    /// Create new document from template
    func newDocument(from template: DocumentTemplate) {
        let document = TLADocument()
        document.content = template.content
        document.makeWindowControllers()
        document.showWindows()
        addDocument(document)
    }

    // MARK: - Open Document

    override func openDocument(_ sender: Any?) {
        let panel = NSOpenPanel()
        panel.allowedContentTypes = [
            UTType(filenameExtension: "tla") ?? .plainText,
            UTType(filenameExtension: "cfg") ?? .plainText
        ]
        panel.allowsMultipleSelection = true
        panel.canChooseDirectories = false

        panel.begin { [weak self] response in
            guard response == .OK else { return }
            for url in panel.urls {
                self?.openDocument(withContentsOf: url, display: true) { _, _, _ in }
            }
        }
    }

    /// Open specific file programmatically
    func openDocument(at url: URL) {
        openDocument(withContentsOf: url, display: true) { document, wasOpen, error in
            if let error = error {
                NSApp.presentError(error)
            }
        }
    }

    // MARK: - Recent Documents

    override func noteNewRecentDocumentURL(_ url: URL) {
        if url.pathExtension == "tla" || url.pathExtension == "cfg" {
            super.noteNewRecentDocumentURL(url)
        }
    }
}

// MARK: - Document Templates

/// Templates for creating new TLA+ documents
enum DocumentTemplate: String, CaseIterable {
    case empty
    case specification
    case plusCal
    case refinement

    var displayName: String {
        switch self {
        case .empty: return "Empty Specification"
        case .specification: return "Specification with Variables"
        case .plusCal: return "PlusCal Algorithm"
        case .refinement: return "Refinement Mapping"
        }
    }

    var content: String {
        switch self {
        case .empty:
            return TLADocument.newDocumentTemplate()

        case .specification:
            return """
            -------------------------------- MODULE Spec --------------------------------
            \\* A TLA+ specification template

            EXTENDS Naturals, Sequences, FiniteSets

            CONSTANTS
                NumProcesses

            VARIABLES
                state

            vars == <<state>>

            TypeInvariant ==
                state \\in [1..NumProcesses -> {"idle", "running", "done"}]

            Init ==
                state = [p \\in 1..NumProcesses |-> "idle"]

            Step(p) ==
                /\\ state[p] = "idle"
                /\\ state' = [state EXCEPT ![p] = "running"]

            Complete(p) ==
                /\\ state[p] = "running"
                /\\ state' = [state EXCEPT ![p] = "done"]

            Next ==
                \\E p \\in 1..NumProcesses:
                    \\/ Step(p)
                    \\/ Complete(p)

            Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)

            ================================================================================
            """

        case .plusCal:
            return """
            -------------------------------- MODULE Algorithm --------------------------------
            EXTENDS Naturals, Sequences, TLC

            (*--algorithm Example
            variables x = 0;

            process Worker \\in 1..3
            begin
                Work:
                    x := x + 1;
            end process;

            end algorithm; *)

            \\* BEGIN TRANSLATION
            \\* END TRANSLATION

            ================================================================================
            """

        case .refinement:
            return """
            -------------------------------- MODULE ImplSpec --------------------------------
            \\* Refinement mapping from implementation to abstract spec

            EXTENDS AbstractSpec

            VARIABLES
                implState

            \\* Refinement mapping
            StateMapping ==
                \\* Map implementation state to abstract state
                TRUE

            ImplInit ==
                /\\ implState = InitialValue
                /\\ StateMapping

            ImplNext ==
                /\\ implState' \\in NextStates(implState)
                /\\ StateMapping'

            ImplSpec == ImplInit /\\ [][ImplNext]_implState

            THEOREM ImplSpec => Spec

            ================================================================================
            """
        }
    }
}
