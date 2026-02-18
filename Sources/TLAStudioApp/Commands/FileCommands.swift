import SwiftUI

// MARK: - File Commands

/// File menu commands with all file operations
struct FileCommands: Commands {

    var body: some Commands {
        // Replace default New Item group
        CommandGroup(replacing: .newItem) {
            Button("New Specification") {
                NSDocumentController.shared.newDocument(nil)
            }
            .keyboardShortcut("n", modifiers: .command)

            Menu("New From Template") {
                ForEach(DocumentTemplate.allCases, id: \.self) { template in
                    Button(template.displayName) {
                        (NSDocumentController.shared as? TLADocumentController)?
                            .newDocument(from: template)
                    }
                }
            }

            Divider()

            Button("Open...") {
                NSDocumentController.shared.openDocument(nil)
            }
            .keyboardShortcut("o", modifiers: .command)

            // Recent documents menu is automatic via NSDocumentController
        }

        // Replace default Save group
        CommandGroup(replacing: .saveItem) {
            Button("Save") {
                NSApp.sendAction(#selector(NSDocument.save(_:)), to: nil, from: nil)
            }
            .keyboardShortcut("s", modifiers: .command)

            Button("Save As...") {
                NSApp.sendAction(#selector(NSDocument.saveAs(_:)), to: nil, from: nil)
            }
            .keyboardShortcut("s", modifiers: [.command, .shift])

            Button("Save All") {
                for document in NSDocumentController.shared.documents {
                    document.save(nil)
                }
            }
            .keyboardShortcut("s", modifiers: [.command, .option])

            Divider()

            Button("Revert to Saved") {
                NSApp.sendAction(#selector(NSDocument.revertToSaved(_:)), to: nil, from: nil)
            }
        }

        // Add Close commands after Save
        CommandGroup(after: .saveItem) {
            Divider()

            Button("Close") {
                NSApp.sendAction(#selector(NSWindow.performClose(_:)), to: nil, from: nil)
            }
            .keyboardShortcut("w", modifiers: .command)

            Button("Close All") {
                NSDocumentController.shared.closeAllDocuments(
                    withDelegate: nil,
                    didCloseAllSelector: nil,
                    contextInfo: nil
                )
            }
            .keyboardShortcut("w", modifiers: [.command, .option])
        }
    }
}

// MARK: - Edit Commands

/// Standard edit commands (undo, redo, cut, copy, paste)
struct EditCommands: Commands {
    var body: some Commands {
        // Use default edit commands - they work with NSDocument/NSTextView
        CommandGroup(after: .undoRedo) {
            Divider()

            Button("Find...") {
                NotificationCenter.default.post(name: .showFindReplace, object: nil, userInfo: ["showReplace": false])
            }
            .keyboardShortcut("f", modifiers: .command)

            Button("Find and Replace...") {
                NotificationCenter.default.post(name: .showFindReplace, object: nil, userInfo: ["showReplace": true])
            }
            .keyboardShortcut("f", modifiers: [.command, .option])

            Button("Find Next") {
                NotificationCenter.default.post(name: .findNext, object: nil)
            }
            .keyboardShortcut("g", modifiers: .command)

            Button("Find Previous") {
                NotificationCenter.default.post(name: .findPrevious, object: nil)
            }
            .keyboardShortcut("g", modifiers: [.command, .shift])

            Divider()

            Button("Use Selection for Find") {
                NotificationCenter.default.post(name: .useSelectionForFind, object: nil)
            }
            .keyboardShortcut("e", modifiers: .command)
        }
    }
}

// MARK: - View Commands

/// View menu commands for folding and display options
struct ViewCommands: Commands {
    var body: some Commands {
        CommandMenu("View") {
            Button("Go to Line...") {
                NotificationCenter.default.post(name: .goToLine, object: nil)
            }
            .keyboardShortcut("g", modifiers: .command)

            Divider()

            Button("Fold All") {
                NotificationCenter.default.post(name: .foldAll, object: nil)
            }
            .keyboardShortcut("k", modifiers: [.command, .option])

            Button("Unfold All") {
                NotificationCenter.default.post(name: .unfoldAll, object: nil)
            }
            .keyboardShortcut("j", modifiers: [.command, .option])

            Button("Toggle Fold") {
                NotificationCenter.default.post(name: .toggleFold, object: nil)
            }
            .keyboardShortcut("[", modifiers: .command)

            Divider()

            Button("Show Symbol Outline") {
                NotificationCenter.default.post(name: .toggleSymbolOutline, object: nil)
            }
            .keyboardShortcut("0", modifiers: .command)
        }
    }
}

// MARK: - TLA Commands

struct TLACommands: Commands {
    var body: some Commands {
        CommandMenu("TLA+") {
            Button("Translate PlusCal") {
                NotificationCenter.default.post(name: .translatePlusCal, object: nil)
            }
            .keyboardShortcut("t", modifiers: [.command, .shift])

            Divider()

            Button("Go to Definition") {
                NotificationCenter.default.post(name: .goToDefinition, object: nil)
            }
            .keyboardShortcut("d", modifiers: .command)

            Button("Find All References") {
                NotificationCenter.default.post(name: .findReferences, object: nil)
            }
            .keyboardShortcut("r", modifiers: [.command, .shift])
        }
    }
}

// MARK: - Model Check Commands

struct ModelCheckCommands: Commands {
    var body: some Commands {
        CommandMenu("Model") {
            Button("Run TLC") {
                if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                    doc.runModelCheck()
                }
            }
            .keyboardShortcut("r", modifiers: .command)

            Button("Stop TLC") {
                if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                    doc.stopModelCheck()
                }
            }
            .keyboardShortcut(".", modifiers: .command)

            Divider()

            Button("Edit Model Configuration...") {
                NotificationCenter.default.post(name: .editModelConfig, object: nil)
            }
            .keyboardShortcut("m", modifiers: [.command, .shift])
        }
    }
}

// MARK: - Proof Commands

struct ProofCommands: Commands {
    var body: some Commands {
        CommandMenu("Proof") {
            Button("Check All Proofs") {
                if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                    doc.runProofCheck()
                }
            }
            .keyboardShortcut("p", modifiers: [.command, .shift])

            Button("Check Selection") {
                if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                    doc.checkSelectionProofStep()
                }
            }
            .keyboardShortcut("p", modifiers: .command)

            Divider()

            Button("Stop Proof Checking") {
                if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                    doc.stopProofCheck()
                }
            }

            Divider()

            Button("Go to Next Failed Proof") {
                if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                    doc.goToNextFailedProof()
                }
            }
            .keyboardShortcut("'", modifiers: .command)
        }
    }
}

// MARK: - Help Commands

struct HelpCommands: Commands {
    var body: some Commands {
        CommandGroup(replacing: .help) {
            Button("Keyboard Shortcuts") {
                NSApp.showKeyboardShortcuts()
            }
            .keyboardShortcut("/", modifiers: .command)

            Divider()

            Button("TLA+ Language Reference") {
                if let url = URL(string: "https://lamport.azurewebsites.net/tla/tla.html") {
                    NSWorkspace.shared.open(url)
                }
            }

            Button("TLC Model Checker Guide") {
                if let url = URL(string: "https://lamport.azurewebsites.net/tla/tlc.html") {
                    NSWorkspace.shared.open(url)
                }
            }

            Button("TLAPS Proof System") {
                if let url = URL(string: "https://tla.msr-inria.inria.fr/tlaps/content/Home.html") {
                    NSWorkspace.shared.open(url)
                }
            }
        }
    }
}

// MARK: - Notification Names

// Notification.Name declarations are centralized in Utilities/NotificationNames.swift
