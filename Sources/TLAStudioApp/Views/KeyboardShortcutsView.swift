import SwiftUI

// MARK: - Keyboard Shortcuts View

/// A sheet displaying all available keyboard shortcuts
struct KeyboardShortcutsView: View {
    @Environment(\.dismiss) private var dismiss

    var body: some View {
        VStack(spacing: 0) {
            // Header
            HStack {
                Text("Keyboard Shortcuts")
                    .font(.title2.bold())
                Spacer()
                Button(action: { dismiss() }) {
                    Image(systemName: "xmark.circle.fill")
                        .font(.title2)
                        .foregroundColor(.secondary)
                }
                .buttonStyle(.plain)
            }
            .padding()

            Divider()

            // Shortcuts list
            ScrollView {
                VStack(alignment: .leading, spacing: 24) {
                    ShortcutSection(title: "File", shortcuts: fileShortcuts)
                    ShortcutSection(title: "Edit", shortcuts: editShortcuts)
                    ShortcutSection(title: "View", shortcuts: viewShortcuts)
                    ShortcutSection(title: "Navigation", shortcuts: navigationShortcuts)
                    ShortcutSection(title: "Model Checking", shortcuts: modelShortcuts)
                    ShortcutSection(title: "Proof", shortcuts: proofShortcuts)
                }
                .padding()
            }
        }
        .frame(width: 500, height: 600)
    }

    // MARK: - Shortcut Data

    private var fileShortcuts: [ShortcutItem] {
        [
            ShortcutItem(keys: "N", description: "New Specification"),
            ShortcutItem(keys: "O", description: "Open..."),
            ShortcutItem(keys: "S", description: "Save"),
            ShortcutItem(keys: "S", modifiers: [.shift], description: "Save As..."),
            ShortcutItem(keys: "S", modifiers: [.option], description: "Save All"),
            ShortcutItem(keys: "W", description: "Close"),
            ShortcutItem(keys: "W", modifiers: [.option], description: "Close All"),
        ]
    }

    private var editShortcuts: [ShortcutItem] {
        [
            ShortcutItem(keys: "Z", description: "Undo"),
            ShortcutItem(keys: "Z", modifiers: [.shift], description: "Redo"),
            ShortcutItem(keys: "X", description: "Cut"),
            ShortcutItem(keys: "C", description: "Copy"),
            ShortcutItem(keys: "V", description: "Paste"),
            ShortcutItem(keys: "A", description: "Select All"),
            ShortcutItem(keys: "F", description: "Find..."),
            ShortcutItem(keys: "F", modifiers: [.option], description: "Find and Replace..."),
            ShortcutItem(keys: "G", description: "Find Next"),
            ShortcutItem(keys: "G", modifiers: [.shift], description: "Find Previous"),
            ShortcutItem(keys: "E", description: "Use Selection for Find"),
        ]
    }

    private var viewShortcuts: [ShortcutItem] {
        [
            ShortcutItem(keys: "G", description: "Go to Line..."),
            ShortcutItem(keys: "K", modifiers: [.option], description: "Fold All"),
            ShortcutItem(keys: "J", modifiers: [.option], description: "Unfold All"),
            ShortcutItem(keys: "[", description: "Toggle Fold"),
            ShortcutItem(keys: "0", description: "Show Symbol Outline"),
        ]
    }

    private var navigationShortcuts: [ShortcutItem] {
        [
            ShortcutItem(keys: "D", description: "Go to Definition"),
            ShortcutItem(keys: "R", modifiers: [.shift], description: "Find All References"),
        ]
    }

    private var modelShortcuts: [ShortcutItem] {
        [
            ShortcutItem(keys: "R", description: "Run TLC"),
            ShortcutItem(keys: ".", description: "Stop TLC"),
            ShortcutItem(keys: "M", modifiers: [.shift], description: "Edit Model Configuration..."),
        ]
    }

    private var proofShortcuts: [ShortcutItem] {
        [
            ShortcutItem(keys: "P", modifiers: [.shift], description: "Check All Proofs"),
            ShortcutItem(keys: "P", description: "Check Selection"),
            ShortcutItem(keys: "'", description: "Go to Next Failed Proof"),
            ShortcutItem(keys: "T", modifiers: [.shift], description: "Translate PlusCal"),
        ]
    }
}

// MARK: - Shortcut Section

private struct ShortcutSection: View {
    let title: String
    let shortcuts: [ShortcutItem]

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            Text(title)
                .font(.headline)
                .foregroundColor(.secondary)

            ForEach(shortcuts) { shortcut in
                HStack {
                    Text(shortcut.description)
                        .font(.body)
                    Spacer()
                    ShortcutBadge(shortcut: shortcut)
                }
            }
        }
    }
}

// MARK: - Shortcut Item

private struct ShortcutItem: Identifiable {
    let id = UUID()
    let keys: String
    var modifiers: Set<ModifierKey> = []
    let description: String

    enum ModifierKey {
        case shift
        case option
        case control
    }
}

// MARK: - Shortcut Badge

private struct ShortcutBadge: View {
    let shortcut: ShortcutItem

    var body: some View {
        HStack(spacing: 2) {
            // Command key is always present
            KeyCap(symbol: "\u{2318}")

            // Additional modifiers
            if shortcut.modifiers.contains(.shift) {
                KeyCap(symbol: "\u{21E7}")
            }
            if shortcut.modifiers.contains(.option) {
                KeyCap(symbol: "\u{2325}")
            }
            if shortcut.modifiers.contains(.control) {
                KeyCap(symbol: "\u{2303}")
            }

            // Main key
            KeyCap(symbol: shortcut.keys)
        }
    }
}

// MARK: - Key Cap

private struct KeyCap: View {
    let symbol: String

    var body: some View {
        Text(symbol)
            .font(.system(size: 12, weight: .medium, design: .rounded))
            .frame(minWidth: 22, minHeight: 22)
            .background(Color(NSColor.controlBackgroundColor))
            .cornerRadius(4)
            .overlay(
                RoundedRectangle(cornerRadius: 4)
                    .stroke(Color.secondary.opacity(0.3), lineWidth: 1)
            )
    }
}

// MARK: - Menu Command

extension NSApplication {
    @objc func showKeyboardShortcuts() {
        let panel = NSPanel(
            contentRect: NSRect(x: 0, y: 0, width: 500, height: 600),
            styleMask: [.titled, .closable, .resizable],
            backing: .buffered,
            defer: false
        )
        panel.title = "Keyboard Shortcuts"
        panel.contentView = NSHostingView(rootView: KeyboardShortcutsView())
        panel.center()
        panel.makeKeyAndOrderFront(nil)
    }
}

// MARK: - Preview

#if DEBUG
struct KeyboardShortcutsView_Previews: PreviewProvider {
    static var previews: some View {
        KeyboardShortcutsView()
    }
}
#endif
