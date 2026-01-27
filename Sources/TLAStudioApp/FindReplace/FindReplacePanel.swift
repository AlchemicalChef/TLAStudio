import AppKit
import Combine
import SwiftUI

// MARK: - Find Replace Panel

/// A SwiftUI view for the find/replace panel that appears at the top of the editor.
/// Provides search, replace, and navigation functionality similar to Xcode/VSCode.
struct FindReplacePanel: View {
    @ObservedObject var manager: FindReplaceManager
    @State private var showReplace = false
    @State private var showOptions = false
    @FocusState private var isSearchFocused: Bool
    @FocusState private var isReplaceFocused: Bool

    var body: some View {
        VStack(spacing: 0) {
            // Search row
            searchRow

            // Replace row (collapsible)
            if showReplace {
                replaceRow
            }

            // Bottom border
            Divider()
        }
        .background(Color(nsColor: .controlBackgroundColor))
        .onChange(of: showReplace) { _, newValue in
            // Notify hosting view of height change
            manager.showReplace = newValue
            NotificationCenter.default.post(
                name: .findReplacePanelHeightChanged,
                object: manager
            )
        }
        .onReceive(NotificationCenter.default.publisher(for: .findReplaceFocusSearchField)) { _ in
            isSearchFocused = true
        }
        .onReceive(NotificationCenter.default.publisher(for: .findReplaceFocusReplaceField)) { _ in
            showReplace = true
            isReplaceFocused = true
        }
        .onAppear {
            // Sync local state with manager on appear
            showReplace = manager.showReplace
            isSearchFocused = true
        }
    }

    // MARK: - Search Row

    private var searchRow: some View {
        HStack(spacing: 8) {
            // Toggle replace visibility
            Button {
                withAnimation(.easeInOut(duration: 0.15)) {
                    showReplace.toggle()
                }
            } label: {
                Image(systemName: showReplace ? "chevron.down" : "chevron.right")
                    .font(.system(size: 10, weight: .semibold))
                    .foregroundColor(.secondary)
                    .frame(width: 16, height: 16)
            }
            .buttonStyle(.plain)
            .help(showReplace ? "Hide Replace" : "Show Replace")

            // Search icon
            Image(systemName: "magnifyingglass")
                .foregroundColor(.secondary)
                .font(.system(size: 12))

            // Search text field
            TextField("Find", text: $manager.searchQuery)
                .textFieldStyle(.roundedBorder)
                .controlSize(.small)
                .focused($isSearchFocused)
                .onSubmit {
                    if NSApp.currentEvent?.modifierFlags.contains(.shift) == true {
                        manager.findPrevious()
                    } else {
                        manager.findNext()
                    }
                }
                .onKeyPress(.escape) {
                    manager.hide()
                    return .handled
                }
                .frame(minWidth: 180, maxWidth: 300)

            // Navigation buttons
            HStack(spacing: 2) {
                Button {
                    manager.findPrevious()
                } label: {
                    Image(systemName: "chevron.left")
                        .font(.system(size: 11, weight: .medium))
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
                .disabled(manager.totalMatches == 0)
                .help("Previous Match (Shift+Enter)")
                .keyboardShortcut("g", modifiers: [.command, .shift])

                Button {
                    manager.findNext()
                } label: {
                    Image(systemName: "chevron.right")
                        .font(.system(size: 11, weight: .medium))
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
                .disabled(manager.totalMatches == 0)
                .help("Next Match (Enter)")
                .keyboardShortcut("g", modifiers: .command)
            }

            // Done button
            Button {
                manager.hide()
            } label: {
                Image(systemName: "xmark")
                    .font(.system(size: 10, weight: .semibold))
            }
            .buttonStyle(.bordered)
            .controlSize(.small)
            .help("Close (Escape)")
            .keyboardShortcut(.escape, modifiers: [])

            Spacer()

            // Match count label
            matchCountLabel
                .frame(minWidth: 70, alignment: .trailing)

            // Options button
            optionsMenu
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 6)
    }

    // MARK: - Replace Row

    private var replaceRow: some View {
        HStack(spacing: 8) {
            // Spacer to align with search row
            Color.clear
                .frame(width: 16, height: 16)

            // Replace icon
            Image(systemName: "arrow.left.arrow.right")
                .foregroundColor(.secondary)
                .font(.system(size: 12))

            // Replace text field
            TextField("Replace", text: $manager.replaceQuery)
                .textFieldStyle(.roundedBorder)
                .controlSize(.small)
                .focused($isReplaceFocused)
                .onSubmit {
                    manager.replaceCurrent()
                    manager.findNext()
                }
                .onKeyPress(.escape) {
                    manager.hide()
                    return .handled
                }
                .frame(minWidth: 180, maxWidth: 300)

            // Replace buttons
            HStack(spacing: 4) {
                Button("Replace") {
                    manager.replaceCurrent()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
                .disabled(manager.currentMatchIndex == nil)
                .help("Replace Current Match")

                Button("All") {
                    manager.replaceAll()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
                .disabled(manager.totalMatches == 0)
                .help("Replace All Matches")
            }

            Spacer()
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 6)
        .transition(.opacity.combined(with: .move(edge: .top)))
    }

    // MARK: - Match Count Label

    @ViewBuilder
    private var matchCountLabel: some View {
        if manager.searchQuery.isEmpty {
            Text("")
                .font(.caption)
                .foregroundColor(.secondary)
        } else if manager.totalMatches == 0 {
            Text("No matches")
                .font(.caption)
                .foregroundColor(.secondary)
        } else if let currentIndex = manager.currentMatchIndex {
            Text("\(currentIndex + 1) of \(manager.totalMatches)")
                .font(.caption)
                .foregroundColor(.secondary)
                .monospacedDigit()
        } else {
            Text("\(manager.totalMatches) matches")
                .font(.caption)
                .foregroundColor(.secondary)
                .monospacedDigit()
        }
    }

    // MARK: - Options Menu

    private var optionsMenu: some View {
        Menu {
            Toggle(isOn: $manager.isCaseSensitive) {
                Label("Match Case", systemImage: "textformat")
            }

            Toggle(isOn: $manager.isWholeWord) {
                Label("Whole Word", systemImage: "text.word.spacing")
            }

            Toggle(isOn: $manager.isRegex) {
                Label("Regular Expression", systemImage: "ellipsis.curlybraces")
            }
        } label: {
            HStack(spacing: 4) {
                Text("Options")
                    .font(.caption)
                Image(systemName: "chevron.down")
                    .font(.system(size: 8, weight: .semibold))
            }
            .foregroundColor(.secondary)
        }
        .menuStyle(.borderlessButton)
        .frame(width: 80)
        .help("Search Options")
    }
}

// MARK: - Preview

#Preview("Find Replace Panel") {
    VStack(spacing: 0) {
        FindReplacePanel(manager: {
            let manager = FindReplaceManager()
            manager.searchQuery = "example"
            return manager
        }())

        Divider()

        // Simulated editor content
        Text("This is example content with example text to demonstrate the find replace panel.")
            .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .topLeading)
            .padding()
    }
    .frame(width: 600, height: 300)
}

#Preview("Find Replace Panel - With Matches") {
    VStack(spacing: 0) {
        FindReplacePanel(manager: {
            let manager = FindReplaceManager()
            manager.searchQuery = "test"
            return manager
        }())

        Divider()

        Text("Test content")
            .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .topLeading)
            .padding()
    }
    .frame(width: 600, height: 300)
}

#Preview("Find Replace Panel - With Replace") {
    VStack(spacing: 0) {
        FindReplacePanel(manager: {
            let manager = FindReplaceManager()
            manager.showReplace = true
            return manager
        }())

        Divider()

        Text("Content area")
            .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .topLeading)
            .padding()
    }
    .frame(width: 600, height: 300)
}
