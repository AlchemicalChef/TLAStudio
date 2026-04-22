import SwiftUI

// MARK: - Welcome View

/// Welcome screen shown on first launch
struct WelcomeView: View {
    @AppStorage(UserSettings.Keys.showWelcomeOnLaunch) private var showWelcomeOnLaunch = true

    /// Close the welcome window (dismiss() doesn't work in NSHostingView-hosted views)
    private func closeWindow() {
        WelcomeWindowController.shared.window?.close()
    }

    var body: some View {
        VStack(spacing: 0) {
            // Header
            VStack(spacing: 12) {
                Image(systemName: "doc.text.magnifyingglass")
                    .font(.system(size: 48))
                    .foregroundColor(.accentColor)

                Text("Welcome to TLA+ Studio")
                    .font(.title.bold())

                Text("A native macOS IDE for TLA+ specifications")
                    .font(.subheadline)
                    .foregroundColor(.secondary)
            }
            .padding(.top, 24)
            .padding(.bottom, 16)

            Divider()

            // Two-column layout: Templates + Recent Files
            HStack(alignment: .top, spacing: 0) {
                // Left: Template gallery
                VStack(alignment: .leading, spacing: 0) {
                    Text("New from Template")
                        .font(.headline)
                        .padding(.horizontal, 16)
                        .padding(.top, 12)
                        .padding(.bottom, 8)

                    ScrollView {
                        VStack(alignment: .leading, spacing: 12) {
                            ForEach(DocumentTemplate.grouped, id: \.category) { group in
                                VStack(alignment: .leading, spacing: 6) {
                                    Text(group.category)
                                        .font(.caption.bold())
                                        .foregroundColor(.secondary)
                                        .textCase(.uppercase)

                                    LazyVGrid(columns: [
                                        GridItem(.flexible(), spacing: 8),
                                        GridItem(.flexible(), spacing: 8)
                                    ], spacing: 8) {
                                        ForEach(group.templates, id: \.rawValue) { template in
                                            TemplateCard(template: template) {
                                                closeWindow()
                                                if let controller = NSDocumentController.shared as? TLADocumentController {
                                                    controller.newDocument(from: template)
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        .padding(.horizontal, 16)
                        .padding(.bottom, 12)
                    }
                }
                .frame(maxWidth: .infinity)

                Divider()

                // Right: Recent files + Quick actions
                VStack(alignment: .leading, spacing: 0) {
                    // Quick actions
                    HStack(spacing: 8) {
                        Button {
                            closeWindow()
                            NSDocumentController.shared.newDocument(nil)
                        } label: {
                            Label("New", systemImage: "doc.badge.plus")
                        }
                        .keyboardShortcut("n")

                        Button {
                            closeWindow()
                            NSDocumentController.shared.openDocument(nil)
                        } label: {
                            Label("Open", systemImage: "folder")
                        }
                        .keyboardShortcut("o")
                    }
                    .padding(.horizontal, 16)
                    .padding(.top, 12)
                    .padding(.bottom, 8)

                    Text("Recent Files")
                        .font(.headline)
                        .padding(.horizontal, 16)
                        .padding(.bottom, 8)

                    let recentURLs = NSDocumentController.shared.recentDocumentURLs

                    if recentURLs.isEmpty {
                        Text("No recent files")
                            .foregroundColor(.secondary)
                            .font(.caption)
                            .padding(.horizontal, 16)
                        Spacer()
                    } else {
                        ScrollView {
                            VStack(alignment: .leading, spacing: 2) {
                                ForEach(recentURLs, id: \.absoluteString) { url in
                                    RecentFileRow(url: url) {
                                        closeWindow()
                                        NSDocumentController.shared.openDocument(
                                            withContentsOf: url, display: true
                                        ) { _, _, _ in }
                                    }
                                }
                            }
                            .padding(.horizontal, 8)
                        }
                    }
                }
                .frame(width: 220)
            }

            Divider()

            // Footer
            HStack {
                Toggle("Show this window on startup", isOn: $showWelcomeOnLaunch)
                    .toggleStyle(.checkbox)

                Spacer()

                Button("Get Started") {
                    closeWindow()
                    NSDocumentController.shared.newDocument(nil)
                }
                .buttonStyle(.borderedProminent)
            }
            .padding(.horizontal, 24)
            .padding(.vertical, 12)
        }
        .frame(width: 700, height: 550)
        .background(Color(NSColor.windowBackgroundColor))
    }
}

// MARK: - Welcome Action Button

private struct WelcomeActionButton: View {
    let icon: String
    let title: String
    let description: String
    let shortcut: String?
    let action: () -> Void

    @State private var isHovered = false

    var body: some View {
        Button(action: action) {
            HStack(spacing: 16) {
                Image(systemName: icon)
                    .font(.title2)
                    .foregroundColor(.accentColor)
                    .frame(width: 32)

                VStack(alignment: .leading, spacing: 2) {
                    Text(title)
                        .font(.body.bold())
                        .foregroundColor(.primary)

                    Text(description)
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                Spacer()

                if let shortcut = shortcut {
                    Text("\u{2318}\(shortcut)")
                        .font(.caption.monospaced())
                        .foregroundColor(.secondary)
                        .padding(.horizontal, 6)
                        .padding(.vertical, 2)
                        .background(Color.secondary.opacity(0.1))
                        .cornerRadius(4)
                }
            }
            .padding(.horizontal, 24)
            .padding(.vertical, 12)
            .background(isHovered ? Color.accentColor.opacity(0.1) : Color.clear)
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .onHover { hovering in
            isHovered = hovering
        }
    }
}

// MARK: - Template Card

private struct TemplateCard: View {
    let template: DocumentTemplate
    let action: () -> Void

    @State private var isHovered = false

    var body: some View {
        Button(action: action) {
            HStack(spacing: 8) {
                Image(systemName: template.icon)
                    .font(.title3)
                    .foregroundColor(.accentColor)
                    .frame(width: 24)

                VStack(alignment: .leading, spacing: 1) {
                    Text(template.displayName)
                        .font(.caption.bold())
                        .foregroundColor(.primary)
                        .lineLimit(1)

                    Text(template.description)
                        .font(.caption2)
                        .foregroundColor(.secondary)
                        .lineLimit(1)
                }
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(8)
            .background(isHovered ? Color.accentColor.opacity(0.1) : Color(NSColor.controlBackgroundColor))
            .cornerRadius(6)
        }
        .buttonStyle(.plain)
        .onHover { hovering in
            isHovered = hovering
        }
    }
}

// MARK: - Recent File Row

private struct RecentFileRow: View {
    let url: URL
    let action: () -> Void

    @State private var isHovered = false

    var body: some View {
        Button(action: action) {
            VStack(alignment: .leading, spacing: 1) {
                Text(url.deletingPathExtension().lastPathComponent)
                    .font(.caption.bold())
                    .foregroundColor(.primary)
                    .lineLimit(1)

                Text(url.deletingLastPathComponent().path.replacingOccurrences(of: NSHomeDirectory(), with: "~"))
                    .font(.caption2)
                    .foregroundColor(.secondary)
                    .lineLimit(1)
            }
            .frame(maxWidth: .infinity, alignment: .leading)
            .padding(.horizontal, 8)
            .padding(.vertical, 4)
            .background(isHovered ? Color.accentColor.opacity(0.1) : Color.clear)
            .cornerRadius(4)
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .onHover { hovering in
            isHovered = hovering
        }
    }
}

// MARK: - Welcome Window Controller

final class WelcomeWindowController: NSWindowController {

    static let shared = WelcomeWindowController()

    private init() {
        let window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 700, height: 550),
            styleMask: [.titled, .closable, .fullSizeContentView],
            backing: .buffered,
            defer: false
        )
        window.titlebarAppearsTransparent = true
        window.titleVisibility = .hidden
        window.isMovableByWindowBackground = true
        window.center()

        super.init(window: window)

        let hostingView = NSHostingView(rootView: WelcomeView())
        window.contentView = hostingView
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    func show() {
        window?.center()
        window?.makeKeyAndOrderFront(nil)
        NSApp.activate(ignoringOtherApps: true)
    }
}

// MARK: - Preview

#if DEBUG
struct WelcomeView_Previews: PreviewProvider {
    static var previews: some View {
        WelcomeView()
    }
}
#endif
