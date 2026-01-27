import SwiftUI

// MARK: - Welcome View

/// Welcome screen shown on first launch
struct WelcomeView: View {
    @Environment(\.dismiss) private var dismiss
    @AppStorage("showWelcomeOnLaunch") private var showWelcomeOnLaunch = true

    var body: some View {
        VStack(spacing: 0) {
            // Header
            VStack(spacing: 16) {
                Image(systemName: "doc.text.magnifyingglass")
                    .font(.system(size: 64))
                    .foregroundColor(.accentColor)

                Text("Welcome to TLA+ Studio")
                    .font(.largeTitle.bold())

                Text("A native macOS IDE for TLA+ specifications")
                    .font(.title3)
                    .foregroundColor(.secondary)
            }
            .padding(.top, 40)
            .padding(.bottom, 32)

            Divider()

            // Quick actions
            VStack(alignment: .leading, spacing: 0) {
                Text("Get Started")
                    .font(.headline)
                    .padding(.horizontal, 24)
                    .padding(.top, 20)
                    .padding(.bottom, 12)

                WelcomeActionButton(
                    icon: "doc.badge.plus",
                    title: "New Specification",
                    description: "Create a new TLA+ specification from scratch",
                    shortcut: "N"
                ) {
                    dismiss()
                    NSDocumentController.shared.newDocument(nil)
                }

                WelcomeActionButton(
                    icon: "folder",
                    title: "Open Specification",
                    description: "Open an existing .tla file",
                    shortcut: "O"
                ) {
                    dismiss()
                    NSDocumentController.shared.openDocument(nil)
                }

                WelcomeActionButton(
                    icon: "doc.on.doc",
                    title: "Open Recent",
                    description: "Open a recently edited specification",
                    shortcut: nil
                ) {
                    // Show recent documents menu
                    if let recentURLs = NSDocumentController.shared.recentDocumentURLs.first {
                        dismiss()
                        NSDocumentController.shared.openDocument(withContentsOf: recentURLs, display: true) { _, _, _ in }
                    }
                }
            }

            Divider()
                .padding(.top, 16)

            // Features overview
            VStack(alignment: .leading, spacing: 0) {
                Text("Features")
                    .font(.headline)
                    .padding(.horizontal, 24)
                    .padding(.top, 20)
                    .padding(.bottom, 12)

                ScrollView(.horizontal, showsIndicators: false) {
                    HStack(spacing: 16) {
                        FeatureCard(
                            icon: "play.fill",
                            title: "Model Checking",
                            description: "Run TLC to verify your specifications"
                        )

                        FeatureCard(
                            icon: "checkmark.seal",
                            title: "Proof Verification",
                            description: "Check proofs with TLAPS"
                        )

                        FeatureCard(
                            icon: "arrow.triangle.2.circlepath",
                            title: "PlusCal Translation",
                            description: "Translate PlusCal algorithms to TLA+"
                        )

                        FeatureCard(
                            icon: "text.magnifyingglass",
                            title: "Syntax Highlighting",
                            description: "Rich editor with TLA+ syntax support"
                        )
                    }
                    .padding(.horizontal, 24)
                }
            }

            Spacer()

            // Footer
            HStack {
                Toggle("Show this window on startup", isOn: $showWelcomeOnLaunch)
                    .toggleStyle(.checkbox)

                Spacer()

                Button("Get Started") {
                    dismiss()
                    NSDocumentController.shared.newDocument(nil)
                }
                .buttonStyle(.borderedProminent)
            }
            .padding(24)
        }
        .frame(width: 600, height: 550)
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

// MARK: - Feature Card

private struct FeatureCard: View {
    let icon: String
    let title: String
    let description: String

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            Image(systemName: icon)
                .font(.title)
                .foregroundColor(.accentColor)

            Text(title)
                .font(.headline)

            Text(description)
                .font(.caption)
                .foregroundColor(.secondary)
                .lineLimit(2)
        }
        .frame(width: 140, alignment: .leading)
        .padding(12)
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(8)
    }
}

// MARK: - Welcome Window Controller

final class WelcomeWindowController: NSWindowController {

    static let shared = WelcomeWindowController()

    private init() {
        let window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 600, height: 550),
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

    func showIfNeeded() {
        let showWelcome = UserDefaults.standard.bool(forKey: "showWelcomeOnLaunch")
        // Default to true if not set
        if !UserDefaults.standard.bool(forKey: "welcomeShownBefore") {
            UserDefaults.standard.set(true, forKey: "showWelcomeOnLaunch")
            UserDefaults.standard.set(true, forKey: "welcomeShownBefore")
            show()
        } else if showWelcome {
            show()
        }
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
