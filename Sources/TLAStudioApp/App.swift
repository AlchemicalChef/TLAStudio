import os
import SourceEditor
import SwiftUI

private let logger = Log.logger(category: "App")

// MARK: - App Entry Point

@main
struct TLAStudioApp: App {

    // Register custom document controller before any documents open
    @NSApplicationDelegateAdaptor(AppDelegate.self) var appDelegate

    var body: some Scene {
        // Settings window only - documents are managed by NSDocumentController
        Settings {
            SettingsView()
        }
        .commands {
            FileCommands()
            EditCommands()
            ViewCommands()
            TLACommands()
            ModelCheckCommands()
            ProofCommands()
            HelpCommands()
        }
    }
}

// MARK: - App Delegate

class AppDelegate: NSObject, NSApplicationDelegate {

    func applicationWillFinishLaunching(_ notification: Notification) {
        logger.info("applicationWillFinishLaunching")
        // Ensure app is a regular foreground app that can receive keyboard input
        NSApp.setActivationPolicy(.regular)

        // Install custom document controller before any documents open
        _ = TLADocumentController()
    }

    func applicationDidFinishLaunching(_ notification: Notification) {
        logger.info("applicationDidFinishLaunching")
        // Setup custom menus (also try here in case init timing was wrong)
        setupModelMenu()

        // Apply saved appearance setting
        applyAppearanceSetting()

        // Observe system appearance changes
        setupAppearanceObserver()

        // Show welcome screen or create new document if none are open
        DispatchQueue.main.async {
            if NSDocumentController.shared.documents.isEmpty {
                let showWelcome = UserDefaults.standard.object(forKey: UserSettings.Keys.showWelcomeOnLaunch) as? Bool ?? true
                if showWelcome {
                    WelcomeWindowController.shared.show()
                } else {
                    NSDocumentController.shared.newDocument(nil)
                }
            }

            // Aggressively activate app and make window key
            NSApp.activate(ignoringOtherApps: true)
            if let window = NSApp.windows.first {
                window.makeKeyAndOrderFront(nil)
            }

            // Activate again after a short delay to ensure it takes effect
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.1) {
                NSApp.activate(ignoringOtherApps: true)
                NSApp.windows.first?.makeKeyAndOrderFront(nil)
            }
        }
    }

    private func applyAppearanceSetting() {
        let appearance = UserDefaults.standard.string(forKey: UserSettings.Keys.appearance) ?? "system"
        let nsAppearance: NSAppearance?

        switch appearance {
        case "light":
            nsAppearance = NSAppearance(named: .aqua)
        case "dark":
            nsAppearance = NSAppearance(named: .darkAqua)
        default:
            nsAppearance = nil // Follow system
        }

        NSApp.appearance = nsAppearance
    }

    private func setupAppearanceObserver() {
        // Observe appearance setting changes
        NotificationCenter.default.addObserver(
            forName: UserDefaults.didChangeNotification,
            object: nil,
            queue: .main
        ) { [weak self] _ in
            self?.applyAppearanceSetting()
        }
    }

    private func setupModelMenu() {
        guard let mainMenu = NSApp.mainMenu else {
            return
        }

        // Avoid adding duplicate menu
        if mainMenu.item(withTitle: "Model") != nil {
            return
        }

        // Create Model menu
        let modelMenu = NSMenu(title: "Model")

        let runTLCItem = NSMenuItem(title: "Run TLC", action: #selector(runTLC(_:)), keyEquivalent: "r")
        runTLCItem.keyEquivalentModifierMask = .command
        runTLCItem.target = self
        modelMenu.addItem(runTLCItem)

        let stopTLCItem = NSMenuItem(title: "Stop TLC", action: #selector(stopTLC(_:)), keyEquivalent: ".")
        stopTLCItem.keyEquivalentModifierMask = .command
        stopTLCItem.target = self
        modelMenu.addItem(stopTLCItem)

        let modelMenuItem = NSMenuItem(title: "Model", action: nil, keyEquivalent: "")
        modelMenuItem.submenu = modelMenu

        // Insert before Window menu (usually second to last)
        let insertIndex = max(mainMenu.items.count - 2, 0)
        mainMenu.insertItem(modelMenuItem, at: insertIndex)
    }

    @objc func runTLC(_ sender: Any?) {
        Task { @MainActor in
            if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                doc.runModelCheck()
            }
        }
    }

    @objc func stopTLC(_ sender: Any?) {
        Task { @MainActor in
            if let doc = NSDocumentController.shared.currentDocument as? TLADocument {
                doc.stopModelCheck()
            }
        }
    }

    func applicationShouldOpenUntitledFile(_ sender: NSApplication) -> Bool {
        // Create new document on launch if none open
        true
    }

    func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool {
        // Standard macOS behavior for document apps
        false
    }

    func applicationOpenUntitledFile(_ sender: NSApplication) -> Bool {
        NSDocumentController.shared.newDocument(nil)
        return true
    }

    func applicationShouldTerminate(_ sender: NSApplication) -> NSApplication.TerminateReply {
        // Check if any documents have running TLC or proof sessions
        let documents = NSDocumentController.shared.documents.compactMap { $0 as? TLADocument }
        let hasRunningSessions = documents.contains { doc in
            (doc.tlcSession?.isRunning ?? false) || (doc.proofSession?.isRunning ?? false)
        }

        if hasRunningSessions {
            // Stop all running sessions gracefully with proper async coordination
            Task { @MainActor in
                // Stop all document sessions concurrently
                await withTaskGroup(of: Void.self) { group in
                    for doc in documents {
                        group.addTask {
                            await doc.stopModelCheckAsync()
                        }
                        group.addTask {
                            await doc.stopProofCheckAsync()
                        }
                    }
                }

                // Also stop all processes at the manager level
                await TLCProcessManager.shared.stopAll()
                await TLAPMProcessManager.shared.stopAll()

                // Clean up all active trace files
                await TraceStorageManager.shared.cleanupAllActiveTraces()
                await TraceStorageManager.shared.cleanupStaleTraces()

                // Final synchronous cleanup - terminateAll now properly kills process trees
                ProcessRegistry.shared.terminateAll()

                // Now terminate
                NSApp.reply(toApplicationShouldTerminate: true)
            }

            return .terminateLater
        }

        // Clean up stale trace files even if no sessions running
        Task {
            await TraceStorageManager.shared.cleanupStaleTraces()
        }

        // Synchronous process cleanup even when no sessions appear to be running
        // (catches edge cases where session state is out of sync with actual processes)
        ProcessRegistry.shared.terminateAll()

        return .terminateNow
    }

    func applicationWillTerminate(_ notification: Notification) {
        // Final synchronous cleanup - ensure all processes and their children are terminated
        // This catches any processes that might have been missed by async cleanup
        // The terminateAll() method now properly kills process trees with SIGKILL fallback
        ProcessRegistry.shared.terminateAll()
    }
}

// MARK: - Settings View

struct SettingsView: View {
    var body: some View {
        TabView {
            GeneralSettingsView()
                .tabItem { Label("General", systemImage: "gear") }

            EditorSettingsView()
                .tabItem { Label("Editor", systemImage: "doc.text") }

            ProverSettingsView()
                .tabItem { Label("Provers", systemImage: "checkmark.seal") }
        }
        .frame(width: 650, height: 600)
    }
}

// GeneralSettingsView is defined in Settings/GeneralSettingsView.swift
// EditorSettingsView is defined in Settings/EditorSettingsView.swift
// ProverSettingsView is defined in Settings/ProverSettingsView.swift
