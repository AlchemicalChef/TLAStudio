import os
import SourceEditor
import SwiftUI

private let logger = Log.logger(category: "App")

// MARK: - App Entry Point

@main
struct TLAStudioApp: App {

    @NSApplicationDelegateAdaptor(AppDelegate.self) var appDelegate

    init() {
        // The FIRST NSDocumentController instantiated becomes `shared`, and
        // SwiftUI creates a vanilla one during scene setup — before any app
        // delegate callback. Instantiating ours here (App.init runs first) is
        // the only way it actually becomes the shared controller; doing it in
        // applicationWillFinishLaunching was provably too late, leaving every
        // TLADocumentController override dead — template creation, recents
        // filtering, the custom open panel (platform review 2026-06-10).
        _ = TLADocumentController()
    }

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

    private func presentInitialInterfaceIfNeeded() {
        // `odoc` opens and draft restoration both add documents asynchronously
        // around launch; checking `documents` alone raced them and spawned
        // phantom Untitled documents (platform review 2026-06-10). A visible
        // window also counts as "interface present".
        guard NSDocumentController.shared.documents.isEmpty,
              !NSApp.windows.contains(where: { $0.isVisible }) else {
            return
        }

        if UserSettings.shared.showWelcomeOnLaunch {
            WelcomeWindowController.shared.show()
        } else {
            NSDocumentController.shared.newDocument(nil)
        }
    }

    func applicationWillFinishLaunching(_ notification: Notification) {
        logger.info("applicationWillFinishLaunching")
        // Ensure app is a regular foreground app that can receive keyboard input
        NSApp.setActivationPolicy(.regular)

        // The custom document controller is installed in TLAStudioApp.init()
        // — by this point SwiftUI has already created a vanilla controller,
        // so installing here would silently fail to become `shared`.
        assert(NSDocumentController.shared is TLADocumentController,
               "TLADocumentController must be installed before SwiftUI scene setup")
    }

    func applicationDidFinishLaunching(_ notification: Notification) {
        logger.info("applicationDidFinishLaunching")

        // Apply saved appearance setting
        applyAppearanceSetting()

        // Observe system appearance changes
        setupAppearanceObserver()

        // Fire-and-forget sweep of orphaned archive-extraction staging dirs
        // left behind by SIGKILL or crashes during prior runs. SafeArchiveExtractor
        // gates removal on a 24h mtime cutoff to avoid racing concurrent extractions.
        Task.detached(priority: .background) {
            SafeArchiveExtractor.cleanupStaleStagingDirs()
        }

        // Welcome-or-untitled decision, deferred long enough for launch-time
        // document opens to land: the odoc for `open App file` can arrive as
        // a separate event seconds into a cold start. The guards inside
        // (documents.isEmpty + no visible window) make a late fire harmless.
        DispatchQueue.main.asyncAfter(deadline: .now() + 2.0) {
            self.presentInitialInterfaceIfNeeded()
        }

        DispatchQueue.main.async {
            // Prime the parser off the first edit so initial completions/highlighting
            // do not also pay the language-core startup cost.
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.25) {
                TLACoreWrapper.shared.primeForEditing()
            }

            // Activate and focus the first window. `WelcomeWindowController.show()` and
            // `TLAWindowController.init` each also call `NSApp.activate(...)`, so one call
            // here is enough — earlier code retried after 100ms to paper over a cold-start
            // race that no longer exists.
            NSApp.activate(ignoringOtherApps: true)
            NSApp.windows.first?.makeKeyAndOrderFront(nil)

            // First-launch proof-dependency check. Deferred briefly so it surfaces on top
            // of the welcome window / initial document rather than racing them. No-ops on
            // every launch after the first, when fully set up, or once dismissed.
            DispatchQueue.main.asyncAfter(deadline: .now() + 0.6) {
                ProofSetupCoordinator.shared.maybePresentOnLaunch()
            }
        }
    }

    private func applyAppearanceSetting() {
        let appearance = UserSettings.shared.appearance
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

    func applicationShouldOpenUntitledFile(_ sender: NSApplication) -> Bool {
        // Always false: `open -a App file` can deliver the odoc as a SECOND
        // Apple event after launch, so AppKit's "no documents at launch"
        // signal fires before the document arrives and would spawn a phantom
        // Untitled next to it (verified empirically, platform review). The
        // welcome-or-untitled decision is made by the deferred check in
        // applicationDidFinishLaunching instead.
        false
    }

    func applicationShouldTerminateAfterLastWindowClosed(_ sender: NSApplication) -> Bool {
        // Standard macOS behavior for document apps
        false
    }

    func applicationShouldHandleReopen(_ sender: NSApplication, hasVisibleWindows flag: Bool) -> Bool {
        if !flag {
            presentInitialInterfaceIfNeeded()
        }
        return true
    }

    /// Wall-clock deadline for the async `applicationShouldTerminate` cleanup pass.
    /// Past this point we force a reply so the dock app doesn't linger in
    /// `terminateLater` waiting on a wedged subprocess or a stalled FS unlink.
    private static let terminationDeadlineSeconds: Double = 5.0

    func applicationShouldTerminate(_ sender: NSApplication) -> NSApplication.TerminateReply {
        // Check if any documents have running TLC or proof sessions
        let documents = NSDocumentController.shared.documents.compactMap { $0 as? TLADocument }
        let hasRunningSessions = documents.contains { doc in
            (doc.tlcSession?.isRunning ?? false) || (doc.proofSession?.isRunning ?? false)
        }

        // Both branches need active-trace cleanup (LazyErrorTrace.pendingCleanupIds is
        // in-memory and otherwise survives until the 24h stale sweep). The .terminateNow
        // branch used to skip cleanupAllActiveTraces entirely; .terminateLater needs an
        // overall wall-clock deadline so the dock app doesn't pin in terminateLater
        // waiting on a wedged subprocess or stalled NFS unlink.
        Task { @MainActor in
            let cleanupTask: Task<Void, Never> = Task { @MainActor in
                if hasRunningSessions {
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
                }

                // Clean up all active trace files (drains LazyErrorTrace.pendingCleanupIds
                // as a side effect). Always do this, even when no sessions are running —
                // the user may have closed every model-check view without starting a new
                // one, leaving pending IDs queued in memory.
                await TraceStorageManager.shared.cleanupAllActiveTraces()
                await TraceStorageManager.shared.cleanupStaleTraces()

                // Final synchronous cleanup - terminateAll now properly kills process trees
                ProcessRegistry.shared.terminateAll()
            }

            // Race the cleanup against a wall-clock deadline. Whichever finishes first
            // is "the answer"; we always reply true so the app proceeds to
            // applicationWillTerminate, which performs a synchronous best-effort fallback.
            let deadlineTask: Task<Void, Never> = Task {
                try? await Task.sleep(nanoseconds: UInt64(Self.terminationDeadlineSeconds * 1_000_000_000))
            }

            await withTaskGroup(of: Void.self) { group in
                group.addTask { await cleanupTask.value }
                group.addTask { await deadlineTask.value }
                _ = await group.next()
                group.cancelAll()
            }

            // Cooperative cancel — `cleanupTask` itself does not poll Task.isCancelled
            // (it sits in synchronous ProcessRegistry/actor calls), so this is
            // best-effort. The synchronous `applicationWillTerminate` path picks up any
            // leftover LazyErrorTrace pending IDs as the fallback.
            cleanupTask.cancel()
            deadlineTask.cancel()

            NSApp.reply(toApplicationShouldTerminate: true)
        }

        return .terminateLater
    }

    func applicationWillTerminate(_ notification: Notification) {
        // Final synchronous cleanup - ensure all processes and their children are terminated.
        // This catches any processes that might have been missed by async cleanup.
        // The terminateAll() method now properly kills process trees with SIGKILL fallback.
        ProcessRegistry.shared.terminateAll()

        // Synchronously drain any LazyErrorTrace cleanup IDs that the async terminateLater
        // Task did not reach (e.g., it hit the wall-clock deadline). The IDs are
        // in-memory only — if we don't act here they vanish until the next 24h stale
        // sweep. We use plain FileManager rather than entering the TraceStorageManager
        // actor because we cannot await from this synchronous callback.
        let pending = LazyErrorTrace.drainPendingCleanup()
        guard !pending.isEmpty else { return }
        let tracesDir = TraceStorageManager.tracesDirectory
        let fm = FileManager.default
        for sessionId in pending {
            let traceURL = tracesDir.appendingPathComponent("\(sessionId.uuidString).trace")
            try? fm.removeItem(at: traceURL)
        }
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
