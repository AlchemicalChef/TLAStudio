import AppKit
import os
import SwiftUI

private let logger = Log.logger(category: "ProofSetup")

// MARK: - Dependency Model

/// How a proof backend is obtained.
enum ProofToolKind {
    /// Ships inside the .app bundle — always present in a healthy install.
    case bundled
    /// Not bundled, but can be downloaded and installed from within the app (Isabelle).
    case downloadable
    /// Not bundled and not auto-installable — the user must install it manually (SPASS).
    case manual
}

/// How important a backend is for everyday proofs.
enum ProofToolRole {
    /// Required for the vast majority of TLAPS proofs (TLAPM, Z3, Zenon).
    case core
    /// Only used by some obligations; proofs work without it.
    case optional
}

/// Availability snapshot for a single proof backend.
struct ProofToolStatus: Identifiable {
    let id: String
    let name: String
    let detail: String
    let role: ProofToolRole
    let kind: ProofToolKind
    let isAvailable: Bool
}

/// Aggregate report describing the readiness of the whole proof toolchain.
struct ProofDependencyReport {
    let tools: [ProofToolStatus]

    var readyCount: Int { tools.filter(\.isAvailable).count }
    var totalCount: Int { tools.count }

    /// Backends that are missing but can be installed in-app (Isabelle).
    var missingDownloadable: [ProofToolStatus] {
        tools.filter { !$0.isAvailable && $0.kind == .downloadable }
    }

    /// Every core backend resolves to an executable.
    var allCoreReady: Bool {
        tools.filter { $0.role == .core }.allSatisfy(\.isAvailable)
    }

    /// There is something worth prompting the user about: either an installable gap
    /// we can fill (Isabelle) or a broken core backend we should warn about.
    var shouldPrompt: Bool {
        !missingDownloadable.isEmpty || !allCoreReady
    }
}

// MARK: - Dependency Checker

/// Fast, synchronous availability checks for the proof toolchain.
///
/// Deliberately avoids spawning `--version` subprocesses (that lives in the Prover
/// settings "Verify" action): this runs on launch and before the first proof, so it
/// only does filesystem existence/executable checks via the same resolution the proof
/// runner uses (`UserSettings.resolved*Path` + `BinaryDiscovery`).
enum ProofDependencyChecker {

    private static func isExecutable(_ path: String) -> Bool {
        !path.isEmpty && FileManager.default.isExecutableFile(atPath: path)
    }

    /// Whether Isabelle resolves either from a user-configured path or the in-app install.
    @MainActor
    static func isIsabelleAvailable() -> Bool {
        let fm = FileManager.default

        // In-app download location (canonical for the install flow).
        if fm.isExecutableFile(atPath: IsabelleDownloader.shared.isabelleBinaryPath.path) {
            return true
        }

        // User-configured path: may point at the install dir or the binary itself.
        let configured = UserSettings.shared.isabellePath.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !configured.isEmpty else { return false }
        if fm.isExecutableFile(atPath: configured) {
            return true
        }
        let nested = URL(fileURLWithPath: configured).appendingPathComponent("bin/isabelle").path
        return fm.isExecutableFile(atPath: nested)
    }

    @MainActor
    static func current() -> ProofDependencyReport {
        let settings = UserSettings.shared

        let ls4 = BinaryDiscovery.find(
            named: "ls4",
            options: .init(
                bundleSubdirectories: ["Provers", "bin", "lib/tlapm/backends/bin"],
                homeRelativePaths: [".tla/provers", ".tla"]
            )
        ) != nil

        let tools: [ProofToolStatus] = [
            ProofToolStatus(
                id: "tlapm",
                name: "TLAPM",
                detail: "The TLAPS proof manager — orchestrates every proof.",
                role: .core,
                kind: .bundled,
                isAvailable: isExecutable(settings.resolvedTLAPMPath)
            ),
            ProofToolStatus(
                id: "z3",
                name: "Z3",
                detail: "SMT solver — the default backend for most obligations.",
                role: .core,
                kind: .bundled,
                isAvailable: isExecutable(settings.resolvedZ3Path)
            ),
            ProofToolStatus(
                id: "zenon",
                name: "Zenon",
                detail: "First-order theorem prover bundled with TLAPS.",
                role: .core,
                kind: .bundled,
                isAvailable: isExecutable(settings.resolvedZenonPath)
            ),
            ProofToolStatus(
                id: "cvc5",
                name: "CVC5",
                detail: "Secondary SMT solver for obligations Z3 can't close.",
                role: .optional,
                kind: .bundled,
                isAvailable: isExecutable(settings.resolvedCvc5Path)
            ),
            ProofToolStatus(
                id: "ls4",
                name: "LS4",
                detail: "Temporal (PTL) prover for liveness obligations.",
                role: .optional,
                kind: .bundled,
                isAvailable: ls4
            ),
            ProofToolStatus(
                id: "isabelle",
                name: "Isabelle",
                detail: "Proof assistant backend. Optional, ~1 GB download / ~3 GB installed.",
                role: .optional,
                kind: .downloadable,
                isAvailable: isIsabelleAvailable()
            ),
            ProofToolStatus(
                id: "spass",
                name: "SPASS",
                detail: "First-order prover. Rarely used; install manually if needed.",
                role: .optional,
                kind: .manual,
                isAvailable: isExecutable(settings.resolvedSpassPath)
            )
        ]

        return ProofDependencyReport(tools: tools)
    }
}

// MARK: - Coordinator

/// Decides when to surface the proof-setup prompt and persists the "seen / never ask"
/// state. Two triggers per the product decision: once on first launch, and again before
/// the first proof run — each suppressible, with a permanent "Don't ask again".
@MainActor
final class ProofSetupCoordinator {
    static let shared = ProofSetupCoordinator()

    private var presentedThisSession = false

    private init() {}

    /// Present the prompt the first time the app launches (only if something is actionable).
    func maybePresentOnLaunch() {
        let settings = UserSettings.shared
        guard !settings.proofSetupNeverAsk, !settings.proofSetupLaunchPromptShown else { return }

        let report = ProofDependencyChecker.current()
        // Record that we evaluated the launch trigger regardless, so a fully-ready install
        // never re-checks on every subsequent launch.
        settings.proofSetupLaunchPromptShown = true
        guard report.shouldPrompt else {
            logger.info("Proof toolchain ready on launch; no setup prompt needed")
            return
        }
        present(report: report, reason: "launch")
    }

    /// Present the prompt the first time the user runs a proof, if still actionable.
    /// Non-blocking: the proof itself still proceeds with whatever backends are present.
    func maybePresentBeforeFirstProof() {
        let settings = UserSettings.shared
        guard !settings.proofSetupNeverAsk,
              !settings.proofSetupProofPromptShown,
              !presentedThisSession else { return }

        let report = ProofDependencyChecker.current()
        // Unlike the launch trigger, only consume this trigger when we actually present.
        // If the first proof runs with a healthy toolchain we leave the flag unset, so a
        // *later* loss of a backend (e.g. the user deletes the Isabelle install) still
        // surfaces the prompt once before a subsequent proof.
        guard report.shouldPrompt else { return }
        settings.proofSetupProofPromptShown = true
        present(report: report, reason: "first-proof")
    }

    /// Open the panel on demand (e.g. from a menu item), bypassing the "seen" flags.
    func presentManually() {
        present(report: ProofDependencyChecker.current(), reason: "manual")
    }

    private func present(report: ProofDependencyReport, reason: String) {
        presentedThisSession = true
        logger.info("Presenting proof setup (\(reason, privacy: .public)): \(report.readyCount)/\(report.totalCount) ready")
        ProofSetupWindowController.shared.show(report: report)
    }
}

// MARK: - Window Controller

/// Hosts `ProofSetupView` in a standalone panel, mirroring `WelcomeWindowController`.
@MainActor
final class ProofSetupWindowController: NSWindowController {
    static let shared = ProofSetupWindowController()

    private init() {
        let window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 560, height: 560),
            styleMask: [.titled, .closable, .fullSizeContentView],
            backing: .buffered,
            defer: false
        )
        window.titlebarAppearsTransparent = true
        window.titleVisibility = .hidden
        window.isMovableByWindowBackground = true
        window.title = "Proof System Setup"
        window.center()
        super.init(window: window)
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    func show(report: ProofDependencyReport) {
        let view = ProofSetupView(report: report) { [weak self] in
            self?.window?.close()
        }
        window?.contentView = NSHostingView(rootView: view)
        window?.center()
        window?.makeKeyAndOrderFront(nil)
        NSApp.activate(ignoringOtherApps: true)
    }
}

// MARK: - View

struct ProofSetupView: View {
    let report: ProofDependencyReport
    let onClose: () -> Void

    @ObservedObject private var downloader = IsabelleDownloader.shared

    private var isabelleMissing: Bool {
        report.tools.contains { $0.id == "isabelle" && !$0.isAvailable } && !downloader.state.isInstalled
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            header
            Divider()
            ScrollView {
                VStack(alignment: .leading, spacing: 10) {
                    ForEach(report.tools) { tool in
                        toolRow(tool)
                    }
                }
                .padding(20)
            }
            Divider()
            footer
        }
        .frame(width: 560, height: 560)
    }

    // MARK: Header

    private var header: some View {
        HStack(alignment: .top, spacing: 14) {
            Image(systemName: "checkmark.seal.fill")
                .font(.system(size: 34))
                .foregroundStyle(.tint)
            VStack(alignment: .leading, spacing: 4) {
                Text("Proof System Setup")
                    .font(.title2).bold()
                Text(summaryLine)
                    .font(.subheadline)
                    .foregroundStyle(.secondary)
            }
            Spacer()
        }
        .padding(20)
    }

    private var summaryLine: String {
        if report.allCoreReady {
            return "\(report.readyCount) of \(report.totalCount) backends ready. Core proving works out of the box; optional backends are listed below."
        }
        return "\(report.readyCount) of \(report.totalCount) backends ready. Some core backends are missing — check Prover settings or reinstall."
    }

    // MARK: Tool row

    @ViewBuilder
    private func toolRow(_ tool: ProofToolStatus) -> some View {
        HStack(alignment: .top, spacing: 12) {
            statusIcon(for: tool)
                .frame(width: 22)

            VStack(alignment: .leading, spacing: 2) {
                HStack(spacing: 6) {
                    Text(tool.name).font(.headline)
                    roleTag(tool)
                }
                Text(tool.detail)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                    .fixedSize(horizontal: false, vertical: true)

                if tool.id == "isabelle" {
                    isabelleControls(tool)
                        .padding(.top, 4)
                } else if tool.kind == .manual && !tool.isAvailable {
                    manualControls
                        .padding(.top, 4)
                }
            }
            Spacer()
        }
        .padding(12)
        .background(RoundedRectangle(cornerRadius: 8).fill(Color(nsColor: .controlBackgroundColor)))
    }

    @ViewBuilder
    private func statusIcon(for tool: ProofToolStatus) -> some View {
        if tool.isAvailable || (tool.id == "isabelle" && downloader.state.isInstalled) {
            Image(systemName: "checkmark.circle.fill").foregroundStyle(.green)
        } else if tool.role == .core {
            Image(systemName: "exclamationmark.triangle.fill").foregroundStyle(.orange)
        } else if tool.kind == .downloadable {
            Image(systemName: "arrow.down.circle").foregroundStyle(.blue)
        } else {
            Image(systemName: "minus.circle").foregroundStyle(.secondary)
        }
    }

    @ViewBuilder
    private func roleTag(_ tool: ProofToolStatus) -> some View {
        let label = tool.role == .core ? "Required" : "Optional"
        Text(label)
            .font(.caption2).bold()
            .padding(.horizontal, 6).padding(.vertical, 1)
            .background(
                Capsule().fill(
                    (tool.role == .core ? Color.accentColor : Color.secondary).opacity(0.15)
                )
            )
            .foregroundStyle(tool.role == .core ? Color.accentColor : Color.secondary)
    }

    // MARK: Isabelle controls

    @ViewBuilder
    private func isabelleControls(_ tool: ProofToolStatus) -> some View {
        switch downloader.state {
        case .installed:
            Label("Installed", systemImage: "checkmark")
                .font(.caption).foregroundStyle(.green)
        case .downloading(let progress):
            VStack(alignment: .leading, spacing: 3) {
                ProgressView(value: progress).frame(maxWidth: 320)
                HStack {
                    Text(downloader.formattedProgress).font(.caption2).foregroundStyle(.secondary)
                    Button("Cancel") { downloader.cancel() }
                        .controlSize(.small)
                }
            }
        case .extracting, .checking:
            HStack(spacing: 6) {
                ProgressView().controlSize(.small)
                Text(downloader.state == .extracting ? "Installing…" : "Checking…")
                    .font(.caption).foregroundStyle(.secondary)
            }
        case .error(let message):
            VStack(alignment: .leading, spacing: 3) {
                Text(message).font(.caption).foregroundStyle(.red).lineLimit(3)
                Button("Retry Download") { downloader.download() }
                    .controlSize(.small)
            }
        case .notInstalled:
            if !tool.isAvailable {
                Button {
                    downloader.download()
                } label: {
                    Label("Download Isabelle (~1 GB)", systemImage: "arrow.down.circle")
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.small)
            } else {
                Label("Found via custom path", systemImage: "checkmark")
                    .font(.caption).foregroundStyle(.green)
            }
        }
    }

    /// Opens the app's Settings window. The action selector changed names across macOS
    /// releases (`showSettingsWindow:` on Ventura+, `showPreferencesWindow:` before), and
    /// `sendAction` returns `false` when no responder handles it — so we try both and then
    /// pull the Settings window to the front.
    static func openAppSettings() {
        if !NSApp.sendAction(Selector(("showSettingsWindow:")), to: nil, from: nil) {
            _ = NSApp.sendAction(Selector(("showPreferencesWindow:")), to: nil, from: nil)
        }
        NSApp.activate(ignoringOtherApps: true)
    }

    private var manualControls: some View {
        Link(destination: URL(string: "https://www.spass-prover.org/")!) {
            Label("Installation instructions", systemImage: "arrow.up.right.square")
                .font(.caption)
        }
    }

    // MARK: Footer

    private var footer: some View {
        HStack {
            Button("Open Settings…") {
                Self.openAppSettings()
            }
            .controlSize(.regular)

            Spacer()

            Button("Don't Ask Again") {
                UserSettings.shared.proofSetupNeverAsk = true
                onClose()
            }
            Button(isabelleMissing ? "Not Now" : "Done") {
                onClose()
            }
            .keyboardShortcut(.defaultAction)
        }
        .padding(20)
    }
}

#if DEBUG
struct ProofSetupView_Previews: PreviewProvider {
    static var previews: some View {
        ProofSetupView(report: ProofDependencyChecker.current(), onClose: {})
    }
}
#endif
