import AppKit
import Combine
import SwiftUI

// MARK: - Prover Settings View

/// SwiftUI settings view for configuring TLC, TLAPM, and backend prover paths.
///
/// This view provides a comprehensive interface for managing tool configuration,
/// including path discovery, version detection, and status indicators.
struct ProverSettingsView: View {
    @StateObject private var viewModel = ProverSettingsViewModel()

    var body: some View {
        ScrollView {
            VStack(alignment: .leading, spacing: 24) {
                tlcSection
                tlapmSection
                backendProversSection
                defaultSettingsSection
                actionsSection
            }
            .padding()
        }
        .frame(minWidth: 600, minHeight: 500)
        .onAppear {
            viewModel.verifyAllPaths()
        }
    }

    // MARK: - TLC Section

    private var tlcSection: some View {
        SettingsSection(title: "TLC (Model Checker)", icon: "gearshape.2") {
            VStack(alignment: .leading, spacing: 12) {
                // Path configuration
                ToolPathRow(
                    label: "TLC Path",
                    path: $viewModel.tlcPath,
                    status: viewModel.tlcStatus,
                    version: viewModel.tlcVersion,
                    onBrowse: { viewModel.browseTLCPath() },
                    onUseBundled: { viewModel.useBundledTLC() }
                )

                Divider()

                // Worker threads
                HStack {
                    Text("Worker threads:")
                        .frame(width: 140, alignment: .leading)

                    Stepper(
                        "\(viewModel.workerThreads)",
                        value: $viewModel.workerThreads,
                        in: 1...viewModel.maxWorkerThreads
                    )
                    .frame(width: 100)

                    Text("(max: \(viewModel.maxWorkerThreads))")
                        .foregroundColor(.secondary)
                        .font(.caption)

                    Spacer()
                }

                // Checkpoint settings
                HStack {
                    Toggle("Enable checkpointing", isOn: $viewModel.checkpointEnabled)
                        .frame(width: 200, alignment: .leading)

                    Spacer()
                }

                if viewModel.checkpointEnabled {
                    HStack {
                        Text("Checkpoint interval:")
                            .frame(width: 140, alignment: .leading)

                        Stepper(
                            "\(viewModel.checkpointInterval) minutes",
                            value: $viewModel.checkpointInterval,
                            in: 5...120
                        )
                        .frame(width: 140)

                        Spacer()
                    }
                }
            }
        }
    }

    // MARK: - TLAPM Section

    private var tlapmSection: some View {
        SettingsSection(title: "TLAPM (Proof Manager)", icon: "checkmark.seal") {
            ToolPathRow(
                label: "TLAPM Path",
                path: $viewModel.tlapmPath,
                status: viewModel.tlapmStatus,
                version: viewModel.tlapmVersion,
                onBrowse: { viewModel.browseTLAPMPath() },
                onUseBundled: { viewModel.useBundledTLAPM() }
            )
        }
    }

    // MARK: - Backend Provers Section

    private var backendProversSection: some View {
        SettingsSection(title: "Backend Provers", icon: "cpu") {
            VStack(alignment: .leading, spacing: 12) {
                ForEach(ProverInfo.allProvers) { prover in
                    if prover.backend == .isabelle {
                        // Special row for Isabelle with download support
                        IsabelleProverRow(
                            path: viewModel.binding(for: prover.backend),
                            status: viewModel.proverStatus(for: prover.backend),
                            version: viewModel.proverVersion(for: prover.backend),
                            onBrowse: { viewModel.browseProverPath(prover.backend) },
                            onPathUpdate: { path in
                                viewModel.updateIsabellePath(path)
                            }
                        )
                    } else {
                        ProverPathRow(
                            prover: prover,
                            path: viewModel.binding(for: prover.backend),
                            status: viewModel.proverStatus(for: prover.backend),
                            version: viewModel.proverVersion(for: prover.backend),
                            onBrowse: { viewModel.browseProverPath(prover.backend) }
                        )
                    }

                    if prover != ProverInfo.allProvers.last {
                        Divider()
                    }
                }
            }
        }
    }

    // MARK: - Default Settings Section

    private var defaultSettingsSection: some View {
        SettingsSection(title: "Default Settings", icon: "slider.horizontal.3") {
            VStack(alignment: .leading, spacing: 12) {
                // Default prover backend
                HStack {
                    Text("Default prover backend:")
                        .frame(width: 160, alignment: .leading)

                    Picker("", selection: $viewModel.defaultProverBackend) {
                        ForEach(ProverBackend.allCases, id: \.self) { backend in
                            Text(backend.displayName).tag(backend)
                        }
                    }
                    .pickerStyle(.menu)
                    .frame(width: 120)

                    Spacer()
                }

                // Default timeout
                HStack {
                    Text("Default timeout:")
                        .frame(width: 160, alignment: .leading)

                    Stepper(
                        "\(viewModel.defaultTimeout) seconds",
                        value: $viewModel.defaultTimeout,
                        in: 5...300,
                        step: 5
                    )
                    .frame(width: 140)

                    Spacer()
                }
            }
        }
    }

    // MARK: - Actions Section

    private var actionsSection: some View {
        SettingsSection(title: "Actions", icon: "wand.and.stars") {
            HStack(spacing: 12) {
                Button {
                    viewModel.verifyAllPaths()
                } label: {
                    HStack {
                        Image(systemName: "checkmark.circle")
                        Text("Verify All Paths")
                    }
                }
                .buttonStyle(.bordered)
                .disabled(viewModel.isVerifying)

                Button {
                    viewModel.openDownloadPage()
                } label: {
                    HStack {
                        Image(systemName: "arrow.down.circle")
                        Text("Download Missing Tools")
                    }
                }
                .buttonStyle(.bordered)

                Button {
                    viewModel.resetToBundled()
                } label: {
                    HStack {
                        Image(systemName: "arrow.counterclockwise")
                        Text("Reset to Bundled")
                    }
                }
                .buttonStyle(.bordered)

                Spacer()

                if viewModel.isVerifying {
                    ProgressView()
                        .controlSize(.small)
                    Text("Verifying...")
                        .foregroundColor(.secondary)
                        .font(.caption)
                }
            }

            if let verificationResult = viewModel.lastVerificationResult {
                VerificationResultView(result: verificationResult)
                    .padding(.top, 8)
            }
        }
    }
}

// MARK: - Settings Section Container

/// A styled container for a settings section with a title and icon.
struct SettingsSection<Content: View>: View {
    let title: String
    let icon: String
    let content: Content

    init(
        title: String,
        icon: String,
        @ViewBuilder content: () -> Content
    ) {
        self.title = title
        self.icon = icon
        self.content = content()
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack(spacing: 8) {
                Image(systemName: icon)
                    .foregroundColor(.accentColor)
                Text(title)
                    .font(.headline)
            }

            content
                .padding(.leading, 4)
        }
        .padding()
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(8)
    }
}

// MARK: - Tool Path Row

/// A row for configuring a tool path with status indicator.
struct ToolPathRow: View {
    let label: String
    @Binding var path: String
    let status: ToolStatus
    let version: String?
    let onBrowse: () -> Void
    let onUseBundled: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack {
                Text(label)
                    .frame(width: 100, alignment: .leading)

                TextField("Path", text: $path)
                    .textFieldStyle(.roundedBorder)

                Button("Browse...") {
                    onBrowse()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)

                Button("Use Bundled") {
                    onUseBundled()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)

                StatusIndicator(status: status)
            }

            if let version = version, status == .found {
                HStack {
                    Spacer()
                        .frame(width: 100)
                    Text("Version: \(version)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
            }
        }
    }
}

// MARK: - Prover Path Row

/// A row for configuring a backend prover path.
struct ProverPathRow: View {
    let prover: ProverInfo
    @Binding var path: String
    let status: ToolStatus
    let version: String?
    let onBrowse: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 6) {
            HStack {
                VStack(alignment: .leading, spacing: 2) {
                    Text(prover.displayName)
                        .fontWeight(.medium)
                    Text(prover.description)
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
                .frame(width: 160, alignment: .leading)

                TextField("Path", text: $path)
                    .textFieldStyle(.roundedBorder)

                Button("Browse...") {
                    onBrowse()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)

                StatusIndicator(status: status)
            }

            if let version = version, status == .found {
                HStack {
                    Spacer()
                        .frame(width: 160)
                    Text("Version: \(version)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
            }
        }
    }
}

// MARK: - Isabelle Prover Row

/// Special row for Isabelle with download functionality.
struct IsabelleProverRow: View {
    @Binding var path: String
    let status: ToolStatus
    let version: String?
    let onBrowse: () -> Void
    let onPathUpdate: (String) -> Void

    @StateObject private var downloader = IsabelleDownloader.shared

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack {
                VStack(alignment: .leading, spacing: 2) {
                    Text("Isabelle")
                        .fontWeight(.medium)
                    Text("Interactive theorem prover (~3 GB)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
                .frame(width: 160, alignment: .leading)

                // Show different content based on download state
                switch downloader.state {
                case .notInstalled:
                    notInstalledContent

                case .checking:
                    HStack {
                        ProgressView()
                            .controlSize(.small)
                        Text("Checking...")
                            .foregroundColor(.secondary)
                    }
                    Spacer()

                case .downloading(let progress):
                    downloadingContent(progress: progress)

                case .extracting:
                    HStack {
                        ProgressView()
                            .controlSize(.small)
                        Text("Extracting...")
                            .foregroundColor(.secondary)
                    }
                    Spacer()

                case .installed(let installedPath):
                    installedContent(installedPath: installedPath)

                case .error(let message):
                    errorContent(message: message)
                }
            }

            if let version = version, status == .found {
                HStack {
                    Spacer()
                        .frame(width: 160)
                    Text("Version: \(version)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
            }
        }
        .onAppear {
            // If Isabelle is installed, update the path
            if case .installed(let installedPath) = downloader.state {
                if path.isEmpty || path != installedPath {
                    path = installedPath
                    onPathUpdate(installedPath)
                }
            }
        }
        .onChange(of: downloader.state) { oldValue, newValue in
            if case .installed(let installedPath) = newValue {
                path = installedPath + "/bin/isabelle"
                onPathUpdate(path)
            }
        }
    }

    private var notInstalledContent: some View {
        HStack {
            Text("Not installed")
                .foregroundColor(.secondary)
                .frame(maxWidth: .infinity, alignment: .leading)

            Button {
                downloader.download()
            } label: {
                HStack(spacing: 4) {
                    Image(systemName: "arrow.down.circle")
                    Text("Download")
                }
            }
            .buttonStyle(.borderedProminent)
            .controlSize(.small)

            Button("Browse...") {
                onBrowse()
            }
            .buttonStyle(.bordered)
            .controlSize(.small)

            StatusIndicator(status: .notFound)
        }
    }

    private func downloadingContent(progress: Double) -> some View {
        HStack {
            VStack(alignment: .leading, spacing: 4) {
                ProgressView(value: progress)
                    .frame(maxWidth: .infinity)
                Text(downloader.formattedProgress)
                    .font(.caption)
                    .foregroundColor(.secondary)
            }

            Button {
                downloader.cancel()
            } label: {
                Image(systemName: "xmark.circle")
            }
            .buttonStyle(.bordered)
            .controlSize(.small)
        }
    }

    private func installedContent(installedPath: String) -> some View {
        HStack {
            Text(installedPath)
                .font(.caption)
                .foregroundColor(.secondary)
                .lineLimit(1)
                .truncationMode(.middle)
                .frame(maxWidth: .infinity, alignment: .leading)

            Button("Uninstall") {
                downloader.uninstall()
                path = ""
            }
            .buttonStyle(.bordered)
            .controlSize(.small)

            Button("Browse...") {
                onBrowse()
            }
            .buttonStyle(.bordered)
            .controlSize(.small)

            StatusIndicator(status: .found)
        }
    }

    private func errorContent(message: String) -> some View {
        HStack {
            Text(message)
                .font(.caption)
                .foregroundColor(.red)
                .lineLimit(2)
                .frame(maxWidth: .infinity, alignment: .leading)

            Button("Retry") {
                downloader.download()
            }
            .buttonStyle(.bordered)
            .controlSize(.small)

            Button("Browse...") {
                onBrowse()
            }
            .buttonStyle(.bordered)
            .controlSize(.small)

            StatusIndicator(status: .error(message))
        }
    }
}

// MARK: - Status Indicator

/// Visual indicator for tool installation status.
struct StatusIndicator: View {
    let status: ToolStatus

    var body: some View {
        HStack(spacing: 4) {
            Image(systemName: status.symbolName)
                .foregroundColor(status.color)

            if status == .checking {
                ProgressView()
                    .controlSize(.small)
            }
        }
        .frame(width: 30)
        .help(status.helpText)
    }
}

// MARK: - Verification Result View

/// Displays the results of path verification.
struct VerificationResultView: View {
    let result: VerificationResult

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack {
                Image(systemName: result.allPassed ? "checkmark.circle.fill" : "exclamationmark.triangle.fill")
                    .foregroundColor(result.allPassed ? .green : .orange)

                Text(result.summary)
                    .font(.callout)
                    .fontWeight(.medium)
            }

            if !result.missingTools.isEmpty {
                VStack(alignment: .leading, spacing: 4) {
                    Text("Missing tools:")
                        .font(.caption)
                        .foregroundColor(.secondary)

                    ForEach(result.missingTools, id: \.self) { tool in
                        HStack(spacing: 4) {
                            Image(systemName: "xmark.circle.fill")
                                .foregroundColor(.red)
                                .font(.caption)
                            Text(tool)
                                .font(.caption)
                        }
                    }
                }
            }
        }
        .padding(12)
        .background(result.allPassed ? Color.green.opacity(0.1) : Color.orange.opacity(0.1))
        .cornerRadius(6)
    }
}

// MARK: - Tool Status

/// Status of a tool installation.
enum ToolStatus: Equatable {
    case unknown
    case checking
    case found
    case notFound
    case error(String)

    var symbolName: String {
        switch self {
        case .unknown:
            return "questionmark.circle"
        case .checking:
            return "clock"
        case .found:
            return "checkmark.circle.fill"
        case .notFound:
            return "xmark.circle.fill"
        case .error:
            return "exclamationmark.triangle.fill"
        }
    }

    var color: Color {
        switch self {
        case .unknown:
            return .secondary
        case .checking:
            return .secondary
        case .found:
            return .green
        case .notFound:
            return .red
        case .error:
            return .orange
        }
    }

    var helpText: String {
        switch self {
        case .unknown:
            return "Status unknown"
        case .checking:
            return "Checking..."
        case .found:
            return "Tool found and executable"
        case .notFound:
            return "Tool not found"
        case .error(let message):
            return "Error: \(message)"
        }
    }
}

// MARK: - Prover Info

/// Information about a backend prover.
struct ProverInfo: Identifiable, Equatable {
    let id: String
    let backend: ProverBackend
    let displayName: String
    let description: String
    let binaryName: String
    let versionFlag: String

    static let allProvers: [ProverInfo] = [
        ProverInfo(
            id: "z3",
            backend: .z3,
            displayName: "Z3",
            description: "SMT solver from Microsoft Research",
            binaryName: "z3",
            versionFlag: "--version"
        ),
        ProverInfo(
            id: "zenon",
            backend: .zenon,
            displayName: "Zenon",
            description: "First-order theorem prover",
            binaryName: "zenon",
            versionFlag: "-version"
        ),
        ProverInfo(
            id: "isabelle",
            backend: .isabelle,
            displayName: "Isabelle",
            description: "Interactive theorem prover",
            binaryName: "isabelle",
            versionFlag: "version"
        ),
        ProverInfo(
            id: "cvc5",
            backend: .cvc5,
            displayName: "CVC5",
            description: "Modern SMT solver",
            binaryName: "cvc5",
            versionFlag: "--version"
        ),
        ProverInfo(
            id: "spass",
            backend: .spass,
            displayName: "SPASS",
            description: "First-order theorem prover",
            binaryName: "SPASS",
            versionFlag: "-V"
        )
    ]
}

// MARK: - Verification Result

/// Result of verifying all tool paths.
struct VerificationResult {
    let foundCount: Int
    let totalCount: Int
    let missingTools: [String]

    var allPassed: Bool {
        missingTools.isEmpty
    }

    var summary: String {
        if allPassed {
            return "All \(foundCount) tools found and verified"
        } else {
            return "\(foundCount)/\(totalCount) tools found, \(missingTools.count) missing"
        }
    }
}

// MARK: - Prover Settings View Model

/// View model for prover settings.
@MainActor
final class ProverSettingsViewModel: ObservableObject {
    // MARK: - TLC Settings

    @Published var tlcPath: String = "" {
        didSet { saveSetting(tlcPath, forKey: .tlcPath) }
    }
    @Published var tlcStatus: ToolStatus = .unknown
    @Published var tlcVersion: String?
    @Published var workerThreads: Int = ProcessInfo.processInfo.processorCount {
        didSet { saveSetting(workerThreads, forKey: .workerThreads) }
    }
    @Published var checkpointEnabled: Bool = true {
        didSet { saveSetting(checkpointEnabled, forKey: .checkpointEnabled) }
    }
    @Published var checkpointInterval: Int = 30 {
        didSet { saveSetting(checkpointInterval, forKey: .checkpointInterval) }
    }

    // MARK: - TLAPM Settings

    @Published var tlapmPath: String = "" {
        didSet { saveSetting(tlapmPath, forKey: .tlapmPath) }
    }
    @Published var tlapmStatus: ToolStatus = .unknown
    @Published var tlapmVersion: String?

    // MARK: - Backend Prover Settings

    @Published var z3Path: String = "" {
        didSet { saveSetting(z3Path, forKey: .z3Path) }
    }
    @Published var zenonPath: String = "" {
        didSet { saveSetting(zenonPath, forKey: .zenonPath) }
    }
    @Published var isabellePath: String = "" {
        didSet { saveSetting(isabellePath, forKey: .isabellePath) }
    }
    @Published var cvc5Path: String = "" {
        didSet { saveSetting(cvc5Path, forKey: .cvc5Path) }
    }
    @Published var spassPath: String = "" {
        didSet { saveSetting(spassPath, forKey: .spassPath) }
    }

    @Published private var proverStatuses: [ProverBackend: ToolStatus] = [:]
    @Published private var proverVersions: [ProverBackend: String] = [:]

    // MARK: - Default Settings

    @Published var defaultProverBackend: ProverBackend = .auto {
        didSet { saveSetting(defaultProverBackend.rawValue, forKey: .defaultProverBackend) }
    }
    @Published var defaultTimeout: Int = 30 {
        didSet { saveSetting(defaultTimeout, forKey: .defaultTimeout) }
    }

    // MARK: - State

    @Published var isVerifying: Bool = false
    @Published var lastVerificationResult: VerificationResult?

    let maxWorkerThreads: Int = ProcessInfo.processInfo.processorCount

    // MARK: - Initialization

    init() {
        loadSettings()
    }

    // MARK: - Settings Keys

    private enum SettingsKey: String {
        case tlcPath = "prover.tlc.path"
        case tlapmPath = "prover.tlapm.path"
        case z3Path = "prover.z3.path"
        case zenonPath = "prover.zenon.path"
        case isabellePath = "prover.isabelle.path"
        case cvc5Path = "prover.cvc5.path"
        case spassPath = "prover.spass.path"
        case workerThreads = "prover.tlc.workerThreads"
        case checkpointEnabled = "prover.tlc.checkpointEnabled"
        case checkpointInterval = "prover.tlc.checkpointInterval"
        case defaultProverBackend = "prover.defaultBackend"
        case defaultTimeout = "prover.defaultTimeout"
    }

    // MARK: - Settings Persistence

    private func loadSettings() {
        let defaults = UserDefaults.standard

        tlcPath = defaults.string(forKey: SettingsKey.tlcPath.rawValue) ?? ""
        tlapmPath = defaults.string(forKey: SettingsKey.tlapmPath.rawValue) ?? ""
        z3Path = defaults.string(forKey: SettingsKey.z3Path.rawValue) ?? ""
        zenonPath = defaults.string(forKey: SettingsKey.zenonPath.rawValue) ?? ""
        isabellePath = defaults.string(forKey: SettingsKey.isabellePath.rawValue) ?? ""
        cvc5Path = defaults.string(forKey: SettingsKey.cvc5Path.rawValue) ?? ""
        spassPath = defaults.string(forKey: SettingsKey.spassPath.rawValue) ?? ""

        if defaults.object(forKey: SettingsKey.workerThreads.rawValue) != nil {
            workerThreads = defaults.integer(forKey: SettingsKey.workerThreads.rawValue)
        }

        if defaults.object(forKey: SettingsKey.checkpointEnabled.rawValue) != nil {
            checkpointEnabled = defaults.bool(forKey: SettingsKey.checkpointEnabled.rawValue)
        }

        if defaults.object(forKey: SettingsKey.checkpointInterval.rawValue) != nil {
            checkpointInterval = defaults.integer(forKey: SettingsKey.checkpointInterval.rawValue)
        }

        if let backendRaw = defaults.string(forKey: SettingsKey.defaultProverBackend.rawValue),
           let backend = ProverBackend(rawValue: backendRaw) {
            defaultProverBackend = backend
        }

        if defaults.object(forKey: SettingsKey.defaultTimeout.rawValue) != nil {
            defaultTimeout = defaults.integer(forKey: SettingsKey.defaultTimeout.rawValue)
        }
    }

    private func saveSetting<T>(_ value: T, forKey key: SettingsKey) {
        UserDefaults.standard.set(value, forKey: key.rawValue)
    }

    // MARK: - Bindings

    func binding(for backend: ProverBackend) -> Binding<String> {
        switch backend {
        case .z3:
            return Binding(
                get: { self.z3Path },
                set: { self.z3Path = $0 }
            )
        case .zenon:
            return Binding(
                get: { self.zenonPath },
                set: { self.zenonPath = $0 }
            )
        case .isabelle:
            return Binding(
                get: { self.isabellePath },
                set: { self.isabellePath = $0 }
            )
        case .cvc5:
            return Binding(
                get: { self.cvc5Path },
                set: { self.cvc5Path = $0 }
            )
        case .spass:
            return Binding(
                get: { self.spassPath },
                set: { self.spassPath = $0 }
            )
        case .auto, .ls4:
            // These don't have separate paths
            return .constant("")
        }
    }

    func proverStatus(for backend: ProverBackend) -> ToolStatus {
        proverStatuses[backend] ?? .unknown
    }

    func proverVersion(for backend: ProverBackend) -> String? {
        proverVersions[backend]
    }

    // MARK: - Browse Actions

    func browseTLCPath() {
        if let url = browseForExecutable(title: "Select TLC Binary") {
            tlcPath = url.path
            Task { await verifyTLC() }
        }
    }

    func browseTLAPMPath() {
        if let url = browseForExecutable(title: "Select TLAPM Binary") {
            tlapmPath = url.path
            Task { await verifyTLAPM() }
        }
    }

    func browseProverPath(_ backend: ProverBackend) {
        if let url = browseForExecutable(title: "Select \(backend.displayName) Binary") {
            switch backend {
            case .z3:
                z3Path = url.path
            case .zenon:
                zenonPath = url.path
            case .isabelle:
                isabellePath = url.path
            case .cvc5:
                cvc5Path = url.path
            case .spass:
                spassPath = url.path
            case .auto, .ls4:
                break
            }
            Task { await verifyProver(backend) }
        }
    }

    private func browseForExecutable(title: String) -> URL? {
        let panel = NSOpenPanel()
        panel.title = title
        panel.canChooseFiles = true
        panel.canChooseDirectories = false
        panel.allowsMultipleSelection = false
        panel.canCreateDirectories = false
        panel.message = "Select the executable file"

        // Start in /usr/local/bin if it exists
        let initialDir = FileManager.default.fileExists(atPath: "/usr/local/bin")
            ? URL(fileURLWithPath: "/usr/local/bin")
            : FileManager.default.homeDirectoryForCurrentUser
        panel.directoryURL = initialDir

        guard panel.runModal() == .OK else { return nil }
        return panel.url
    }

    // MARK: - Use Bundled Actions

    func useBundledTLC() {
        tlcPath = ""
        Task { await verifyTLC() }
    }

    func useBundledTLAPM() {
        tlapmPath = ""
        Task { await verifyTLAPM() }
    }

    // MARK: - Verification

    func verifyAllPaths() {
        isVerifying = true
        lastVerificationResult = nil

        Task {
            async let tlcResult = verifyTLC()
            async let tlapmResult = verifyTLAPM()

            // Verify all provers in parallel
            await withTaskGroup(of: Void.self) { group in
                for prover in ProverInfo.allProvers {
                    group.addTask { await self.verifyProver(prover.backend) }
                }
            }

            // Wait for main tools
            _ = await (tlcResult, tlapmResult)

            // Build verification result
            var found = 0
            let total = 2 + ProverInfo.allProvers.count
            var missing: [String] = []

            if tlcStatus == .found {
                found += 1
            } else {
                missing.append("TLC")
            }

            if tlapmStatus == .found {
                found += 1
            } else {
                missing.append("TLAPM")
            }

            for prover in ProverInfo.allProvers {
                if proverStatuses[prover.backend] == .found {
                    found += 1
                } else {
                    missing.append(prover.displayName)
                }
            }

            lastVerificationResult = VerificationResult(
                foundCount: found,
                totalCount: total,
                missingTools: missing
            )

            isVerifying = false
        }
    }

    @discardableResult
    private func verifyTLC() async -> Bool {
        tlcStatus = .checking
        tlcVersion = nil

        let path = tlcPath.isEmpty ? findBundledTLC() : tlcPath

        guard let path = path, !path.isEmpty else {
            tlcStatus = .notFound
            return false
        }

        let (exists, version) = await checkBinaryExists(
            at: path,
            versionFlag: "-version"
        )

        if exists {
            tlcStatus = .found
            tlcVersion = version
            return true
        } else {
            tlcStatus = .notFound
            return false
        }
    }

    @discardableResult
    private func verifyTLAPM() async -> Bool {
        tlapmStatus = .checking
        tlapmVersion = nil

        let path = tlapmPath.isEmpty ? findBundledTLAPM() : tlapmPath

        guard let path = path, !path.isEmpty else {
            tlapmStatus = .notFound
            return false
        }

        let (exists, version) = await checkBinaryExists(
            at: path,
            versionFlag: "--version"
        )

        if exists {
            tlapmStatus = .found
            tlapmVersion = version
            return true
        } else {
            tlapmStatus = .notFound
            return false
        }
    }

    @discardableResult
    private func verifyProver(_ backend: ProverBackend) async -> Bool {
        proverStatuses[backend] = .checking
        proverVersions[backend] = nil

        let path: String?
        let versionFlag: String

        switch backend {
        case .z3:
            path = z3Path.isEmpty ? findInPath("z3") : z3Path
            versionFlag = "--version"
        case .zenon:
            path = zenonPath.isEmpty ? findInPath("zenon") : zenonPath
            versionFlag = "-version"
        case .isabelle:
            path = isabellePath.isEmpty ? findInPath("isabelle") : isabellePath
            versionFlag = "version"
        case .cvc5:
            path = cvc5Path.isEmpty ? findInPath("cvc5") : cvc5Path
            versionFlag = "--version"
        case .spass:
            path = spassPath.isEmpty ? findInPath("SPASS") : spassPath
            versionFlag = "-V"
        case .auto, .ls4:
            return true
        }

        guard let path = path, !path.isEmpty else {
            proverStatuses[backend] = .notFound
            return false
        }

        let (exists, version) = await checkBinaryExists(at: path, versionFlag: versionFlag)

        if exists {
            proverStatuses[backend] = .found
            proverVersions[backend] = version
            return true
        } else {
            proverStatuses[backend] = .notFound
            return false
        }
    }

    // MARK: - Binary Discovery

    private func findBundledTLC() -> String? {
        // Check SPM resource bundle
        if let url = Bundle.module.url(forResource: "tlc-native", withExtension: nil) {
            return url.path
        }

        // Check main bundle
        if let url = Bundle.main.url(forResource: "tlc-native", withExtension: nil) {
            return url.path
        }

        // Check bundle resources directly
        if let bundlePath = Bundle.main.resourcePath {
            let path = URL(fileURLWithPath: bundlePath)
                .appendingPathComponent("tlc-native").path
            if FileManager.default.fileExists(atPath: path) {
                return path
            }
        }

        return findInPath("tlc-native")
    }

    private func findBundledTLAPM() -> String? {
        // Check SPM resource bundle
        if let url = Bundle.module.url(forResource: "tlapm", withExtension: nil) {
            return url.path
        }

        // Check main bundle
        if let url = Bundle.main.url(forResource: "tlapm", withExtension: nil) {
            return url.path
        }

        // Check bundle resources directly
        if let bundlePath = Bundle.main.resourcePath {
            let path = URL(fileURLWithPath: bundlePath)
                .appendingPathComponent("tlapm").path
            if FileManager.default.fileExists(atPath: path) {
                return path
            }
        }

        return findInPath("tlapm")
    }

    private func findInPath(_ binaryName: String) -> String? {
        let commonPaths = [
            "/usr/local/bin/\(binaryName)",
            "/opt/homebrew/bin/\(binaryName)",
            FileManager.default.homeDirectoryForCurrentUser
                .appendingPathComponent(".tla/\(binaryName)").path,
            FileManager.default.homeDirectoryForCurrentUser
                .appendingPathComponent(".tla/provers/\(binaryName)").path
        ]

        for path in commonPaths {
            if FileManager.default.fileExists(atPath: path) {
                return path
            }
        }

        return nil
    }

    private func checkBinaryExists(
        at path: String,
        versionFlag: String
    ) async -> (exists: Bool, version: String?) {
        let fileManager = FileManager.default

        // Check if file exists
        guard fileManager.fileExists(atPath: path) else {
            return (false, nil)
        }

        // Check if executable
        guard fileManager.isExecutableFile(atPath: path) else {
            return (false, nil)
        }

        // Try to get version
        let version = await getToolVersion(at: path, versionFlag: versionFlag)
        return (true, version)
    }

    private func getToolVersion(at path: String, versionFlag: String) async -> String? {
        return await withCheckedContinuation { continuation in
            let process = Process()
            process.executableURL = URL(fileURLWithPath: path)
            process.arguments = versionFlag.split(separator: " ").map(String.init)

            let pipe = Pipe()
            process.standardOutput = pipe
            process.standardError = pipe

            do {
                try process.run()

                // Set a timeout
                DispatchQueue.global().asyncAfter(deadline: .now() + 5) {
                    if process.isRunning {
                        process.terminate()
                    }
                }

                process.waitUntilExit()

                let data = pipe.fileHandleForReading.readDataToEndOfFile()
                if let output = String(data: data, encoding: .utf8)?.trimmingCharacters(in: .whitespacesAndNewlines),
                   !output.isEmpty {
                    // Extract first line and clean up
                    let firstLine = output.components(separatedBy: .newlines).first ?? output
                    let cleaned = firstLine.trimmingCharacters(in: .whitespacesAndNewlines)
                    // Limit to reasonable length
                    let version = String(cleaned.prefix(100))
                    continuation.resume(returning: version)
                } else {
                    continuation.resume(returning: nil)
                }
            } catch {
                continuation.resume(returning: nil)
            }
        }
    }

    // MARK: - Actions

    func openDownloadPage() {
        let url = URL(string: "https://lamport.azurewebsites.net/tla/tools.html")!
        NSWorkspace.shared.open(url)
    }

    func resetToBundled() {
        tlcPath = ""
        tlapmPath = ""
        z3Path = ""
        zenonPath = ""
        isabellePath = ""
        cvc5Path = ""
        spassPath = ""

        verifyAllPaths()
    }

    /// Update Isabelle path and verify it
    func updateIsabellePath(_ path: String) {
        isabellePath = path
        Task { await verifyProver(.isabelle) }
    }
}

// MARK: - Preview

#if DEBUG
struct ProverSettingsView_Previews: PreviewProvider {
    static var previews: some View {
        ProverSettingsView()
            .frame(width: 700, height: 800)
    }
}
#endif
