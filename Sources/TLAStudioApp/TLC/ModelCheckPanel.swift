import SwiftUI

// MARK: - Model Check Panel

/// Main panel for TLC model checking UI
struct ModelCheckPanel: View {
    @ObservedObject var document: TLADocument
    @StateObject private var viewModel: ModelCheckViewModel

    init(document: TLADocument) {
        self.document = document
        self._viewModel = StateObject(wrappedValue: ModelCheckViewModel(document: document))
    }

    var body: some View {
        VStack(spacing: 0) {
            HStack {
                if viewModel.isRunning {
                    Menu {
                        Button(action: viewModel.stopModelCheck) {
                            Label("Stop", systemImage: "stop.fill")
                        }
                        Button(action: viewModel.stopWithCheckpoint) {
                            Label("Stop & Checkpoint", systemImage: "stop.circle")
                        }
                    } label: {
                        Label("Stop", systemImage: "stop.fill")
                    }
                    .menuStyle(.borderlessButton)
                    .frame(width: 80)
                    .background(Color.red.opacity(0.1))
                    .cornerRadius(6)
                } else {
                    Button(action: viewModel.runModelCheck) {
                        Label("Run TLC", systemImage: "play.fill")
                    }
                    .buttonStyle(.borderedProminent)
                    .disabled(!viewModel.canRun)

                    TLCModePicker(selectedMode: $document.selectedTLCMode)
                }

                Spacer()

                Picker("", selection: $viewModel.viewMode) {
                    Text("Progress").tag(ModelCheckViewMode.progress)
                    Text("Config").tag(ModelCheckViewMode.config)
                    Text("Coverage").tag(ModelCheckViewMode.coverage)
                    if viewModel.hasErrorTrace {
                        Text("Trace").tag(ModelCheckViewMode.trace)
                        Text("Graph").tag(ModelCheckViewMode.stateGraph)
                    }
                    Text("Checkpoints").tag(ModelCheckViewMode.checkpoints)
                    Text("Proof").tag(ModelCheckViewMode.proof)
                }
                .pickerStyle(.segmented)
                .frame(maxWidth: viewModel.hasErrorTrace ? 550 : 450)
            }
            .padding(8)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            switch viewModel.viewMode {
            case .progress:
                progressView

            case .config:
                ModelConfigEditor(
                    config: $viewModel.config,
                    symbols: document.symbols
                )

            case .coverage:
                if let session = viewModel.session,
                   let progress = session.progress {
                    CoverageView(
                        coverage: progress.coverage,
                        totalStates: progress.distinctStates
                    )
                } else {
                    NoCoverageView()
                }

            case .trace:
                if let trace = viewModel.errorTrace {
                    ErrorTraceView(trace: trace) { location in
                        viewModel.jumpToSource(location, in: document)
                    }
                } else {
                    Text("No error trace available")
                        .foregroundColor(.secondary)
                        .frame(maxWidth: .infinity, maxHeight: .infinity)
                }

            case .stateGraph:
                if let trace = viewModel.errorTrace {
                    StateGraphView(trace: trace)
                } else {
                    Text("No error trace available")
                        .foregroundColor(.secondary)
                        .frame(maxWidth: .infinity, maxHeight: .infinity)
                }

            case .checkpoints:
                CheckpointSettingsView(
                    config: $viewModel.config,
                    specURL: document.fileURL,
                    onResume: { checkpoint in
                        viewModel.resumeFromCheckpoint(checkpoint)
                    }
                )

            case .proof:
                if let proofSession = document.proofSession {
                    ProofObligationsPanel(
                        session: proofSession,
                        onJumpToSource: { location in
                            let offset = document.offset(forLine: location.startLine, column: location.startColumn)
                            document.selectedRange = NSRange(location: offset, length: 0)
                        }
                    )
                } else {
                    VStack(spacing: 16) {
                        Image(systemName: "checkmark.shield")
                            .font(.largeTitle)
                            .foregroundColor(.secondary)

                        Text("Proof Checking")
                            .font(.headline)

                        Text("Click 'Check All Proofs' or press Shift+Cmd+P to verify proofs")
                            .font(.callout)
                            .foregroundColor(.secondary)
                            .multilineTextAlignment(.center)

                        Button("Check All Proofs") {
                            document.runProofCheck()
                        }
                        .buttonStyle(.borderedProminent)
                    }
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
                    .padding()
                }
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .runModelCheck)) { notification in
            // Handle both nil (from menu) and specific document (from toolbar)
            if notification.object == nil || (notification.object as? TLADocument) === document {
                viewModel.runModelCheck()
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .stopModelCheck)) { notification in
            // Handle both nil (from menu) and specific document (from toolbar)
            if notification.object == nil || (notification.object as? TLADocument) === document {
                viewModel.stopModelCheck()
            }
        }
    }

    @ViewBuilder
    var progressView: some View {
        if let session = viewModel.session {
            ModelCheckProgressView(session: session)
        } else if let lastResult = viewModel.lastResult {
            VStack(spacing: 16) {
                ResultSummaryView(result: lastResult)

                if lastResult.outOfMemory {
                    OOMRecoveryView(
                        suggestJVM: lastResult.suggestJVMRetry,
                        onRetryWithJVM: { viewModel.retryWithJVM() },
                        onRetryWithDiskStorage: { viewModel.retryWithDiskStorage() },
                        onEnableDiskStorage: {
                            viewModel.config.useDiskStorage = true
                            viewModel.runModelCheck()
                        }
                    )
                }

                if let trace = lastResult.errorTrace {
                    CompactErrorTraceView(trace: trace) {
                        viewModel.viewMode = .trace
                    }
                }
            }
            .padding()
            .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .top)
        } else {
            VStack(spacing: 16) {
                Image(systemName: "play.rectangle")
                    .font(.largeTitle)
                    .foregroundColor(.secondary)

                Text("Ready to Check")
                    .font(.headline)

                Text("Click 'Run TLC' or press Cmd+R to start model checking")
                    .font(.callout)
                    .foregroundColor(.secondary)

                if viewModel.config.invariants.isEmpty {
                    HStack {
                        Image(systemName: "exclamationmark.triangle")
                            .foregroundColor(.orange)
                        Text("No invariants configured")
                            .foregroundColor(.orange)
                    }
                    .font(.caption)
                }
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity)
        }
    }
}

// MARK: - View Mode

enum ModelCheckViewMode {
    case progress
    case config
    case coverage
    case trace
    case stateGraph
    case checkpoints
    case proof
}

// MARK: - View Model

@MainActor
class ModelCheckViewModel: ObservableObject {
    weak var document: TLADocument?

    @Published var config: ModelConfig
    @Published var viewMode: ModelCheckViewMode = .progress

    init(document: TLADocument) {
        self.document = document

        let specURL = document.fileURL ?? URL(fileURLWithPath: "/tmp/untitled.tla")
        let configURL = specURL.deletingPathExtension().appendingPathExtension("cfg")
        let existingConfig = ModelConfig.parse(from: configURL)

        let constants = existingConfig?.constants ?? [:]
        var invariants = existingConfig?.invariants ?? []

        let detectedInvariants = Self.detectInvariants(in: document.symbols)
        for inv in detectedInvariants {
            if !invariants.contains(inv) {
                invariants.append(inv)
            }
        }

        self.config = ModelConfig(
            name: "Default",
            specFile: specURL,
            initPredicate: existingConfig?.initPredicate ?? "Init",
            nextAction: existingConfig?.nextAction ?? "Next",
            constants: constants,
            invariants: invariants,
            temporalProperties: existingConfig?.temporalProperties ?? [],
            stateConstraint: existingConfig?.stateConstraint,
            actionConstraint: existingConfig?.actionConstraint,
            workers: ProcessInfo.processInfo.activeProcessorCount
        )
    }

    // Use document's session directly instead of maintaining a separate copy
    var session: TLCSession? {
        document?.tlcSession
    }

    var isRunning: Bool {
        session?.isRunning ?? false
    }

    var canRun: Bool {
        document?.fileURL != nil || !(document?.content.isEmpty ?? true)
    }

    // Use document's last result directly
    var lastResult: ModelCheckResult? {
        document?.lastTLCResult
    }

    var hasErrorTrace: Bool {
        lastResult?.errorTrace != nil || session?.result?.errorTrace != nil
    }

    var errorTrace: ErrorTrace? {
        session?.result?.errorTrace ?? lastResult?.errorTrace
    }

    func runModelCheck() {
        guard let document = document else {
            return
        }
        viewMode = .progress

        // Save config to .cfg file so document reads our edits
        if let fileURL = document.fileURL {
            let configURL = fileURL.deletingPathExtension().appendingPathExtension("cfg")
            try? config.write(to: configURL)
        }

        document.runModelCheck()  // Uses document.selectedTLCMode
    }

    func stopModelCheck() {
        document?.stopModelCheck()
    }

    func stopWithCheckpoint() {
        session?.stopWithCheckpoint()
    }

    func resumeFromCheckpoint(_ checkpoint: CheckpointInfo) {
        guard let document = document else { return }
        viewMode = .progress

        let session = TLCSession(
            specURL: document.fileURL ?? config.specFile,
            config: config,
            binaryMode: document.selectedTLCMode
        )
        document.tlcSession = session
        session.resume(from: checkpoint)

        // Watch for completion (fixes missing watch task bug)
        Task { @MainActor [weak document] in
            while session.isRunning {
                try? await Task.sleep(nanoseconds: 100_000_000) // 100ms
                if Task.isCancelled { return }
                guard document != nil else { return }
            }
            document?.lastTLCResult = session.result
        }
    }

    func jumpToSource(_ location: SourceLocation, in document: TLADocument) {
        let offset = document.offset(forLine: location.line, column: location.column)
        document.selectedRange = NSRange(location: offset, length: 0)
        document.delegate?.documentDidNavigate(
            document,
            to: TLARange(
                start: TLAPosition(line: UInt32(location.line), column: UInt32(location.column)),
                end: TLAPosition(
                    line: UInt32(location.endLine ?? location.line),
                    column: UInt32(location.endColumn ?? location.column)
                )
            )
        )
    }

    // MARK: - OOM Recovery

    /// Retry with JVM mode after OOM
    func retryWithJVM() {
        guard lastResult?.outOfMemory == true else { return }

        if let session = session {
            viewMode = .progress
            session.retryWithJVM()
        } else if let document = document {
            viewMode = .progress
            let newSession = TLCSession(
                specURL: document.fileURL ?? config.specFile,
                config: config,
                binaryMode: .jvm
            )
            document.tlcSession = newSession
            newSession.start()
        }
    }

    /// Retry with disk storage after OOM
    func retryWithDiskStorage() {
        guard lastResult?.outOfMemory == true else { return }

        if let session = session {
            viewMode = .progress
            session.retryWithDiskStorage()
        } else if let document = document {
            viewMode = .progress
            config.useDiskStorage = true
            let newSession = TLCSession(
                specURL: document.fileURL ?? config.specFile,
                config: config
            )
            document.tlcSession = newSession
            newSession.start()
        }
    }

    // MARK: - Detection

    static func detectInvariants(in symbols: [TLASymbol]) -> [String] {
        var invariants: [String] = []

        for symbol in symbols {
            let name = symbol.name
            if name == "TypeOK" || name == "TypeInvariant" ||
               name.contains("Invariant") || name.contains("Safe") {
                invariants.append(name)
            }

            invariants.append(contentsOf: detectInvariants(in: symbol.children))
        }

        return invariants
    }
}


// MARK: - Compact Panel for Bottom Bar

/// Smaller version of model check panel for bottom panel integration
struct ModelCheckPanelCompact: View {
    @ObservedObject var document: TLADocument
    @StateObject private var viewModel: ModelCheckViewModel

    init(document: TLADocument) {
        self.document = document
        self._viewModel = StateObject(wrappedValue: ModelCheckViewModel(document: document))
    }

    var body: some View {
        HStack {
            if viewModel.isRunning {
                ProgressView()
                    .controlSize(.small)

                if let progress = viewModel.session?.progress {
                    Text("\(progress.distinctStates) states")
                        .font(.caption)
                        .monospacedDigit()

                    Text("(\(Int(progress.statesPerSecond))/s)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                Spacer()

                Button("Stop") {
                    viewModel.stopModelCheck()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
            } else if let error = viewModel.session?.error {
                Image(systemName: "exclamationmark.triangle.fill")
                    .foregroundColor(.orange)

                Text(error.localizedDescription)
                    .font(.caption)
                    .foregroundColor(.red)
                    .lineLimit(2)
                    .truncationMode(.tail)
                    .textSelection(.enabled)

                Spacer()

                Button("Run Again") {
                    viewModel.runModelCheck()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
            } else if let result = viewModel.lastResult {
                Image(systemName: result.success ? "checkmark.circle.fill" : "xmark.circle.fill")
                    .foregroundColor(result.success ? .green : .red)

                Text(result.success ? "Passed" : "Error Found")
                    .font(.caption)

                Text("(\(result.distinctStates) states)")
                    .font(.caption)
                    .foregroundColor(.secondary)

                Spacer()

                if result.errorTrace != nil {
                    Button("View Trace") {
                        // Show trace in popover or new window
                    }
                    .buttonStyle(.link)
                    .controlSize(.small)
                }

                Button("Run Again") {
                    viewModel.runModelCheck()
                }
                .buttonStyle(.bordered)
                .controlSize(.small)
            } else {
                Text("Ready to check")
                    .font(.caption)
                    .foregroundColor(.secondary)

                Spacer()

                Button("Run TLC") {
                    viewModel.runModelCheck()
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.small)
                .disabled(!viewModel.canRun)
            }
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
        .onReceive(NotificationCenter.default.publisher(for: .runModelCheck)) { notification in
            // Handle both nil (from menu) and specific document (from toolbar)
            if notification.object == nil || (notification.object as? TLADocument) === document {
                viewModel.runModelCheck()
            }
        }
        .onReceive(NotificationCenter.default.publisher(for: .stopModelCheck)) { notification in
            // Handle both nil (from menu) and specific document (from toolbar)
            if notification.object == nil || (notification.object as? TLADocument) === document {
                viewModel.stopModelCheck()
            }
        }
    }
}

// MARK: - OOM Recovery View

/// View shown when TLC runs out of memory, offering recovery options
struct OOMRecoveryView: View {
    let suggestJVM: Bool
    let onRetryWithJVM: () -> Void
    let onRetryWithDiskStorage: () -> Void
    let onEnableDiskStorage: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack {
                Image(systemName: "exclamationmark.triangle.fill")
                    .foregroundColor(.orange)
                Text("Out of Memory")
                    .font(.headline)
            }

            Text("TLC ran out of memory. The native image has a 32GB heap limit. Try one of these options:")
                .font(.callout)
                .foregroundColor(.secondary)

            VStack(alignment: .leading, spacing: 8) {
                if suggestJVM {
                    Button(action: onRetryWithJVM) {
                        HStack {
                            Image(systemName: "arrow.clockwise")
                            VStack(alignment: .leading) {
                                Text("Retry with JVM")
                                    .fontWeight(.medium)
                                Text("No memory limit, 2-3s startup overhead")
                                    .font(.caption)
                                    .foregroundColor(.secondary)
                            }
                        }
                    }
                    .buttonStyle(.borderedProminent)
                }

                Button(action: onRetryWithDiskStorage) {
                    HStack {
                        Image(systemName: "externaldrive")
                        VStack(alignment: .leading) {
                            Text("Retry with Disk Storage")
                                .fontWeight(.medium)
                            Text("Spill fingerprints to disk, ~3-5x slower")
                                .font(.caption)
                                .foregroundColor(.secondary)
                        }
                    }
                }
                .buttonStyle(.bordered)

                Button(action: onEnableDiskStorage) {
                    HStack {
                        Image(systemName: "gearshape")
                        Text("Enable Disk Storage & Run")
                    }
                }
                .buttonStyle(.bordered)
            }
        }
        .padding()
        .background(Color.orange.opacity(0.1))
        .cornerRadius(8)
        .overlay(
            RoundedRectangle(cornerRadius: 8)
                .stroke(Color.orange.opacity(0.3), lineWidth: 1)
        )
    }
}

// MARK: - TLC Mode Picker

/// Picker for selecting TLC execution mode
struct TLCModePicker: View {
    @Binding var selectedMode: TLCProcessManager.TLCBinaryMode

    var body: some View {
        Picker(selection: $selectedMode, label: pickerLabel) {
            Label("Auto", systemImage: "wand.and.stars")
                .tag(TLCProcessManager.TLCBinaryMode.auto)

            Divider()

            Label("Fast (Epsilon GC)", systemImage: "hare")
                .tag(TLCProcessManager.TLCBinaryMode.fast)

            Label("Standard (SerialGC)", systemImage: "tortoise")
                .tag(TLCProcessManager.TLCBinaryMode.standard)

            Divider()

            Label("JVM (No Memory Limit)", systemImage: "cup.and.saucer")
                .tag(TLCProcessManager.TLCBinaryMode.jvm)
        }
        .pickerStyle(.menu)
        .help(modeTooltip)
    }

    private var pickerLabel: some View {
        HStack(spacing: 4) {
            Image(systemName: modeIcon)
            Text(modeLabel)
                .font(.caption)
        }
        .padding(.horizontal, 8)
        .padding(.vertical, 4)
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(6)
    }

    private var modeLabel: String {
        switch selectedMode {
        case .auto: return "Auto"
        case .fast: return "Fast"
        case .standard: return "Standard"
        case .jvm: return "JVM"
        }
    }

    private var modeIcon: String {
        switch selectedMode {
        case .auto: return "wand.and.stars"
        case .fast: return "hare"
        case .standard: return "tortoise"
        case .jvm: return "cup.and.saucer"
        }
    }

    private var modeTooltip: String {
        switch selectedMode {
        case .auto:
            return "Auto-select based on estimated state space"
        case .fast:
            return "Epsilon GC: Fastest, but limited to 32GB heap"
        case .standard:
            return "SerialGC: Slower but handles GC, 32GB heap limit"
        case .jvm:
            return "Full JVM: No memory limit, 2-3s startup overhead"
        }
    }
}
