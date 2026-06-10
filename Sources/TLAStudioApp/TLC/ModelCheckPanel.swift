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

                    Text(viewModel.config.name)
                        .font(.caption.weight(.medium))
                        .padding(.horizontal, 8)
                        .padding(.vertical, 4)
                        .background(Color.accentColor.opacity(0.1))
                        .clipShape(Capsule())
                        .help("Current model")
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
                    symbols: document.symbols,
                    configStore: document.modelConfigStore,
                    onActivateModel: { activatedConfig in
                        viewModel.config = activatedConfig
                        document.activeModelConfig = activatedConfig
                    }
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
                } else if viewModel.isLoadingErrorTrace {
                    ProgressView("Loading trace…")
                        .frame(maxWidth: .infinity, maxHeight: .infinity)
                } else {
                    Text("No error trace available")
                        .foregroundColor(.secondary)
                        .frame(maxWidth: .infinity, maxHeight: .infinity)
                }

            case .stateGraph:
                if let trace = viewModel.errorTrace {
                    StateGraphView(trace: trace)
                } else if viewModel.isLoadingErrorTrace {
                    ProgressView("Loading trace…")
                        .frame(maxWidth: .infinity, maxHeight: .infinity)
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
                            // ProofSourceLocation is 1-based; offset(forLine:column:) is 0-based.
                            let offset = document.offset(
                                forLine: max(0, location.startLine - 1),
                                column: max(0, location.startColumn - 1)
                            )
                            document.selectedRange = NSRange(location: offset, length: 0)
                        },
                        assistProvider: { obligation in
                            let suggestions = ProofAssist.byDefSuggestions(
                                for: obligation,
                                content: document.content,
                                symbols: document.symbols,
                                crossModuleSymbols: document.crossModuleProvider.symbols
                            )
                            return ProofObligationAssist(
                                byDefSuggestions: suggestions,
                                byDefInsertion: ProofAssist.planByDefInsertion(
                                    names: suggestions,
                                    for: obligation,
                                    content: document.content
                                ),
                                invariantCandidates: ProofAssist.invariantCandidates(
                                    for: obligation,
                                    symbols: document.symbols
                                )
                            )
                        },
                        onApplyByDef: { insertion in
                            document.applyByDefInsertion(insertion)
                        },
                        onModelCheckInvariant: { name in
                            document.modelCheckInvariant(named: name)
                        }
                    )
                } else {
                    VStack(spacing: 16) {
                        Image(systemName: "checkmark.shield")
                            .font(.largeTitle)
                            .foregroundColor(.secondary)

                        Text("Proof Checking")
                            .font(.headline)

                        Text("Click 'Check All Proofs' or press ⇧⌘P to verify proofs")
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
        .task(id: viewModel.traceLoadKey) {
            await viewModel.refreshLoadedErrorTrace(loadIfNeeded: viewModel.shouldLoadErrorTrace)
        }
        .onReceiveDocumentNotification(.runModelCheck, for: document) {
            viewModel.runModelCheck()
        }
        .onReceiveDocumentNotification(.stopModelCheck, for: document) {
            viewModel.stopModelCheck()
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

                if let trace = viewModel.errorTrace {
                    CompactErrorTraceView(trace: trace) {
                        viewModel.viewMode = .trace
                    }
                } else if lastResult.hasErrorTrace {
                    LazyErrorTraceSummaryView(
                        stateCount: lastResult.errorTraceStateCount,
                        isLoading: viewModel.isLoadingErrorTrace
                    ) {
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

                Text("Ready to check")
                    .font(.headline)

                Text("Click 'Run TLC' or press ⌘R to start model checking")
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
    @Published private(set) var loadedErrorTrace: ErrorTrace?
    @Published private(set) var isLoadingErrorTrace = false

    private var loadedTraceSessionID: UUID?

    init(document: TLADocument) {
        self.document = document

        self.config = document.resolvedModelConfig()
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
        errorTrace != nil || activeTraceResult?.hasErrorTrace == true
    }

    var errorTrace: ErrorTrace? {
        if let trace = activeTraceResult?.errorTrace {
            return trace
        }
        guard loadedTraceSessionID == activeTraceResult?.sessionId else {
            return nil
        }
        return loadedErrorTrace
    }

    var traceLoadKey: UUID? {
        shouldLoadErrorTrace ? activeTraceResult?.sessionId : nil
    }

    var shouldLoadErrorTrace: Bool {
        switch viewMode {
        case .trace, .stateGraph:
            return true
        default:
            return false
        }
    }

    func runModelCheck() {
        guard let document = document else {
            return
        }
        viewMode = .progress
        document.activeModelConfig = config
        document.runModelCheck(config: config)
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
        document.resumeModelCheck(from: checkpoint, config: config)
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
        guard lastResult?.outOfMemory == true, let document = document else { return }

        viewMode = .progress
        document.runModelCheck(config: document.activeModelConfig ?? config, binaryMode: .jvm)
    }

    /// Retry with disk storage after OOM
    func retryWithDiskStorage() {
        guard lastResult?.outOfMemory == true, let document = document else { return }

        viewMode = .progress
        var retryConfig = document.activeModelConfig ?? config
        retryConfig.useDiskStorage = true
        config = retryConfig
        document.runModelCheck(config: retryConfig)
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

    private var activeTraceResult: ModelCheckResult? {
        session?.result ?? lastResult
    }

    func refreshLoadedErrorTrace(loadIfNeeded: Bool) async {
        guard let result = activeTraceResult else {
            loadedErrorTrace = nil
            loadedTraceSessionID = nil
            isLoadingErrorTrace = false
            return
        }

        if let trace = result.errorTrace {
            loadedErrorTrace = trace
            loadedTraceSessionID = result.sessionId
            isLoadingErrorTrace = false
            return
        }

        guard let lazyTrace = result.lazyErrorTrace else {
            loadedErrorTrace = nil
            loadedTraceSessionID = result.sessionId
            isLoadingErrorTrace = false
            return
        }

        guard loadIfNeeded else {
            isLoadingErrorTrace = false
            return
        }

        if loadedTraceSessionID == result.sessionId, loadedErrorTrace != nil {
            isLoadingErrorTrace = false
            return
        }

        isLoadingErrorTrace = true
        defer { isLoadingErrorTrace = false }
        do {
            let trace = try await lazyTrace.toErrorTrace()
            guard activeTraceResult?.sessionId == result.sessionId else { return }
            loadedErrorTrace = trace
            loadedTraceSessionID = result.sessionId
        } catch {
            guard activeTraceResult?.sessionId == result.sessionId else { return }
            loadedErrorTrace = nil
            loadedTraceSessionID = result.sessionId
        }
    }
}

private struct LazyErrorTraceSummaryView: View {
    let stateCount: Int
    let isLoading: Bool
    let onOpenTrace: () -> Void

    var body: some View {
        VStack(alignment: .leading, spacing: 10) {
            HStack {
                Image(systemName: "point.3.connected.trianglepath.dotted")
                    .foregroundColor(.orange)
                Text("Counterexample available")
                    .font(.headline)
            }

            Text("\(stateCount) states are available in the trace. Load the detailed trace view only when needed.")
                .font(.callout)
                .foregroundColor(.secondary)

            Button(action: onOpenTrace) {
                if isLoading {
                    Label("Loading Trace…", systemImage: "hourglass")
                } else {
                    Label("Open Trace", systemImage: "list.bullet.rectangle")
                }
            }
            .buttonStyle(.bordered)
            .disabled(isLoading)
        }
        .padding()
        .background(Color.orange.opacity(0.08))
        .cornerRadius(8)
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
