import AppKit
import UniformTypeIdentifiers
import Combine
import os

// MARK: - TLADocument

/// Primary document class for TLA+ specification files.
/// See Docs/architecture/01-document-management.md for full specification.
final class TLADocument: NSDocument, ObservableObject {

    // MARK: - Logging

    private let logger = Log.logger(category: "TLADocument")

    // MARK: - Document State

    /// Raw text content of the specification
    @Published var content: String = "" {
        didSet {
            if content != oldValue {
                guard !suppressContentChangeHandling else {
                    lineIndexNeedsRebuild = true
                    return
                }
                updateChangeCount(.changeDone)
                contentDidChange()
            }
        }
    }

    /// Selected range in the editor
    @Published var selectedRange: NSRange = NSRange(location: 0, length: 0)

    /// Parsed syntax tree (updated on content change)
    @Published private(set) var parseResult: TLAParseResult?

    /// Extracted symbols from the document
    @Published private(set) var symbols: [TLASymbol] = []

    /// Diagnostics (errors, warnings) — the union of tree-sitter syntax
    /// diagnostics and SANY semantic diagnostics. Every diagnostics surface
    /// (Problems panel, editor underlines, status bar, minimap, navigator)
    /// observes this single array.
    @Published private(set) var diagnostics: [TLADiagnostic] = []

    /// Active TLC session for model checking
    @Published var tlcSession: TLCSession?

    /// Last TLC result (persists after session ends)
    @Published var lastTLCResult: ModelCheckResult?

    /// Selected TLC binary mode (shared across all panels)
    @Published var selectedTLCMode: TLCProcessManager.TLCBinaryMode = .auto

    /// Active proof session for TLAPS
    @Published var proofSession: ProofSession?

    /// Last proof result (persists after session ends)
    @Published var lastProofResult: ProofCheckResult?

    /// Proof annotation manager for editor integration
    @Published var proofAnnotationManager = ProofAnnotationManager()

    /// Active interactive-simulation session (nil until the user starts one)
    @Published var simulationSession: SimulationSession?

    /// Cross-module symbol snapshot for this document's EXTENDS closure —
    /// read synchronously by completions, hover, signature help, go-to-def.
    let crossModuleProvider = CrossModuleSymbolProvider()

    /// Latest Find All References results (point-in-time; cleared on edit).
    @Published private(set) var referenceResults: ReferenceResults?

    /// Error from the most recent attempt to start a simulation
    @Published private(set) var simulationError: String?

    /// Transient, auto-dismissing explanation of why an action didn't happen
    /// (shown as a banner over the editor; replaces silent beeps/log-only
    /// failures — platform review Phase 3).
    @Published private(set) var actionFeedback: ActionFeedback?
    private var actionFeedbackDismissTask: Task<Void, Never>?

    /// Model configuration store for persisting named configs
    @Published var modelConfigStore = ModelConfigStore()

    /// The currently active model configuration used by menu, toolbar, and inspector actions.
    @Published var activeModelConfig: ModelConfig?

    /// Document encoding (default UTF-8, preserve original on open)
    var encoding: String.Encoding = .utf8

    /// Line ending style
    var lineEnding: LineEnding = .lf

    /// Module name extracted from the content or document filename
    var moduleName: String {
        // Try to extract module name from content
        let modulePattern = #"----+\s+MODULE\s+(\w+)\s+----+"#
        if let regex = try? NSRegularExpression(pattern: modulePattern),
           let match = regex.firstMatch(in: content, range: NSRange(content.startIndex..., in: content)),
           let nameRange = Swift.Range(match.range(at: 1), in: content) {
            return String(content[nameRange])
        }

        // Fall back to filename without extension
        if let url = fileURL {
            return url.deletingPathExtension().lastPathComponent
        }

        return "Untitled"
    }

    /// Delegate for editor updates
    weak var delegate: TLADocumentDelegate?

    // MARK: - Private State

    private var parseTask: Task<Void, Never>?
    private var tlcWatchTask: Task<Void, Never>?
    private var proofWatchTask: Task<Void, Never>?

    /// Backing storage for `diagnostics`: syntax (tree-sitter) and semantic (SANY)
    /// findings update independently and are merged by `publishDiagnostics()`,
    /// so a slow SANY run never disturbs fresh syntax underlines and vice versa.
    private var syntaxDiagnostics: [TLADiagnostic] = []
    private var semanticDiagnostics: [TLADiagnostic] = []

    private var semanticCheckTask: Task<Void, Never>?

    /// Monotonic generation counter for semantic checks. A finished check only
    /// commits its results if no newer check was scheduled in the meantime —
    /// the counter analog of the `tlcSession === session` identity guard.
    private var semanticCheckGeneration = 0
    private var cancellables = Set<AnyCancellable>()
    private var tlcToolingSpecURL: URL?
    private var proofToolingSpecURL: URL?
    private var simulationToolingSpecURL: URL?

    /// Set by `close()` to make subsequent operations no-ops. Guards against
    /// late-arriving work running against a deallocated document.
    private var isClosed = false

    // MARK: - Line Offset Index (Performance Optimization)

    /// Cached UTF-16 line start offsets for O(log n) line lookup from editor selections.
    /// Index i contains the UTF-16 offset where line i starts (0-indexed).
    /// Line 0 always starts at offset 0.
    private var lineStartOffsets: [Int] = [0]

    /// Used while loading content from disk to avoid duplicate parse scheduling and dirty-state churn.
    private var suppressContentChangeHandling = false

    /// Fast path for the common case of ASCII-only specs where UTF-16 offsets and character
    /// columns are identical.
    private var contentIsASCII = true

    /// Cached UTF-16 length of the current content for editor range math.
    private var contentUTF16Length = 0

    /// Whether the line offset index needs to be rebuilt
    private var lineIndexNeedsRebuild = true

    // MARK: - Initialization

    override init() {
        super.init()
        content = Self.newDocumentTemplate()
        setupBindings()
    }

    private func setupBindings() {
        // Debounce content changes for parsing
        $content
            .debounce(for: .milliseconds(150), scheduler: RunLoop.main)
            .removeDuplicates()
            .sink { [weak self] _ in
                self?.scheduleParseContent()
            }
            .store(in: &cancellables)

        // Semantic analysis (SANY) rides a much longer debounce than the syntax
        // parse: each check spawns a JVM, so it must only fire once typing pauses.
        // Saves trigger an immediate check via `write(to:ofType:for:originalContentsURL:)`.
        $content
            .debounce(for: .milliseconds(1200), scheduler: RunLoop.main)
            .removeDuplicates()
            .sink { [weak self] _ in
                self?.scheduleSemanticCheck()
            }
            .store(in: &cancellables)
    }

    /// Template for new TLA+ files
    static func newDocumentTemplate() -> String {
        """
        -------------------------------- MODULE DieHard --------------------------------
        (*
          The Die Hard problem from the movie Die Hard 3.
          You have a 3 gallon jug and a 5 gallon jug, and need to measure exactly 4 gallons.

          This is a good test spec because:
          - Small state space (~30 states)
          - Has a reachable goal state
          - Tests basic TLC functionality
        *)

        EXTENDS Naturals

        VARIABLES
            small,   \\* 3 gallon jug
            big      \\* 5 gallon jug

        vars == <<small, big>>

        (* Type invariant - jugs can't be overfilled *)
        TypeOK ==
            /\\ small \\in 0..3
            /\\ big \\in 0..5

        (* Initial state - both jugs empty *)
        Init ==
            /\\ small = 0
            /\\ big = 0

        (* Fill the small jug completely *)
        FillSmall ==
            /\\ small' = 3
            /\\ big' = big

        (* Fill the big jug completely *)
        FillBig ==
            /\\ big' = 5
            /\\ small' = small

        (* Empty the small jug *)
        EmptySmall ==
            /\\ small' = 0
            /\\ big' = big

        (* Empty the big jug *)
        EmptyBig ==
            /\\ big' = 0
            /\\ small' = small

        (* Pour small jug into big jug *)
        SmallToBig ==
            LET amount == IF small + big <= 5
                          THEN small
                          ELSE 5 - big
            IN /\\ small' = small - amount
               /\\ big' = big + amount

        (* Pour big jug into small jug *)
        BigToSmall ==
            LET amount == IF small + big <= 3
                          THEN big
                          ELSE 3 - small
            IN /\\ big' = big - amount
               /\\ small' = small + amount

        (* All possible actions *)
        Next ==
            \\/ FillSmall
            \\/ FillBig
            \\/ EmptySmall
            \\/ EmptyBig
            \\/ SmallToBig
            \\/ BigToSmall

        (* The complete specification *)
        Spec == Init /\\ [][Next]_vars

        -----------------------------------------------------------------------------
        (* Properties to check *)

        (* Safety: TypeOK should always hold *)
        TypeInvariant == TypeOK

        (*
          NotSolved: The goal is to get exactly 4 gallons in the big jug.
          If we use this as an invariant, TLC should find a counterexample
          showing how to reach the goal state.
        *)
        NotSolved == big /= 4

        =============================================================================
        """
    }

    // MARK: - NSDocument Configuration

    override class var autosavesInPlace: Bool { true }
    override class var autosavesDrafts: Bool { true }
    override class var preservesVersions: Bool { true }
    override var autosavingFileType: String? { "com.tlaplus.specification" }

    override func canAsynchronouslyWrite(
        to url: URL,
        ofType typeName: String,
        for saveOperation: NSDocument.SaveOperationType
    ) -> Bool {
        true
    }

    // MARK: - Reading (OPEN)

    override func read(from url: URL, ofType typeName: String) throws {
        let data = try Data(contentsOf: url)

        // Encoding detection: Try UTF-8 first, fall back to Windows-1252
        if let text = String(data: data, encoding: .utf8) {
            encoding = .utf8
            setContentWithoutTriggeringChange(text)
        } else if let text = String(data: data, encoding: .windowsCP1252) {
            encoding = .windowsCP1252
            setContentWithoutTriggeringChange(text)
        } else {
            throw CocoaError(.fileReadUnknownStringEncoding)
        }

        // Detect and normalize line endings
        lineEnding = detectLineEnding(in: content)
        let normalizedContent = content
            .replacingOccurrences(of: "\r\n", with: "\n")
            .replacingOccurrences(of: "\r", with: "\n")
        setContentWithoutTriggeringChange(normalizedContent)

        // Parse immediately
        scheduleParseContent()

        // Load saved model configurations
        Task { @MainActor in
            modelConfigStore.load(for: url)
            activeModelConfig = resolvedModelConfig(for: url)
        }
    }

    private func setContentWithoutTriggeringChange(_ text: String) {
        // Temporarily remove the change observer
        let oldValue = content
        suppressContentChangeHandling = true
        content = text
        suppressContentChangeHandling = false
        lineIndexNeedsRebuild = true
        // Restore dirty state if it was clean
        if oldValue.isEmpty {
            updateChangeCount(.changeCleared)
        }
    }

    // MARK: - Writing (SAVE)

    override func data(ofType typeName: String) throws -> Data {
        // Apply original line ending style
        var outputContent = content
        switch lineEnding {
        case .crlf:
            outputContent = content.replacingOccurrences(of: "\n", with: "\r\n")
        case .cr:
            outputContent = content.replacingOccurrences(of: "\n", with: "\r")
        case .lf:
            break
        }

        guard let data = outputContent.data(using: encoding) else {
            throw CocoaError(.fileWriteUnknown)
        }
        return data
    }

    override func write(
        to url: URL,
        ofType typeName: String,
        for saveOperation: NSDocument.SaveOperationType,
        originalContentsURL: URL?
    ) throws {
        if saveOperation == .saveAsOperation {
            updateModuleNameFromFilename(url.deletingPathExtension().lastPathComponent)
        }

        try super.write(to: url, ofType: typeName, for: saveOperation,
                        originalContentsURL: originalContentsURL)

        // A successful explicit save is the strongest "check it now" signal for
        // semantic analysis. Saves may run on a background thread
        // (`canAsynchronouslyWrite`), so hop to the main actor; autosaves are
        // excluded — the edit-debounce pipeline already covers them.
        if saveOperation == .saveOperation || saveOperation == .saveAsOperation {
            Task { @MainActor [weak self] in
                self?.scheduleSemanticCheck()
            }
            // Other open documents indexing this file must see the new
            // contents; the index notifies their providers.
            let savedURL = url
            Task.detached(priority: .utility) {
                await ModuleSymbolIndex.shared.invalidate(fileURL: savedURL)
            }
        }
    }

    // MARK: - Window Controller

    override func makeWindowControllers() {
        let windowController = TLAWindowController(document: self)
        addWindowController(windowController)
    }

    override func close() {
        guard !isClosed else { return }
        isClosed = true

        // Cancel all running tasks first to prevent any new state updates
        let parseTaskToCancel = parseTask
        let tlcWatchTaskToCancel = tlcWatchTask
        let proofWatchTaskToCancel = proofWatchTask
        let semanticCheckTaskToCancel = semanticCheckTask

        parseTask = nil
        tlcWatchTask = nil
        proofWatchTask = nil
        semanticCheckTask = nil
        semanticCheckGeneration += 1

        parseTaskToCancel?.cancel()
        tlcWatchTaskToCancel?.cancel()
        proofWatchTaskToCancel?.cancel()
        semanticCheckTaskToCancel?.cancel()

        // Capture sessions and nil immediately so any re-entrant access sees clean state.
        let tlcSessionToStop = tlcSession
        let proofSessionToStop = proofSession
        let tlcToolingSpecURLToCleanup = tlcToolingSpecURL
        let proofToolingSpecURLToCleanup = proofToolingSpecURL

        tlcSession = nil
        proofSession = nil
        tlcToolingSpecURL = nil
        proofToolingSpecURL = nil

        // The simulation session owns no long-lived subprocess (each step is a
        // one-shot TLC run reaped by ProcessRegistry); invalidating discards
        // any in-flight result commit.
        simulationSession?.invalidate()
        simulationSession = nil
        SecureTempFile.cleanupContainer(for: simulationToolingSpecURL)
        simulationToolingSpecURL = nil

        crossModuleProvider.teardown()

        actionFeedbackDismissTask?.cancel()
        actionFeedbackDismissTask = nil
        actionFeedback = nil

        // Terminate subprocesses asynchronously: ProcessRegistry.terminate can block
        // up to ~1s (SIGTERM → SIGKILL escalation) and we don't want a UI hang on Cmd-W.
        // `applicationShouldTerminate` still calls ProcessRegistry.terminateAll synchronously
        // at app quit, so nothing outlives the app.
        if tlcSessionToStop != nil || proofSessionToStop != nil {
            Task { @MainActor in
                await tlcSessionToStop?.stopAsync()
                await proofSessionToStop?.stopAsync()
                SecureTempFile.cleanupContainer(for: tlcToolingSpecURLToCleanup)
                SecureTempFile.cleanupContainer(for: proofToolingSpecURLToCleanup)
            }
        } else {
            SecureTempFile.cleanupContainer(for: tlcToolingSpecURLToCleanup)
            SecureTempFile.cleanupContainer(for: proofToolingSpecURLToCleanup)
        }

        // Clear all Combine subscriptions before clearing state
        cancellables.removeAll()

        // Clear state (reuse the existing annotation manager instead of instantiating a new one
        // mid-teardown, which would churn SwiftUI observers bound to the old value).
        parseResult = nil
        symbols = []
        syntaxDiagnostics = []
        semanticDiagnostics = []
        diagnostics = []
        lastTLCResult = nil
        lastProofResult = nil
        proofAnnotationManager.updateAnnotations(for: [])
        activeModelConfig = nil

        delegate = nil
        NotificationCenter.default.post(name: .documentWillClose, object: self)

        super.close()
    }

    // MARK: - Parsing

    /// Show a transient banner explaining why an action didn't happen.
    @MainActor
    func reportActionFeedback(_ message: String, style: ActionFeedback.Style = .warning) {
        actionFeedback = ActionFeedback(message: message, style: style)
        actionFeedbackDismissTask?.cancel()
        actionFeedbackDismissTask = Task { @MainActor [weak self] in
            try? await Task.sleep(nanoseconds: 4_000_000_000)
            guard !Task.isCancelled else { return }
            self?.actionFeedback = nil
        }
    }

    private func contentDidChange() {
        lineIndexNeedsRebuild = true
        // Reference hits are point-in-time ranges; an edit invalidates them.
        if referenceResults != nil {
            referenceResults = nil
        }
        delegate?.documentContentDidChange(self)
    }

    /// Run symbol-aware Find All References and publish the results
    /// (References tab observes `referenceResults`).
    @MainActor
    func findAllReferences(to name: String) async {
        referenceResults = await ReferenceService.findReferences(to: name, in: self)
    }

    private func scheduleParseContent() {
        parseTask?.cancel()
        parseTask = Task { @MainActor [weak self] in
            guard let self else { return }
            await self.parseContent()
        }
    }

    @MainActor
    private func parseContent() async {
        do {
            let result = try await TLACoreWrapper.shared.parse(content, previous: parseResult)
            self.parseResult = result
            self.syntaxDiagnostics = result.diagnostics
            publishDiagnostics()

            // Extract symbols
            self.symbols = await TLACoreWrapper.shared.getSymbols(from: result)

            delegate?.documentDidParse(self)

            // Keep the cross-module symbol snapshot in sync with the
            // document's EXTENDS set (no-ops when unchanged).
            crossModuleProvider.scheduleRefresh(
                extendedModules: Array(Self.extendedModuleNames(in: content)),
                specDirectory: fileURL?.deletingLastPathComponent(),
                ownFileURL: fileURL
            )
        } catch {
            parseResult = nil
            symbols = []
            self.syntaxDiagnostics = [TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 0)
                ),
                severity: .error,
                message: error.localizedDescription,
                code: nil
            )]
            publishDiagnostics()
        }
    }

    /// Recompute the published union of syntax and semantic diagnostics.
    /// Syntax findings come first; entries equal to one already present are
    /// dropped (`TLADiagnostic` equality ignores `id`).
    @MainActor
    private func publishDiagnostics() {
        var combined = syntaxDiagnostics
        for diagnostic in semanticDiagnostics where !combined.contains(diagnostic) {
            combined.append(diagnostic)
        }
        diagnostics = combined
    }

    // MARK: - Semantic Analysis (SANY)

    /// Cancel any in-flight SANY check and start a new one for the current
    /// content. Called from the long edit-debounce pipeline and after saves;
    /// like `scheduleParseContent`, only ever invoked on the main thread.
    private func scheduleSemanticCheck() {
        guard !isClosed else { return }

        semanticCheckTask?.cancel()
        semanticCheckGeneration += 1
        let generation = semanticCheckGeneration

        semanticCheckTask = Task { @MainActor [weak self] in
            await self?.runSemanticCheck(generation: generation)
        }
    }

    @MainActor
    private func runSemanticCheck(generation: Int) async {
        guard !isClosed else { return }

        let toolingSpecURL: URL
        do {
            toolingSpecURL = try specURLForTooling()
        } catch {
            logger.warning("Semantic check skipped, no tooling spec: \(error.localizedDescription)")
            return
        }
        defer {
            if SecureTempFile.isManagedTemporaryFile(toolingSpecURL) {
                SecureTempFile.cleanupContainer(for: toolingSpecURL)
            }
        }

        let searchPaths = ProjectModuleResolver.searchPaths(
            for: toolingSpecURL,
            extraDirectories: originalDirectoryLibraryPaths(forToolingSpecURL: toolingSpecURL)
        )
        let moduleName = self.moduleName

        let result = await SANYRunner.shared.analyze(
            specFileURL: toolingSpecURL,
            searchPaths: searchPaths
        )

        // Commit only if this is still the newest check and the document is alive.
        guard generation == semanticCheckGeneration, !isClosed, !Task.isCancelled else { return }

        switch result {
        case .unavailable(let reason):
            // Toolchain missing: semantic analysis is silently off; syntax
            // diagnostics keep working. Don't surface anything in the UI.
            logger.info("Semantic analysis unavailable: \(reason, privacy: .public)")
            updateSemanticDiagnostics([])
        case .failure(let error):
            logger.warning("Semantic analysis failed: \(error.localizedDescription)")
            updateSemanticDiagnostics([])
        case .success(let stdout, let stderr, _):
            let parsed = SANYOutputParser.parse(
                stdout: stdout,
                stderr: stderr,
                moduleName: moduleName
            )
            updateSemanticDiagnostics(parsed)
        }
    }

    @MainActor
    private func updateSemanticDiagnostics(_ newDiagnostics: [TLADiagnostic]) {
        guard semanticDiagnostics != newDiagnostics else { return }
        semanticDiagnostics = newDiagnostics
        publishDiagnostics()
    }

    // MARK: - Interactive Simulation

    /// Start (or restart) an interactive simulation of the current spec.
    /// Snapshots the buffer, model config, and Next-action decomposition; later
    /// edits don't affect the running session until it is restarted.
    @MainActor
    func startSimulation() {
        guard !isClosed else { return }
        simulationError = nil
        simulationSession?.invalidate()
        SecureTempFile.cleanupContainer(for: simulationToolingSpecURL)
        simulationToolingSpecURL = nil

        let toolingSpecURL: URL
        do {
            toolingSpecURL = try specURLForTooling()
        } catch {
            simulationError = "Could not prepare the spec for simulation: \(error.localizedDescription)"
            simulationSession = nil
            return
        }
        if SecureTempFile.isManagedTemporaryFile(toolingSpecURL) {
            simulationToolingSpecURL = toolingSpecURL
        }

        let config = resolvedModelConfig()
        let nextName = config.nextAction.isEmpty ? "Next" : config.nextAction

        var actions: [SimActionDefinition]?
        if let definition = definitionText(forOperator: nextName),
           let body = NextActionDecomposer.body(ofDefinition: definition) {
            actions = NextActionDecomposer.decompose(
                nextBody: body.body,
                bodyStartColumn: body.startColumn
            )
        }

        let context = SimulationSpecContext(
            userModuleName: moduleName,
            searchPaths: ProjectModuleResolver.searchPaths(
                for: toolingSpecURL,
                extraDirectories: originalDirectoryLibraryPaths(forToolingSpecURL: toolingSpecURL)
            ),
            config: config,
            actions: actions
        )

        let session = SimulationSession(context: context)
        simulationSession = session
        session.start()
    }

    @MainActor
    func stopSimulation() {
        simulationSession?.invalidate()
        simulationSession = nil
        SecureTempFile.cleanupContainer(for: simulationToolingSpecURL)
        simulationToolingSpecURL = nil
    }

    // MARK: - Proof Assist

    /// Apply a planned `BY DEF` edit. Returns false (no mutation) when the
    /// target line changed since the plan was computed.
    @MainActor
    @discardableResult
    func applyByDefInsertion(_ insertion: ProofAssist.ByDefInsertion) -> Bool {
        var lines = content.components(separatedBy: "\n")
        guard insertion.lineIndex >= 0,
              insertion.lineIndex < lines.count,
              lines[insertion.lineIndex] == insertion.originalLine else {
            reportActionFeedback("The proof step changed since these suggestions were computed — re-run the check.", style: .warning)
            return false
        }
        lines[insertion.lineIndex] = insertion.updatedLine
        content = lines.joined(separator: "\n")
        return true
    }

    /// Proof→TLC bridge: model-check a named state predicate as the sole
    /// invariant. A counterexample means the theorem is false; a clean run
    /// means the proof (not the property) needs work.
    ///
    /// One-shot: the bridge config must NOT become `activeModelConfig`, or the
    /// user's next plain ⌘R would silently re-run it instead of their model.
    @MainActor
    func modelCheckInvariant(named name: String) {
        var config = resolvedModelConfig()
        config.invariants = [name]
        config.temporalProperties = []
        let previousActiveConfig = activeModelConfig
        runModelCheck(config: config)
        activeModelConfig = previousActiveConfig
        NotificationCenter.default.post(name: .showModelCheckPanel, object: self)
    }

    /// Insert a proof skeleton for the theorem at the cursor ("Decompose
    /// Proof"). Returns false when no theorem is found, the goal shape isn't
    /// recognized, or a proof already exists.
    @MainActor
    @discardableResult
    func decomposeProof() -> Bool {
        let (line, _) = lineAndColumn(for: selectedRange.location)
        guard let insertion = ProofSkeletonGenerator.skeleton(
            forTheoremAtLine: line,
            content: content,
            symbols: symbols
        ) else {
            return false
        }
        var lines = content.components(separatedBy: "\n")
        guard insertion.insertAfterLine < lines.count else { return false }
        lines.insert(contentsOf: insertion.lines, at: insertion.insertAfterLine + 1)
        content = lines.joined(separator: "\n")
        return true
    }

    /// Full source text (whole lines) of the definition of the named operator,
    /// from the latest parse. Whole lines preserve the file's columns, which
    /// the Next-action decomposer needs for junction-list alignment.
    private func definitionText(forOperator name: String) -> String? {
        guard let symbol = symbols.first(where: { $0.name == name }) else { return nil }
        let lines = content.components(separatedBy: "\n")
        let startLine = Int(symbol.range.start.line)
        let endLine = Int(symbol.range.end.line)
        guard startLine <= endLine, endLine < lines.count else { return nil }
        return lines[startLine...endLine].joined(separator: "\n")
    }

    // MARK: - Model Checking

    private func detectedModelInvariants() -> [String] {
        symbols.filter {
            $0.name == "TypeOK" || $0.name == "TypeInvariant" ||
            $0.name.contains("Invariant") || $0.name.contains("Safe")
        }
        .map(\.name)
    }

    @MainActor
    func resolvedModelConfig(for specURL: URL? = nil, override overrideConfig: ModelConfig? = nil) -> ModelConfig {
        let resolvedSpecURL = specURL ?? fileURL ?? URL(fileURLWithPath: "/tmp/untitled.tla")
        let configURL = resolvedSpecURL.deletingPathExtension().appendingPathExtension("cfg")
        let parsedConfig = ModelConfig.parse(from: configURL)
        let settings = UserSettings.shared

        var config = overrideConfig
            ?? activeModelConfig
            ?? modelConfigStore.selectedConfig?.config
            ?? modelConfigStore.config(named: "Default")
            ?? ModelConfig(
                name: "Default",
                specFile: resolvedSpecURL,
                specification: parsedConfig?.specification,
                initPredicate: parsedConfig?.initPredicate ?? "Init",
                nextAction: parsedConfig?.nextAction ?? "Next",
                constants: parsedConfig?.constants ?? [:],
                invariants: parsedConfig?.invariants ?? [],
                temporalProperties: parsedConfig?.temporalProperties ?? [],
                stateConstraint: parsedConfig?.stateConstraint,
                actionConstraint: parsedConfig?.actionConstraint,
                symmetrySets: parsedConfig?.symmetrySets ?? [:],
                workers: max(1, settings.tlcWorkers),
                checkpointInterval: TimeInterval(max(5, settings.tlcCheckpointInterval) * 60),
                checkpointEnabled: settings.tlcCheckpointEnabled
            )

        config.specFile = resolvedSpecURL

        if config.name.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
            config.name = "Default"
        }

        let specification = config.specification?.trimmingCharacters(in: .whitespacesAndNewlines)
        let initPredicate = config.initPredicate.trimmingCharacters(in: .whitespacesAndNewlines)
        let nextAction = config.nextAction.trimmingCharacters(in: .whitespacesAndNewlines)

        if (specification == nil || specification?.isEmpty == true)
            && initPredicate.isEmpty
            && nextAction.isEmpty {
            config.specification = parsedConfig?.specification
            config.initPredicate = parsedConfig?.initPredicate ?? "Init"
            config.nextAction = parsedConfig?.nextAction ?? "Next"
        } else if specification == nil || specification?.isEmpty == true {
            if initPredicate.isEmpty {
                config.initPredicate = parsedConfig?.initPredicate ?? "Init"
            }
            if nextAction.isEmpty {
                config.nextAction = parsedConfig?.nextAction ?? "Next"
            }
        }

        return config
    }

    /// Run TLC model checker on this document
    /// - Parameters:
    ///   - config: Explicit model configuration to run. Falls back to the active/default config when nil.
    ///   - binaryMode: TLC binary mode to use (default: uses document's selectedTLCMode)
    @MainActor
    func runModelCheck(
        config overrideConfig: ModelConfig? = nil,
        binaryMode: TLCProcessManager.TLCBinaryMode? = nil
    ) {
        let mode = binaryMode ?? selectedTLCMode
        let specURL: URL
        do {
            specURL = try specURLForTooling()
        } catch {
            logger.error("Unable to prepare spec for TLC: \(error.localizedDescription)")
            reportActionFeedback("Couldn't prepare the spec for model checking: \(error.localizedDescription)", style: .error)
            return
        }

        var config = resolvedModelConfig(for: fileURL ?? specURL, override: overrideConfig)
        activeModelConfig = config
        config.specFile = specURL
        lastTLCResult = nil

        // Create and start session with specified mode
        let session = TLCSession(
            specURL: specURL,
            config: config,
            binaryMode: mode,
            additionalLibraryPaths: originalDirectoryLibraryPaths(forToolingSpecURL: specURL)
        )
        let toolingSpecURL = SecureTempFile.isManagedTemporaryFile(specURL) ? specURL : nil
        replaceModelCheckSession(with: session)
        tlcToolingSpecURL = toolingSpecURL
        session.start()
        watchModelCheckSession(session)
    }

    /// Resume TLC model checking from a checkpoint using the same document-owned
    /// lifecycle as a normal run.
    @MainActor
    func resumeModelCheck(
        from checkpoint: CheckpointInfo,
        config overrideConfig: ModelConfig? = nil,
        binaryMode: TLCProcessManager.TLCBinaryMode? = nil
    ) {
        let mode = binaryMode ?? selectedTLCMode
        let specURL: URL
        do {
            specURL = try specURLForTooling()
        } catch {
            logger.error("Unable to prepare spec for TLC checkpoint recovery: \(error.localizedDescription)")
            return
        }

        var config = resolvedModelConfig(for: fileURL ?? specURL, override: overrideConfig)
        config.checkpointDir = checkpoint.directoryURL.deletingLastPathComponent()
        activeModelConfig = config
        config.specFile = specURL
        lastTLCResult = nil

        let session = TLCSession(
            specURL: specURL,
            config: config,
            binaryMode: mode,
            additionalLibraryPaths: originalDirectoryLibraryPaths(forToolingSpecURL: specURL)
        )
        let toolingSpecURL = SecureTempFile.isManagedTemporaryFile(specURL) ? specURL : nil
        replaceModelCheckSession(with: session)
        tlcToolingSpecURL = toolingSpecURL
        session.resume(from: checkpoint)
        watchModelCheckSession(session)
    }

    /// Stop the current TLC session synchronously
    @MainActor
    func stopModelCheck() {
        tlcSession?.stop()
    }

    /// Stop the current TLC session and wait for async cleanup
    @MainActor
    func stopModelCheckAsync() async {
        await tlcSession?.stopAsync()
    }

    // MARK: - Proof Checking

    /// Run TLAPS proof checker on this document
    @MainActor
    func runProofCheck() {
        // Offer to install missing proof backends the first time a proof runs. Non-blocking:
        // the proof still proceeds with whatever backends are already present.
        ProofSetupCoordinator.shared.maybePresentBeforeFirstProof()

        let specURL: URL
        do {
            specURL = try specURLForTooling()
        } catch {
            logger.error("Unable to prepare spec for TLAPS: \(error.localizedDescription)")
            reportActionFeedback("Couldn't prepare the spec for proof checking: \(error.localizedDescription)", style: .error)
            return
        }

        lastProofResult = nil
        proofAnnotationManager.updateAnnotations(for: [])

        var options = currentProofCheckOptions()
        options.additionalLibraryPaths = originalDirectoryLibraryPaths(forToolingSpecURL: specURL)

        // Create and start session
        let session = ProofSession(specURL: specURL, options: options)
        let toolingSpecURL = SecureTempFile.isManagedTemporaryFile(specURL) ? specURL : nil
        replaceProofSession(with: session)
        proofToolingSpecURL = toolingSpecURL
        session.start()
        watchProofSession(session)
    }

    /// Check a single proof step at the current editor selection
    @MainActor
    func checkSelectionProofStep() {
        let location = selectedRange.location
        guard location != NSNotFound else {
            logger.debug("checkSelectionProofStep: Selection unavailable")
            return
        }

        let (line, column) = lineAndColumn(for: location)
        logger.debug("checkSelectionProofStep: selection at line=\(line + 1), column=\(column + 1)")

        let specURL: URL
        do {
            specURL = try specURLForTooling()
        } catch {
            logger.error("Unable to prepare spec for TLAPS step check: \(error.localizedDescription)")
            reportActionFeedback("Couldn't prepare the spec for the proof step check: \(error.localizedDescription)", style: .error)
            return
        }

        // Create or reuse session
        let currentSession = proofSession
        let session: ProofSession
        let toolingSpecURL = SecureTempFile.isManagedTemporaryFile(specURL) ? specURL : nil
        if let currentSession, currentSession.specURL == specURL {
            guard !currentSession.isRunning else { return }
            session = currentSession
        } else {
            var options = currentProofCheckOptions()
            options.additionalLibraryPaths = originalDirectoryLibraryPaths(forToolingSpecURL: specURL)
            session = ProofSession(specURL: specURL, options: options)
            replaceProofSession(with: session)
            self.proofToolingSpecURL = toolingSpecURL
        }
        var options = currentProofCheckOptions()
        options.additionalLibraryPaths = originalDirectoryLibraryPaths(forToolingSpecURL: specURL)
        session.options = options
        lastProofResult = nil

        session.checkStep(line: line + 1, column: column + 1) // Convert to 1-based
        watchProofSession(session)
    }

    /// Stop the current proof checking session synchronously
    @MainActor
    func stopProofCheck() {
        proofSession?.stop()
    }

    /// Stop the current proof checking session and wait for async cleanup
    @MainActor
    func stopProofCheckAsync() async {
        await proofSession?.stopAsync()
    }

    /// Jump the editor to the next failed/timed-out obligation after the
    /// cursor, wrapping. (The previous implementation delegated to
    /// ProofAnnotationManager.navigateToNextFailed(), whose editor hook was
    /// never wired — the menu item was a silent no-op; platform review C3.)
    @MainActor
    func goToNextFailedProof() {
        guard let failed = proofSession?.failedObligations, !failed.isEmpty else {
            reportActionFeedback("No failed proof obligations to jump to.", style: .info)
            return
        }
        let currentLine = lineAndColumn(for: selectedRange.location).line + 1   // 1-based
        let sorted = failed.sorted { $0.location.startLine < $1.location.startLine }
        let target = sorted.first { $0.location.startLine > currentLine } ?? sorted[0]
        let targetOffset = offset(
            forLine: max(0, target.location.startLine - 1),
            column: max(0, target.location.startColumn - 1)
        )
        selectedRange = NSRange(location: targetOffset, length: 0)
    }

    // MARK: - PlusCal Translation

    /// Whether a PlusCal translation is currently in progress
    @Published var isTranslatingPlusCal = false

    /// Translate PlusCal algorithm in the current document
    @MainActor
    func translatePlusCal() {
        guard !isTranslatingPlusCal else { return }

        let originalContent = content
        let originalSelection = selectedRange
        isTranslatingPlusCal = true

        Task { @MainActor in
            defer { isTranslatingPlusCal = false }

            let result = await PlusCalTranslator.shared.translate(
                content: content,
                specURL: fileURL
            )

            switch result {
            case .success(let translatedContent):
                content = translatedContent
                selectedRange = PlusCalSourceMapping.remapSelection(
                    originalSelection,
                    from: originalContent,
                    to: translatedContent
                ) ?? originalSelection
                logger.info("PlusCal translation applied successfully")

            case .noChangeNeeded:
                logger.info("PlusCal translation: no changes needed")

            case .error(let message):
                logger.error("PlusCal translation error: \(message)")
                presentPlusCalTranslationError(message)
            }
        }
    }

    @MainActor
    @discardableResult
    func goToPlusCalAlgorithm() -> Bool {
        guard let range = PlusCalSourceMapping.range(for: .algorithm, in: content) else {
            return false
        }
        selectedRange = NSRange(location: range.location, length: 0)
        return true
    }

    @MainActor
    @discardableResult
    func goToPlusCalTranslation() -> Bool {
        guard let range = PlusCalSourceMapping.range(for: .translation, in: content) else {
            return false
        }
        selectedRange = NSRange(location: range.location, length: 0)
        return true
    }

    // MARK: - Helper Methods

    private func detectLineEnding(in text: String) -> LineEnding {
        if text.contains("\r\n") { return .crlf }
        if text.contains("\r") { return .cr }
        return .lf
    }

    private func updateModuleNameFromFilename(_ name: String) {
        let pattern = #"----+ MODULE \w+ ----+"#
        if let range = content.range(of: pattern, options: .regularExpression) {
            let newHeader = String(repeating: "-", count: 32) +
                           " MODULE \(name) " +
                           String(repeating: "-", count: 32)
            content = content.replacingCharacters(in: range, with: newHeader)
        }
    }

    private func currentProofCheckOptions() -> ProofCheckOptions {
        let settings = UserSettings.shared
        let backend = ProverBackend(rawValue: settings.defaultProverBackend)

        return ProofCheckOptions(
            backend: backend == .auto ? nil : backend,
            timeout: TimeInterval(max(1, settings.defaultProverTimeout)),
            threads: max(1, min(4, ProcessInfo.processInfo.activeProcessorCount))
        )
    }

    private func specURLForTooling() throws -> URL {
        if let fileURL, !isDocumentEdited {
            return fileURL
        }

        // TLA+ SANY rejects files whose basename doesn't match the `MODULE <name>` declaration,
        // so the temp file must be named exactly `<moduleName>.tla` (not prefix-UUID.tla).
        return try SecureTempFile.createWithExactName(
            name: moduleName,
            extension: "tla",
            content: content
        )
    }

    private func originalDirectoryLibraryPaths(forToolingSpecURL toolingSpecURL: URL) -> [URL] {
        guard SecureTempFile.isManagedTemporaryFile(toolingSpecURL),
              let fileURL else {
            return []
        }
        return [fileURL.deletingLastPathComponent()]
    }

    @MainActor
    private func replaceModelCheckSession(with session: TLCSession) {
        tlcWatchTask?.cancel()
        tlcWatchTask = nil

        // Defer subprocess termination off the MainActor: ProcessRegistry.terminate
        // blocks up to ~1s (SIGTERM → SIGKILL escalation), which would stall the UI
        // every time the user presses Run while a previous run is still alive.
        // Mirrors the `close()` pattern hardened on 2026-04-16.
        let tlcSessionToStop = tlcSession
        let toolingSpecURLToCleanup = tlcToolingSpecURL
        tlcSession = session
        tlcToolingSpecURL = nil

        if tlcSessionToStop != nil {
            Task.detached {
                await tlcSessionToStop?.stopAsync()
                SecureTempFile.cleanupContainer(for: toolingSpecURLToCleanup)
            }
        } else {
            SecureTempFile.cleanupContainer(for: toolingSpecURLToCleanup)
        }
    }

    @MainActor
    private func replaceProofSession(with session: ProofSession) {
        proofWatchTask?.cancel()
        proofWatchTask = nil

        // Defer subprocess termination off the MainActor — see comment in
        // `replaceModelCheckSession` for rationale.
        let proofSessionToStop = proofSession
        let toolingSpecURLToCleanup = proofToolingSpecURL
        proofSession = session
        proofToolingSpecURL = nil

        if proofSessionToStop != nil {
            Task.detached {
                await proofSessionToStop?.stopAsync()
                SecureTempFile.cleanupContainer(for: toolingSpecURLToCleanup)
            }
        } else {
            SecureTempFile.cleanupContainer(for: toolingSpecURLToCleanup)
        }
    }

    @MainActor
    private func watchModelCheckSession(_ session: TLCSession) {
        tlcWatchTask?.cancel()
        tlcWatchTask = Task { @MainActor [weak self] in
            while session.isRunning {
                try? await Task.sleep(nanoseconds: 100_000_000)
                if Task.isCancelled { return }
                guard self != nil else { return }
            }
            // Commit the final result only if this task is still the active watcher
            // for the current session — guards against a stale task clobbering state
            // after the user has already started a new run.
            guard !Task.isCancelled,
                  let self,
                  self.tlcSession === session else { return }
            self.lastTLCResult = session.result
            SecureTempFile.cleanupContainer(for: self.tlcToolingSpecURL)
            self.tlcToolingSpecURL = nil
        }
    }

    @MainActor
    private func watchProofSession(_ session: ProofSession) {
        proofWatchTask?.cancel()
        proofWatchTask = Task { @MainActor [weak self] in
            while session.isRunning {
                try? await Task.sleep(nanoseconds: 100_000_000)
                if Task.isCancelled { return }
                guard let self, self.proofSession === session else { return }
                self.proofAnnotationManager.updateAnnotations(for: session.obligations)
            }
            guard !Task.isCancelled,
                  let self,
                  self.proofSession === session else { return }
            self.lastProofResult = session.result
            self.proofAnnotationManager.updateAnnotations(for: session.obligations)
            SecureTempFile.cleanupContainer(for: self.proofToolingSpecURL)
            self.proofToolingSpecURL = nil
        }
    }

    @MainActor
    private func presentPlusCalTranslationError(_ message: String) {
        let alert = NSAlert()
        alert.messageText = "PlusCal Translation Failed"
        alert.informativeText = message
        alert.alertStyle = .warning
        alert.addButton(withTitle: "OK")

        if let window = windowControllers.first?.window {
            alert.beginSheetModal(for: window) { _ in }
        } else {
            alert.runModal()
        }
    }

    // MARK: - Public API

    /// Rebuilds the line offset index if content has changed. O(n) but only on content change.
    private func rebuildLineIndexIfNeeded(using text: String? = nil) {
        guard lineIndexNeedsRebuild else { return }

        let currentContent = text ?? content
        let analysis = TextCoordinateMapper.analyze(currentContent)
        lineStartOffsets = analysis.lineStartOffsets
        contentIsASCII = analysis.isASCII
        contentUTF16Length = analysis.utf16Length
        lineIndexNeedsRebuild = false
    }

    /// Get the current line and column for a UTF-16 editor offset.
    /// Lines and columns are reported in logical Swift characters.
    func lineAndColumn(for offset: Int) -> (line: Int, column: Int) {
        let currentContent = content
        rebuildLineIndexIfNeeded(using: currentContent)

        if contentIsASCII {
            let clampedOffset = max(0, min(offset, contentUTF16Length))
            let line = TextCoordinateMapper.lineIndex(forUTF16Offset: clampedOffset, in: lineStartOffsets)
            return (line, clampedOffset - lineStartOffsets[line])
        }

        return TextCoordinateMapper.lineAndColumn(
            forUTF16Offset: offset,
            in: currentContent,
            lineStartOffsets: lineStartOffsets
        )
    }

    var totalLineCount: Int {
        rebuildLineIndexIfNeeded(using: content)
        return lineStartOffsets.count
    }

    /// Get the UTF-16 editor offset for a logical line and column.
    func offset(forLine line: Int, column: Int) -> Int {
        let currentContent = content
        rebuildLineIndexIfNeeded(using: currentContent)

        if contentIsASCII {
            let clampedLine = max(0, line)
            guard clampedLine < lineStartOffsets.count else {
                return contentUTF16Length
            }

            let lineStart = lineStartOffsets[clampedLine]
            let lineEnd: Int
            if clampedLine + 1 < lineStartOffsets.count {
                lineEnd = max(lineStart, lineStartOffsets[clampedLine + 1] - 1)
            } else {
                lineEnd = contentUTF16Length
            }

            let clampedColumn = max(0, min(column, lineEnd - lineStart))
            return lineStart + clampedColumn
        }

        return TextCoordinateMapper.utf16Offset(
            forLine: line,
            column: column,
            in: currentContent,
            lineStartOffsets: lineStartOffsets
        )
    }

    // MARK: - Go To Definition

    /// Navigate to the definition of the symbol at the given character offset.
    /// First checks local definitions, then tries cross-module navigation for EXTENDS'd modules.
    /// Returns true if a definition was found and navigated to.
    @MainActor
    @discardableResult
    func goToDefinition(at characterOffset: Int) -> Bool {
        let (line, column) = lineAndColumn(for: characterOffset)
        let position = TLAPosition(line: UInt32(line), column: UInt32(column))

        // Get the word at the cursor position
        guard let word = TLACoreWrapper.shared.wordAt(position: position, in: content) else {
            return false
        }

        // Try local definition first
        if let definitionRange = TLACoreWrapper.shared.findDefinition(named: word, in: symbols) {
            let targetOffset = offset(forLine: Int(definitionRange.start.line), column: Int(definitionRange.start.column))
            selectedRange = NSRange(location: targetOffset, length: 0)
            delegate?.documentDidNavigate(self, to: definitionRange)
            return true
        }

        // Check if the word is an EXTENDS'd module name — try to open it.
        if Self.extendedModuleNames(in: content).contains(word) {
            let specDir = fileURL?.deletingLastPathComponent()
            if let moduleURL = BinaryDiscovery.findModule(named: word, specDirectory: specDir) {
                NSDocumentController.shared.openDocument(
                    withContentsOf: moduleURL,
                    display: true
                ) { _, _, _ in }
                return true
            }
        }

        // Symbol defined in an EXTENDS'd module: open the file and jump to
        // the definition line.
        if let target = crossModuleDefinitionTarget(for: word) {
            openAndNavigate(to: target)
            return true
        }

        // Nothing found — kick a staleness probe so a cold index catches up
        // for the next attempt.
        crossModuleProvider.refreshIfStaleInBackground()
        return false
    }

    /// First snapshot match for a name (BFS order = nearest module wins).
    /// Pure lookup, separated from `goToDefinition` for testability.
    func crossModuleDefinitionTarget(for word: String) -> ModuleSymbol? {
        crossModuleProvider.symbols.first { $0.symbol.name == word }
    }

    @MainActor
    private func openAndNavigate(to target: ModuleSymbol) {
        DocumentNavigator.open(fileURL: target.fileURL) { targetDocument in
            // If the target document was already open (possibly edited),
            // its live symbols are fresher than the index's on-disk range.
            TLACoreWrapper.shared.findDefinition(
                named: target.symbol.name,
                in: targetDocument.symbols
            ) ?? target.symbol.selectionRange ?? target.symbol.range
        }
    }

    static func extendedModuleNames(in content: String) -> Set<String> {
        var moduleNames = Set<String>()
        var collectingContinuation = false

        for rawLine in content.components(separatedBy: .newlines) {
            let line = strippingLineComment(from: rawLine)

            if let extendsRange = line.range(
                of: #"\bEXTENDS\b"#,
                options: .regularExpression
            ) {
                let fragment = String(line[extendsRange.upperBound...])
                collectingContinuation = collectExtendedModuleNames(
                    from: fragment,
                    into: &moduleNames
                )
                continue
            }

            guard collectingContinuation else { continue }

            let trimmed = line.trimmingCharacters(in: .whitespaces)
            if trimmed.isEmpty {
                continue
            }

            guard isValidExtendsContinuation(trimmed) else {
                collectingContinuation = false
                continue
            }

            collectingContinuation = collectExtendedModuleNames(
                from: trimmed,
                into: &moduleNames
            )
        }

        return moduleNames
    }

    private static func strippingLineComment(from line: String) -> String {
        line.components(separatedBy: "\\*").first ?? line
    }

    private static func collectExtendedModuleNames(
        from fragment: String,
        into moduleNames: inout Set<String>
    ) -> Bool {
        let trimmed = fragment.trimmingCharacters(in: .whitespaces)
        guard !trimmed.isEmpty else { return false }

        let endsWithComma = trimmed.hasSuffix(",")
        let candidates = trimmed
            .split(separator: ",", omittingEmptySubsequences: true)
            .map { $0.trimmingCharacters(in: .whitespaces) }

        guard !candidates.isEmpty else { return false }

        for candidate in candidates where isValidModuleIdentifier(candidate) {
            moduleNames.insert(candidate)
        }

        return endsWithComma
    }

    private static func isValidExtendsContinuation(_ line: String) -> Bool {
        let candidates = line
            .split(separator: ",", omittingEmptySubsequences: true)
            .map { $0.trimmingCharacters(in: .whitespaces) }

        guard !candidates.isEmpty else { return false }
        return candidates.allSatisfy(isValidModuleIdentifier)
    }

    private static func isValidModuleIdentifier(_ candidate: String) -> Bool {
        guard !candidate.isEmpty else { return false }
        return candidate.range(
            of: #"^[A-Za-z_][A-Za-z0-9_]*$"#,
            options: .regularExpression
        ) != nil
    }

    /// Get the symbol at a given character offset, if any
    func symbolAt(characterOffset: Int) -> TLASymbol? {
        let (line, column) = lineAndColumn(for: characterOffset)
        let position = TLAPosition(line: UInt32(line), column: UInt32(column))

        guard let word = TLACoreWrapper.shared.wordAt(position: position, in: content) else {
            return nil
        }

        return symbols.firstInTree { $0.name == word }
    }
}

// MARK: - Supporting Types

enum LineEnding {
    case lf    // Unix (macOS)
    case crlf  // Windows
    case cr    // Legacy Mac
}

protocol TLADocumentDelegate: AnyObject {
    func documentDidParse(_ document: TLADocument)
    func documentContentDidChange(_ document: TLADocument)
    func documentDidNavigate(_ document: TLADocument, to range: TLARange)
}

// Default implementations
extension TLADocumentDelegate {
    func documentDidParse(_ document: TLADocument) {}
    func documentContentDidChange(_ document: TLADocument) {}
    func documentDidNavigate(_ document: TLADocument, to range: TLARange) {}
}

// Notification.Name declarations are centralized in Utilities/NotificationNames.swift
