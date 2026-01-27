import AppKit
import UniformTypeIdentifiers
import Combine

// MARK: - TLADocument

/// Primary document class for TLA+ specification files.
/// See Docs/architecture/01-document-management.md for full specification.
final class TLADocument: NSDocument, ObservableObject {

    // MARK: - Document State

    /// Raw text content of the specification
    @Published var content: String = "" {
        didSet {
            if content != oldValue {
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

    /// Diagnostics (errors, warnings)
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
    private var cancellables = Set<AnyCancellable>()

    // MARK: - Line Offset Index (Performance Optimization)

    /// Cached line start offsets for O(log n) line/offset conversions.
    /// Index i contains the character offset where line i starts (0-indexed).
    /// Line 0 always starts at offset 0.
    private var lineStartOffsets: [Int] = [0]

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
    }

    private func setContentWithoutTriggeringChange(_ text: String) {
        // Temporarily remove the change observer
        let oldValue = content
        content = text
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
        try super.write(to: url, ofType: typeName, for: saveOperation,
                        originalContentsURL: originalContentsURL)

        // Update module name on Save As
        if saveOperation == .saveAsOperation {
            updateModuleNameFromFilename(url.deletingPathExtension().lastPathComponent)
        }
    }

    // MARK: - Window Controller

    override func makeWindowControllers() {
        let windowController = TLAWindowController(document: self)
        addWindowController(windowController)
    }

    // MARK: - Close Handling

    override func canClose(
        withDelegate delegate: Any,
        shouldClose shouldCloseSelector: Selector?,
        contextInfo: UnsafeMutableRawPointer?
    ) {
        cancelActiveOperations()
        super.canClose(withDelegate: delegate,
                       shouldClose: shouldCloseSelector,
                       contextInfo: contextInfo)
    }

    override func close() {
        // Cancel all running tasks first to prevent any new state updates
        let parseTaskToCancel = parseTask
        let tlcWatchTaskToCancel = tlcWatchTask
        let proofWatchTaskToCancel = proofWatchTask

        parseTask = nil
        tlcWatchTask = nil
        proofWatchTask = nil

        parseTaskToCancel?.cancel()
        tlcWatchTaskToCancel?.cancel()
        proofWatchTaskToCancel?.cancel()

        // Stop active sessions - these use ProcessRegistry for synchronous termination
        // Capture and nil first to prevent race conditions
        let tlcSessionToStop = tlcSession
        let proofSessionToStop = proofSession

        tlcSession = nil
        proofSession = nil

        tlcSessionToStop?.stop()
        proofSessionToStop?.stop()

        // Clear all Combine subscriptions before clearing state
        cancellables.removeAll()

        // Clear state
        parseResult = nil
        symbols = []
        diagnostics = []
        lastTLCResult = nil
        lastProofResult = nil
        proofAnnotationManager = ProofAnnotationManager()  // Reset annotation manager

        delegate = nil

        super.close()
    }

    // MARK: - Parsing

    private func contentDidChange() {
        lineIndexNeedsRebuild = true
        delegate?.documentContentDidChange(self)
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
            let result = try await TLACoreWrapper.shared.parse(content)
            self.parseResult = result
            self.diagnostics = result.diagnostics

            // Extract symbols
            self.symbols = await TLACoreWrapper.shared.getSymbols(from: result)

            delegate?.documentDidParse(self)
        } catch {
            // Handle parse error
            self.diagnostics = [TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 0)
                ),
                severity: .error,
                message: error.localizedDescription,
                code: nil
            )]
        }
    }

    // MARK: - Model Checking

    /// Run TLC model checker on this document
    /// - Parameter binaryMode: TLC binary mode to use (default: uses document's selectedTLCMode)
    @MainActor
    func runModelCheck(binaryMode: TLCProcessManager.TLCBinaryMode? = nil) {
        let mode = binaryMode ?? selectedTLCMode

        // Get spec URL (save to temp if unsaved)
        let specURL: URL
        if let fileURL = self.fileURL {
            specURL = fileURL
        } else {
            do {
                specURL = try SecureTempFile.create(prefix: moduleName, extension: "tla", content: content)
            } catch {
                return
            }
        }

        // Try to load existing .cfg file
        let configURL = specURL.deletingPathExtension().appendingPathExtension("cfg")
        let existingConfig = ModelConfig.parse(from: configURL)

        // Detect invariants from symbols
        let detectedInvariants = symbols.filter {
            $0.name == "TypeOK" || $0.name == "TypeInvariant" ||
            $0.name.contains("Invariant") || $0.name.contains("Safe")
        }.map { $0.name }

        // Merge existing config with detected invariants
        let constants = existingConfig?.constants ?? [:]
        var invariants = existingConfig?.invariants ?? []
        for inv in detectedInvariants {
            if !invariants.contains(inv) {
                invariants.append(inv)
            }
        }

        // Create config
        let config = ModelConfig(
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

        // Cancel any existing watch task
        tlcWatchTask?.cancel()

        // Create and start session with specified mode
        let session = TLCSession(specURL: specURL, config: config, binaryMode: mode)
        self.tlcSession = session
        session.start()

        // Watch for completion (store task for cleanup)
        // The weak self check prevents orphaned loops if document deallocates
        tlcWatchTask = Task { @MainActor [weak self] in
            while session.isRunning {
                try? await Task.sleep(nanoseconds: 100_000_000) // 100ms
                if Task.isCancelled { return }
                // Exit if document deallocated (prevents orphaned loop)
                guard self != nil else { return }
            }
            self?.lastTLCResult = session.result
            self?.tlcWatchTask = nil
        }
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

        // Get spec URL (save to temp if unsaved)
        let specURL: URL
        if let fileURL = self.fileURL {
            specURL = fileURL
        } else {
            do {
                specURL = try SecureTempFile.create(prefix: moduleName, extension: "tla", content: content)
            } catch {
                return
            }
        }

        // Cancel any existing watch task
        proofWatchTask?.cancel()

        // Create and start session
        let session = ProofSession(specURL: specURL)
        self.proofSession = session
        session.start()

        // Watch for completion (store task for cleanup)
        // The weak self check prevents orphaned loops if document deallocates
        proofWatchTask = Task { @MainActor [weak self] in
            while session.isRunning {
                try? await Task.sleep(nanoseconds: 100_000_000) // 100ms
                if Task.isCancelled { return }
                // Exit if document deallocated (prevents orphaned loop)
                guard let strongSelf = self else { return }
                // Update annotations while running
                strongSelf.proofAnnotationManager.updateAnnotations(for: session.obligations)
            }
            self?.lastProofResult = session.result
            self?.proofAnnotationManager.updateAnnotations(for: session.obligations)
            self?.proofWatchTask = nil
        }
    }

    /// Check a single proof step at the current editor selection
    @MainActor
    func checkSelectionProofStep() {
        guard let fileURL = self.fileURL else {
            return
        }

        // Get selection directly from the first responder text view
        guard let window = NSApp.keyWindow,
              let textView = window.firstResponder as? NSTextView else {
            NSLog("[TLADocument] checkSelectionProofStep: No text view found")
            return
        }

        let selection = textView.selectedRange()
        let location = selection.location

        guard location != NSNotFound else {
            NSLog("[TLADocument] checkSelectionProofStep: No selection")
            return
        }

        let (line, column) = lineAndColumn(for: location)
        NSLog("[TLADocument] checkSelectionProofStep: selection at line=%d, column=%d", line + 1, column + 1)

        // Create or reuse session
        let session = proofSession ?? ProofSession(specURL: fileURL)
        if proofSession == nil {
            self.proofSession = session
        }

        session.checkStep(line: line + 1, column: column + 1) // Convert to 1-based
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

    /// Navigate to the next failed proof obligation
    @MainActor
    func goToNextFailedProof() {
        proofAnnotationManager.navigateToNextFailed()
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

    private func cancelActiveOperations() {
        // Cancel parse task
        parseTask?.cancel()

        // Cancel watch tasks
        tlcWatchTask?.cancel()
        proofWatchTask?.cancel()

        // Stop any running sessions (synchronous via ProcessRegistry)
        tlcSession?.stop()
        proofSession?.stop()

        NotificationCenter.default.post(name: .documentWillClose, object: self)
    }

    // MARK: - Public API

    /// Rebuilds the line offset index if content has changed. O(n) but only on content change.
    private func rebuildLineIndexIfNeeded() {
        guard lineIndexNeedsRebuild else { return }

        lineStartOffsets = [0]
        lineStartOffsets.reserveCapacity(content.count / 40 + 1) // Estimate ~40 chars per line

        var offset = 0
        for char in content {
            offset += 1
            if char == "\n" {
                lineStartOffsets.append(offset)
            }
        }

        lineIndexNeedsRebuild = false
    }

    /// Get the current line and column for a character offset.
    /// Uses cached line index for O(log n) lookup instead of O(n) string splitting.
    /// Returns (0, 0) for invalid offsets (negative or beyond content).
    func lineAndColumn(for offset: Int) -> (line: Int, column: Int) {
        rebuildLineIndexIfNeeded()

        // Validate input: clamp to valid range
        let clampedOffset = max(0, min(offset, content.count))

        // Handle empty content
        guard !lineStartOffsets.isEmpty else {
            return (0, 0)
        }

        // Binary search for the largest line start <= offset
        var low = 0
        var high = lineStartOffsets.count - 1

        while low < high {
            let mid = (low + high + 1) / 2
            if lineStartOffsets[mid] <= clampedOffset {
                low = mid
            } else {
                high = mid - 1
            }
        }

        let line = low  // 0-indexed line number
        let column = clampedOffset - lineStartOffsets[line]  // Column is offset from line start
        return (line, max(0, column))
    }

    /// Get the character offset for a line and column.
    /// Uses cached line index for O(1) lookup instead of O(n) line counting.
    /// Returns clamped values for invalid inputs.
    func offset(forLine line: Int, column: Int) -> Int {
        rebuildLineIndexIfNeeded()

        // Validate line: clamp negative values and beyond-end values
        let clampedLine = max(0, line)
        guard clampedLine < lineStartOffsets.count else {
            // Line beyond end of document - return end of content
            return content.count
        }

        let lineStart = lineStartOffsets[clampedLine]

        // Validate column: clamp negative values
        let clampedColumn = max(0, column)

        // Calculate line length to clamp column
        let lineEnd: Int
        if clampedLine + 1 < lineStartOffsets.count {
            lineEnd = lineStartOffsets[clampedLine + 1] - 1  // -1 to exclude newline
        } else {
            lineEnd = content.count
        }

        let lineLength = max(0, lineEnd - lineStart)
        return lineStart + min(clampedColumn, lineLength)
    }

    // MARK: - Go To Definition

    /// Navigate to the definition of the symbol at the given character offset
    /// Returns true if a definition was found and navigated to
    @MainActor
    func goToDefinition(at characterOffset: Int) -> Bool {
        let (line, column) = lineAndColumn(for: characterOffset)
        let position = TLAPosition(line: UInt32(line), column: UInt32(column))

        // Get the word at the cursor position
        guard let word = TLACoreWrapper.shared.wordAt(position: position, in: content) else {
            return false
        }

        // Find the definition
        guard let definitionRange = TLACoreWrapper.shared.findDefinition(named: word, in: symbols) else {
            return false
        }

        // Navigate to the definition
        let targetOffset = offset(forLine: Int(definitionRange.start.line), column: Int(definitionRange.start.column))
        selectedRange = NSRange(location: targetOffset, length: 0)

        // Notify delegate to scroll to the position
        delegate?.documentDidNavigate(self, to: definitionRange)

        return true
    }

    /// Get the symbol at a given character offset, if any
    func symbolAt(characterOffset: Int) -> TLASymbol? {
        let (line, column) = lineAndColumn(for: characterOffset)
        let position = TLAPosition(line: UInt32(line), column: UInt32(column))

        guard let word = TLACoreWrapper.shared.wordAt(position: position, in: content) else {
            return nil
        }

        // Find the symbol
        func findSymbol(named name: String, in symbols: [TLASymbol]) -> TLASymbol? {
            for symbol in symbols {
                if symbol.name == name {
                    return symbol
                }
                if let found = findSymbol(named: name, in: symbol.children) {
                    return found
                }
            }
            return nil
        }

        return findSymbol(named: word, in: symbols)
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

extension Notification.Name {
    static let documentWillClose = Notification.Name("TLADocumentWillClose")
}
