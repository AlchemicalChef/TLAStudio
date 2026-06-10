import AppKit
import Combine

/// App-wide command-enablement state for SwiftUI menu items.
///
/// SwiftUI `Commands` can't reach the key window's document directly, so
/// menu items historically stayed enabled and silently no-opped (platform
/// review: "zero menu validation"). This singleton tracks the current
/// document (re-binding on key-window changes) and republishes the session
/// flags the menus need for `.disabled(...)`.
@MainActor
final class AppCommandState: ObservableObject {

    static let shared = AppCommandState()

    @Published private(set) var isTLCRunning = false
    @Published private(set) var isProofRunning = false
    @Published private(set) var hasFailedProofs = false

    private weak var observedDocument: TLADocument?
    private var windowObserver: NSObjectProtocol?
    private var documentCancellables = Set<AnyCancellable>()

    private init() {
        windowObserver = NotificationCenter.default.addObserver(
            forName: NSWindow.didBecomeKeyNotification,
            object: nil,
            queue: .main
        ) { [weak self] _ in
            Task { @MainActor [weak self] in
                self?.rebindToCurrentDocument()
            }
        }
        rebindToCurrentDocument()
    }

    private func rebindToCurrentDocument() {
        let document = NSDocumentController.shared.currentDocument as? TLADocument
        guard document !== observedDocument else { return }
        observedDocument = document
        documentCancellables.removeAll()

        guard let document else {
            bindTLCSession(nil)
            bindProofSession(nil)
            return
        }

        // @Published sinks fire on willSet — use the closure argument, not
        // the (still-old) property.
        document.$tlcSession
            .sink { [weak self] session in self?.bindTLCSession(session) }
            .store(in: &documentCancellables)
        document.$proofSession
            .sink { [weak self] session in self?.bindProofSession(session) }
            .store(in: &documentCancellables)
    }

    private func bindTLCSession(_ session: TLCSession?) {
        tlcCancellable = nil
        guard let session else {
            isTLCRunning = false
            return
        }
        isTLCRunning = session.isRunning
        tlcCancellable = session.$isRunning
            .sink { [weak self] running in self?.isTLCRunning = running }
    }

    private func bindProofSession(_ session: ProofSession?) {
        proofRunningCancellable = nil
        proofObligationsCancellable = nil
        guard let session else {
            isProofRunning = false
            hasFailedProofs = false
            return
        }
        isProofRunning = session.isRunning
        hasFailedProofs = !session.failedObligations.isEmpty
        proofRunningCancellable = session.$isRunning
            .sink { [weak self] running in self?.isProofRunning = running }
        proofObligationsCancellable = session.$obligations
            .sink { [weak self] obligations in
                self?.hasFailedProofs = obligations.contains {
                    $0.status == .failed || $0.status == .timeout
                }
            }
    }

    private var tlcCancellable: AnyCancellable?
    private var proofRunningCancellable: AnyCancellable?
    private var proofObligationsCancellable: AnyCancellable?
}
