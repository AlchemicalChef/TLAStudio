import AppKit

/// A small floating panel showing signature help for operator calls
@MainActor
class SignatureHelpPanel: NSPanel {

    // MARK: - Properties

    private let signatureLabel: NSTextField
    private let documentationLabel: NSTextField
    private let stackView: NSStackView

    private var signatureHelp: TLASignatureHelp?

    // MARK: - Initialization

    init() {
        // Create signature label
        signatureLabel = NSTextField(labelWithString: "")
        signatureLabel.font = .monospacedSystemFont(ofSize: 12, weight: .regular)
        signatureLabel.textColor = .labelColor
        signatureLabel.lineBreakMode = .byTruncatingTail
        signatureLabel.allowsDefaultTighteningForTruncation = true

        // Create documentation label
        documentationLabel = NSTextField(labelWithString: "")
        documentationLabel.font = .systemFont(ofSize: 11)
        documentationLabel.textColor = .secondaryLabelColor
        documentationLabel.lineBreakMode = .byWordWrapping
        documentationLabel.maximumNumberOfLines = 3
        documentationLabel.preferredMaxLayoutWidth = 350

        // Create stack view
        stackView = NSStackView(views: [signatureLabel, documentationLabel])
        stackView.orientation = .vertical
        stackView.alignment = .leading
        stackView.spacing = 4
        stackView.edgeInsets = NSEdgeInsets(top: 6, left: 8, bottom: 6, right: 8)

        // Calculate initial size
        let initialSize = NSSize(width: 300, height: 50)
        let contentRect = NSRect(origin: .zero, size: initialSize)

        super.init(
            contentRect: contentRect,
            styleMask: [.borderless, .nonactivatingPanel],
            backing: .buffered,
            defer: true
        )

        // Configure panel
        self.level = .popUpMenu
        self.hasShadow = true
        self.isOpaque = false
        self.backgroundColor = .clear

        // Create visual effect background
        let visualEffect = NSVisualEffectView(frame: contentRect)
        visualEffect.material = .popover
        visualEffect.blendingMode = .behindWindow
        visualEffect.state = .active
        visualEffect.wantsLayer = true
        visualEffect.layer?.cornerRadius = 4
        visualEffect.layer?.masksToBounds = true

        // Add stack view
        stackView.translatesAutoresizingMaskIntoConstraints = false
        visualEffect.addSubview(stackView)

        NSLayoutConstraint.activate([
            stackView.topAnchor.constraint(equalTo: visualEffect.topAnchor),
            stackView.leadingAnchor.constraint(equalTo: visualEffect.leadingAnchor),
            stackView.trailingAnchor.constraint(equalTo: visualEffect.trailingAnchor),
            stackView.bottomAnchor.constraint(equalTo: visualEffect.bottomAnchor)
        ])

        self.contentView = visualEffect
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    // MARK: - Public Methods

    /// Show signature help at the given screen position
    func show(at screenPoint: NSPoint, with help: TLASignatureHelp) {
        self.signatureHelp = help

        guard !help.signatures.isEmpty else {
            dismiss()
            return
        }

        // Bounds check for activeSignature
        let signatureIndex = min(Int(help.activeSignature), help.signatures.count - 1)
        guard signatureIndex >= 0 else {
            dismiss()
            return
        }

        let signature = help.signatures[signatureIndex]
        updateDisplay(signature: signature, activeParameter: Int(help.activeParameter))

        // Resize to fit content
        let signatureSize = signatureLabel.intrinsicContentSize
        let docSize = documentationLabel.intrinsicContentSize
        let width = max(signatureSize.width, docSize.width) + 16
        let height = signatureSize.height + docSize.height + 16

        var frame = NSRect(
            x: screenPoint.x,
            y: screenPoint.y + 4,
            width: min(max(width, 200), 450),
            height: min(max(height, 40), 100)
        )

        // Ensure on screen (use screen containing the point, not just main)
        let targetScreen = NSScreen.screens.first { $0.frame.contains(screenPoint) } ?? NSScreen.main
        if let screen = targetScreen {
            let screenFrame = screen.visibleFrame
            if frame.maxX > screenFrame.maxX {
                frame.origin.x = screenFrame.maxX - frame.width
            }
            if frame.maxY > screenFrame.maxY {
                frame.origin.y = screenPoint.y - frame.height - 4
            }
        }

        setFrame(frame, display: true)
        orderFront(nil)
    }

    /// Update the active parameter
    func updateActiveParameter(_ index: Int) {
        guard let help = signatureHelp, !help.signatures.isEmpty else { return }
        // Bounds check for activeSignature
        let signatureIndex = min(Int(help.activeSignature), help.signatures.count - 1)
        guard signatureIndex >= 0 else { return }
        let signature = help.signatures[signatureIndex]
        updateDisplay(signature: signature, activeParameter: index)
    }

    /// Dismiss the panel
    func dismiss() {
        orderOut(nil)
        signatureHelp = nil
    }

    // MARK: - Private Methods

    private func updateDisplay(signature: TLASignatureInfo, activeParameter: Int) {
        // Build attributed string with active parameter highlighted
        let attributedSignature = NSMutableAttributedString(
            string: signature.label,
            attributes: [
                .font: NSFont.monospacedSystemFont(ofSize: 12, weight: .regular),
                .foregroundColor: NSColor.labelColor
            ]
        )

        // Highlight the active parameter
        if activeParameter < signature.parameters.count {
            let param = signature.parameters[activeParameter]
            let paramLabel = param.label

            // Find and highlight the parameter in the signature
            if let range = signature.label.range(of: paramLabel) {
                let nsRange = NSRange(range, in: signature.label)
                attributedSignature.addAttributes([
                    .font: NSFont.monospacedSystemFont(ofSize: 12, weight: .bold),
                    .foregroundColor: NSColor.systemBlue
                ], range: nsRange)
            }
        }

        signatureLabel.attributedStringValue = attributedSignature

        // Set documentation
        if let doc = signature.documentation {
            documentationLabel.stringValue = doc
            documentationLabel.isHidden = false
        } else {
            documentationLabel.isHidden = true
        }
    }
}

/// Controller for signature help
@MainActor
class SignatureHelpController {

    // MARK: - Properties

    private var panel: SignatureHelpPanel?
    private weak var textView: NSTextView?

    /// Callback to get signature help
    var signatureHelpProvider: ((Int) async -> TLASignatureHelp?)?

    /// Current signature help task (for cancellation)
    private var signatureHelpTask: Task<Void, Never>?

    /// Generation counter for tracking requests (prevents race conditions)
    private var requestGeneration: UInt64 = 0

    /// Whether signature help is currently showing
    var isActive: Bool {
        panel?.isVisible ?? false
    }

    // MARK: - Initialization

    init(textView: NSTextView) {
        self.textView = textView
    }

    deinit {
        signatureHelpTask?.cancel()
    }

    // MARK: - Public Methods

    /// Called when '(' is typed - may trigger signature help
    func handleOpenParen() {
        // Cancel any pending request
        signatureHelpTask?.cancel()
        signatureHelpTask = Task {
            await triggerSignatureHelp()
        }
    }

    /// Called when ',' is typed - update active parameter
    func handleComma() {
        guard isActive else { return }
        // Cancel any pending request
        signatureHelpTask?.cancel()
        signatureHelpTask = Task {
            await triggerSignatureHelp()
        }
    }

    /// Called when ')' is typed - dismiss
    func handleCloseParen() {
        dismiss()
    }

    /// Manually trigger signature help
    func triggerSignatureHelp() async {
        guard let textView = textView,
              let provider = signatureHelpProvider else { return }

        // Increment generation to track this request
        requestGeneration &+= 1
        let capturedGeneration = requestGeneration

        let cursorPosition = textView.selectedRange().location
        guard let help = await provider(cursorPosition) else {
            dismiss()
            return
        }

        // Only show if this is still the current request
        guard requestGeneration == capturedGeneration else { return }

        showPanel(with: help)
    }

    /// Dismiss signature help
    func dismiss() {
        panel?.dismiss()
    }

    // MARK: - Private Methods

    private func showPanel(with help: TLASignatureHelp) {
        guard let textView = textView, let window = textView.window else { return }

        // Create panel if needed
        if panel == nil {
            panel = SignatureHelpPanel()
        }

        // Calculate position above cursor
        guard let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else { return }

        let cursorLocation = textView.selectedRange().location
        let glyphRange = layoutManager.glyphRange(
            forCharacterRange: NSRange(location: cursorLocation, length: 0),
            actualCharacterRange: nil
        )
        var cursorRect = layoutManager.boundingRect(forGlyphRange: glyphRange, in: textContainer)
        cursorRect.origin.x += textView.textContainerOrigin.x
        cursorRect.origin.y += textView.textContainerOrigin.y

        // Convert to screen coordinates - show above the cursor
        let viewPoint = NSPoint(x: cursorRect.minX, y: cursorRect.minY)
        let windowPoint = textView.convert(viewPoint, to: nil)
        let screenPoint = window.convertPoint(toScreen: windowPoint)

        panel?.show(at: screenPoint, with: help)
    }
}
