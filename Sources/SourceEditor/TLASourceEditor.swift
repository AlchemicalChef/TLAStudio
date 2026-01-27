import AppKit
import CoreText

// MARK: - TLASourceEditor

/// High-performance text editor for TLA+ specifications.
/// Based on NSTextView for reliable text input handling.
public final class TLASourceEditor: NSTextView {

    // MARK: - Configuration

    public struct Configuration {
        public var font: NSFont = .monospacedSystemFont(ofSize: 13, weight: .regular)
        public var theme: SyntaxTheme = .default
        public var showLineNumbers: Bool = true
        public var tabWidth: Int = 4
        public var showInvisibles: Bool = false
        public var lineHeight: CGFloat = 1.4
        public var insertionPointWidth: CGFloat = 2.0

        public init() {}
    }

    public var configuration = Configuration() {
        didSet {
            applyConfiguration()
        }
    }

    /// Delegate for editor events
    public weak var editorDelegate: TLASourceEditorDelegate?

    // MARK: - Line Numbers

    private var lineNumberView: LineNumberRulerView?

    // MARK: - Syntax Highlighting

    private var highlighter: TLASyntaxHighlighter?
    private var isHighlighting = false

    // MARK: - Initialization

    public override init(frame frameRect: NSRect, textContainer container: NSTextContainer?) {
        super.init(frame: frameRect, textContainer: container)
        setup()
    }

    public required init?(coder: NSCoder) {
        super.init(coder: coder)
        setup()
    }

    /// Convenience initializer
    public convenience init() {
        // Create text storage, layout manager, and container
        let textStorage = NSTextStorage()
        let layoutManager = NSLayoutManager()
        textStorage.addLayoutManager(layoutManager)

        let textContainer = NSTextContainer(containerSize: NSSize(width: 1e7, height: 1e7))
        textContainer.widthTracksTextView = true
        textContainer.heightTracksTextView = false
        layoutManager.addTextContainer(textContainer)

        self.init(frame: .zero, textContainer: textContainer)
    }

    private func setup() {
        // Basic configuration
        isEditable = true
        isSelectable = true
        isRichText = false
        importsGraphics = false
        allowsUndo = true
        isAutomaticQuoteSubstitutionEnabled = false
        isAutomaticDashSubstitutionEnabled = false
        isAutomaticTextReplacementEnabled = false
        isAutomaticSpellingCorrectionEnabled = false
        isContinuousSpellCheckingEnabled = false

        // Appearance
        backgroundColor = .textBackgroundColor
        insertionPointColor = .textColor
        drawsBackground = true

        // Text container
        textContainer?.lineFragmentPadding = 5
        textContainerInset = NSSize(width: 0, height: 4)

        // Apply initial configuration
        applyConfiguration()

        // Set up highlighter
        highlighter = TLASyntaxHighlighter(editor: self)

        // Listen for text changes
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChangeNotification(_:)),
            name: NSText.didChangeNotification,
            object: self
        )
    }

    deinit {
        NotificationCenter.default.removeObserver(self)
    }

    public override func viewDidMoveToWindow() {
        super.viewDidMoveToWindow()
        // Automatically become first responder when added to a window
        if let window = window {
            DispatchQueue.main.async { [weak self] in
                window.makeFirstResponder(self)
            }
        }
    }

    public override var acceptsFirstResponder: Bool {
        return true
    }

    public override func mouseDown(with event: NSEvent) {
        // Ensure we become first responder when clicked
        window?.makeFirstResponder(self)
        super.mouseDown(with: event)
    }

    private func applyConfiguration() {
        font = configuration.font

        // Set up paragraph style for line height
        let paragraphStyle = NSMutableParagraphStyle()
        paragraphStyle.lineHeightMultiple = configuration.lineHeight
        defaultParagraphStyle = paragraphStyle

        // Apply to existing text
        if let textStorage = textStorage, textStorage.length > 0 {
            textStorage.addAttribute(.paragraphStyle, value: paragraphStyle,
                                    range: NSRange(location: 0, length: textStorage.length))
        }
    }

    // MARK: - Public API

    /// Get/set text content
    public var text: String {
        get { string }
        set {
            if string != newValue {
                string = newValue
                scheduleHighlighting()
            }
        }
    }

    /// Get/set selection
    public var selection: NSRange {
        get { selectedRange() }
        set { setSelectedRange(newValue) }
    }

    /// Apply syntax highlighting
    public func setHighlights(_ highlights: [HighlightRange]) {
        // Ensure main thread access for thread safety
        assert(Thread.isMainThread, "setHighlights must be called on main thread")
        guard let textStorage = textStorage else { return }

        isHighlighting = true

        // Reset foreground color only - DO NOT touch fonts
        let fullRange = NSRange(location: 0, length: textStorage.length)
        textStorage.addAttribute(.foregroundColor, value: NSColor.textColor, range: fullRange)

        // Apply highlight colors only - no font changes
        for highlight in highlights {
            guard highlight.range.location >= 0,
                  highlight.range.location + highlight.range.length <= textStorage.length else {
                continue
            }

            textStorage.addAttribute(.foregroundColor, value: highlight.color, range: highlight.range)
        }

        isHighlighting = false
    }

    // MARK: - Text Changes

    @objc private func textDidChangeNotification(_ notification: Notification) {
        guard !isHighlighting else { return }

        // Always reset typing attributes to regular font to prevent style inheritance
        typingAttributes = [
            .font: configuration.font,
            .foregroundColor: NSColor.textColor
        ]

        // Clear bracket highlights before text changes affect positions
        clearBracketHighlights()

        editorDelegate?.editorTextDidChange(self)
        scheduleHighlighting()
    }

    private func scheduleHighlighting() {
        highlighter?.scheduleHighlighting()
    }

    // MARK: - Tab Handling

    public override func insertTab(_ sender: Any?) {
        // Insert spaces instead of tab
        let spaces = String(repeating: " ", count: configuration.tabWidth)
        insertText(spaces, replacementRange: selectedRange())
    }

    public override func insertBacktab(_ sender: Any?) {
        // Outdent: remove leading spaces from current line
        guard let textStorage = textStorage else { return }

        let cursorPos = selectedRange().location
        let text = textStorage.string as NSString

        // Find line start
        var lineStart = cursorPos
        while lineStart > 0 && text.character(at: lineStart - 1) != 0x0A {
            lineStart -= 1
        }

        // Count leading spaces
        var spacesToRemove = 0
        for i in 0..<min(configuration.tabWidth, text.length - lineStart) {
            if text.character(at: lineStart + i) == 0x20 { // space
                spacesToRemove += 1
            } else {
                break
            }
        }

        if spacesToRemove > 0 {
            let removeRange = NSRange(location: lineStart, length: spacesToRemove)
            if shouldChangeText(in: removeRange, replacementString: "") {
                textStorage.replaceCharacters(in: removeRange, with: "")
                didChangeText()

                // Adjust cursor
                let newPos = max(lineStart, cursorPos - spacesToRemove)
                setSelectedRange(NSRange(location: newPos, length: 0))
            }
        }
    }

    // MARK: - Selection Changes

    public override func setSelectedRange(_ charRange: NSRange, affinity: NSSelectionAffinity, stillSelecting stillSelectingFlag: Bool) {
        super.setSelectedRange(charRange, affinity: affinity, stillSelecting: stillSelectingFlag)
        if !stillSelectingFlag {
            editorDelegate?.editorSelectionDidChange(self)
            // Update bracket matching
            highlightMatchingBrackets()
        }
    }

    // MARK: - Scroll View Setup

    /// Configure enclosing scroll view with line numbers
    public func configureScrollView(_ scrollView: NSScrollView) {
        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = true
        scrollView.autohidesScrollers = true

        // Set up line number ruler
        if configuration.showLineNumbers {
            let rulerView = LineNumberRulerView(textView: self)
            scrollView.verticalRulerView = rulerView
            scrollView.hasVerticalRuler = true
            scrollView.rulersVisible = true
            lineNumberView = rulerView
        }

        // Configure for text editing
        scrollView.drawsBackground = true
        scrollView.backgroundColor = .textBackgroundColor

        // Text view sizing - use large initial width, will resize with scroll view
        let contentWidth = max(scrollView.contentSize.width, 800)
        minSize = NSSize(width: 0, height: 0)
        maxSize = NSSize(width: CGFloat.greatestFiniteMagnitude, height: CGFloat.greatestFiniteMagnitude)
        isVerticallyResizable = true
        isHorizontallyResizable = false
        autoresizingMask = [.width]

        // Text container must have non-zero width to display text
        textContainer?.containerSize = NSSize(width: contentWidth, height: CGFloat.greatestFiniteMagnitude)
        textContainer?.widthTracksTextView = true

        // Set frame to match scroll view content area
        frame = NSRect(x: 0, y: 0, width: contentWidth, height: 0)
    }
}

// MARK: - Delegate Protocol

public protocol TLASourceEditorDelegate: AnyObject {
    func editorTextDidChange(_ editor: TLASourceEditor)
    func editorSelectionDidChange(_ editor: TLASourceEditor)
}

public extension TLASourceEditorDelegate {
    func editorSelectionDidChange(_ editor: TLASourceEditor) {}
}

// MARK: - Line Number Ruler View

public class LineNumberRulerView: NSRulerView {

    private weak var textView: NSTextView?

    // Cache line offsets for efficient line number calculation
    private var cachedLineOffsets: [Int]?
    private var cachedText: String = ""

    public init(textView: NSTextView) {
        self.textView = textView
        super.init(scrollView: textView.enclosingScrollView, orientation: .verticalRuler)

        ruleThickness = 40
        clientView = textView

        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )

        NotificationCenter.default.addObserver(
            self,
            selector: #selector(boundsDidChange(_:)),
            name: NSView.boundsDidChangeNotification,
            object: textView.enclosingScrollView?.contentView
        )
    }

    public init(textView: NSTextView, scrollView: NSScrollView) {
        self.textView = textView
        super.init(scrollView: scrollView, orientation: .verticalRuler)

        ruleThickness = 40
        clientView = textView

        NotificationCenter.default.addObserver(
            self,
            selector: #selector(textDidChange(_:)),
            name: NSText.didChangeNotification,
            object: textView
        )

        NotificationCenter.default.addObserver(
            self,
            selector: #selector(boundsDidChange(_:)),
            name: NSView.boundsDidChangeNotification,
            object: scrollView.contentView
        )
    }

    required init(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    deinit {
        NotificationCenter.default.removeObserver(self)
    }

    @objc private func textDidChange(_ notification: Notification) {
        // Invalidate line offset cache when text changes
        cachedLineOffsets = nil
        needsDisplay = true
    }

    @objc private func boundsDidChange(_ notification: Notification) {
        needsDisplay = true
    }

    /// Get cached line offsets, computing if needed
    private func getLineOffsets(for text: String) -> [Int] {
        if let cached = cachedLineOffsets, text == cachedText {
            return cached
        }

        // Compute line offsets
        var offsets: [Int] = [0]
        var index = text.startIndex
        while let newlineRange = text.range(of: "\n", range: index..<text.endIndex) {
            offsets.append(text.distance(from: text.startIndex, to: newlineRange.upperBound))
            index = newlineRange.upperBound
        }

        cachedLineOffsets = offsets
        cachedText = text
        return offsets
    }

    /// Binary search to find line number for character offset
    private func lineNumber(for characterOffset: Int, in lineOffsets: [Int]) -> Int {
        var low = 0
        var high = lineOffsets.count - 1

        while low < high {
            let mid = (low + high + 1) / 2
            if lineOffsets[mid] <= characterOffset {
                low = mid
            } else {
                high = mid - 1
            }
        }

        return low
    }

    public override func drawHashMarksAndLabels(in rect: NSRect) {
        guard let textView = textView,
              let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else {
            return
        }

        // Background
        NSColor.controlBackgroundColor.setFill()
        rect.fill()

        // Separator line
        NSColor.separatorColor.setStroke()
        let separatorPath = NSBezierPath()
        separatorPath.move(to: NSPoint(x: bounds.maxX - 0.5, y: rect.minY))
        separatorPath.line(to: NSPoint(x: bounds.maxX - 0.5, y: rect.maxY))
        separatorPath.stroke()

        // Line numbers
        let text = textView.string as NSString
        let visibleRect = textView.visibleRect
        let glyphRange = layoutManager.glyphRange(forBoundingRect: visibleRect, in: textContainer)
        let charRange = layoutManager.characterRange(forGlyphRange: glyphRange, actualGlyphRange: nil)

        let font = NSFont.monospacedDigitSystemFont(ofSize: 11, weight: .regular)
        let attrs: [NSAttributedString.Key: Any] = [
            .font: font,
            .foregroundColor: NSColor.secondaryLabelColor
        ]

        // Use binary search on cached line offsets for O(log n) line counting
        let lineOffsets = getLineOffsets(for: textView.string)
        var lineNumber = lineNumber(for: charRange.location, in: lineOffsets) + 1

        // Draw visible line numbers
        text.enumerateSubstrings(in: charRange, options: [.byLines, .substringNotRequired]) { [weak self] _, substringRange, _, _ in
            guard let self = self else { return }

            let lineRect = layoutManager.lineFragmentRect(forGlyphAt: layoutManager.glyphIndexForCharacter(at: substringRange.location), effectiveRange: nil)

            let lineNumberString = "\(lineNumber)"
            let attrString = NSAttributedString(string: lineNumberString, attributes: attrs)
            let stringSize = attrString.size()

            let y = lineRect.minY + textView.textContainerInset.height - visibleRect.minY + (lineRect.height - stringSize.height) / 2
            let x = self.ruleThickness - stringSize.width - 8

            attrString.draw(at: NSPoint(x: x, y: y))

            lineNumber += 1
        }
    }
}

// MARK: - Syntax Theme

public struct SyntaxTheme {
    public var keyword: NSColor
    public var operator_: NSColor
    public var string: NSColor
    public var comment: NSColor
    public var number: NSColor
    public var identifier: NSColor
    public var type: NSColor
    public var background: NSColor
    public var selection: NSColor
    public var cursor: NSColor
    public var currentLine: NSColor

    /// Default theme that adapts to system appearance
    public static let `default` = SyntaxTheme(
        keyword: .systemBlue,
        operator_: .systemPurple,
        string: .systemRed,
        comment: .systemGreen,
        number: .systemOrange,
        identifier: .textColor,
        type: .systemTeal,
        background: .textBackgroundColor,
        selection: .selectedTextBackgroundColor,
        cursor: .textColor,
        currentLine: NSColor(calibratedWhite: 0.5, alpha: 0.1)
    )

    /// Light theme
    public static let light = SyntaxTheme(
        keyword: NSColor(red: 0.61, green: 0.15, blue: 0.69, alpha: 1.0),
        operator_: NSColor(red: 0.8, green: 0.4, blue: 0.0, alpha: 1.0),
        string: NSColor(red: 0.77, green: 0.1, blue: 0.09, alpha: 1.0),
        comment: NSColor(white: 0.5, alpha: 1.0),
        number: NSColor(red: 0.11, green: 0.0, blue: 0.81, alpha: 1.0),
        identifier: NSColor(white: 0.1, alpha: 1.0),
        type: NSColor(red: 0.0, green: 0.5, blue: 0.5, alpha: 1.0),
        background: .white,
        selection: NSColor(red: 0.7, green: 0.85, blue: 1.0, alpha: 1.0),
        cursor: .black,
        currentLine: NSColor(calibratedWhite: 0.95, alpha: 1.0)
    )

    /// Dark theme
    public static let dark = SyntaxTheme(
        keyword: NSColor(red: 0.78, green: 0.56, blue: 0.89, alpha: 1.0),
        operator_: NSColor(red: 1.0, green: 0.6, blue: 0.2, alpha: 1.0),
        string: NSColor(red: 0.99, green: 0.42, blue: 0.42, alpha: 1.0),
        comment: NSColor(white: 0.55, alpha: 1.0),
        number: NSColor(red: 0.51, green: 0.68, blue: 0.99, alpha: 1.0),
        identifier: NSColor(white: 0.9, alpha: 1.0),
        type: NSColor(red: 0.4, green: 0.8, blue: 0.8, alpha: 1.0),
        background: NSColor(red: 0.12, green: 0.12, blue: 0.14, alpha: 1.0),
        selection: NSColor(red: 0.25, green: 0.35, blue: 0.5, alpha: 1.0),
        cursor: .white,
        currentLine: NSColor(calibratedWhite: 0.18, alpha: 1.0)
    )

    /// Monokai theme
    public static let monokai = SyntaxTheme(
        keyword: NSColor(red: 0.98, green: 0.15, blue: 0.45, alpha: 1.0),
        operator_: NSColor(red: 0.98, green: 0.15, blue: 0.45, alpha: 1.0),
        string: NSColor(red: 0.9, green: 0.86, blue: 0.45, alpha: 1.0),
        comment: NSColor(red: 0.46, green: 0.44, blue: 0.37, alpha: 1.0),
        number: NSColor(red: 0.68, green: 0.51, blue: 1.0, alpha: 1.0),
        identifier: NSColor(red: 0.97, green: 0.97, blue: 0.95, alpha: 1.0),
        type: NSColor(red: 0.4, green: 0.85, blue: 0.94, alpha: 1.0),
        background: NSColor(red: 0.15, green: 0.16, blue: 0.13, alpha: 1.0),
        selection: NSColor(red: 0.28, green: 0.29, blue: 0.26, alpha: 1.0),
        cursor: .white,
        currentLine: NSColor(red: 0.2, green: 0.21, blue: 0.18, alpha: 1.0)
    )

    /// Solarized Light theme
    public static let solarizedLight = SyntaxTheme(
        keyword: NSColor(red: 0.52, green: 0.6, blue: 0.0, alpha: 1.0),
        operator_: NSColor(red: 0.8, green: 0.29, blue: 0.09, alpha: 1.0),
        string: NSColor(red: 0.16, green: 0.63, blue: 0.6, alpha: 1.0),
        comment: NSColor(red: 0.58, green: 0.63, blue: 0.63, alpha: 1.0),
        number: NSColor(red: 0.16, green: 0.63, blue: 0.6, alpha: 1.0),
        identifier: NSColor(red: 0.4, green: 0.48, blue: 0.51, alpha: 1.0),
        type: NSColor(red: 0.15, green: 0.55, blue: 0.82, alpha: 1.0),
        background: NSColor(red: 0.99, green: 0.96, blue: 0.89, alpha: 1.0),
        selection: NSColor(red: 0.93, green: 0.91, blue: 0.84, alpha: 1.0),
        cursor: NSColor(red: 0.4, green: 0.48, blue: 0.51, alpha: 1.0),
        currentLine: NSColor(red: 0.93, green: 0.91, blue: 0.84, alpha: 1.0)
    )

    /// Solarized Dark theme
    public static let solarizedDark = SyntaxTheme(
        keyword: NSColor(red: 0.52, green: 0.6, blue: 0.0, alpha: 1.0),
        operator_: NSColor(red: 0.8, green: 0.29, blue: 0.09, alpha: 1.0),
        string: NSColor(red: 0.16, green: 0.63, blue: 0.6, alpha: 1.0),
        comment: NSColor(red: 0.4, green: 0.48, blue: 0.51, alpha: 1.0),
        number: NSColor(red: 0.16, green: 0.63, blue: 0.6, alpha: 1.0),
        identifier: NSColor(red: 0.51, green: 0.58, blue: 0.59, alpha: 1.0),
        type: NSColor(red: 0.15, green: 0.55, blue: 0.82, alpha: 1.0),
        background: NSColor(red: 0.0, green: 0.17, blue: 0.21, alpha: 1.0),
        selection: NSColor(red: 0.03, green: 0.21, blue: 0.26, alpha: 1.0),
        cursor: NSColor(red: 0.51, green: 0.58, blue: 0.59, alpha: 1.0),
        currentLine: NSColor(red: 0.03, green: 0.21, blue: 0.26, alpha: 1.0)
    )

    public init(
        keyword: NSColor,
        operator_: NSColor,
        string: NSColor,
        comment: NSColor,
        number: NSColor,
        identifier: NSColor,
        type: NSColor,
        background: NSColor = .textBackgroundColor,
        selection: NSColor = .selectedTextBackgroundColor,
        cursor: NSColor = .textColor,
        currentLine: NSColor = NSColor(calibratedWhite: 0.5, alpha: 0.1)
    ) {
        self.keyword = keyword
        self.operator_ = operator_
        self.string = string
        self.comment = comment
        self.number = number
        self.identifier = identifier
        self.type = type
        self.background = background
        self.selection = selection
        self.cursor = cursor
        self.currentLine = currentLine
    }

    /// Get a theme by name
    public static func named(_ name: String) -> SyntaxTheme {
        switch name.lowercased() {
        case "light": return .light
        case "dark": return .dark
        case "monokai": return .monokai
        case "solarized light": return .solarizedLight
        case "solarized dark": return .solarizedDark
        default: return .default
        }
    }
}

// MARK: - Highlight Range

public struct HighlightRange {
    public let range: NSRange
    public let color: NSColor
    public let style: Style

    public enum Style {
        case plain
        case bold
        case italic
    }

    public init(range: NSRange, color: NSColor, style: Style = .plain) {
        self.range = range
        self.color = color
        self.style = style
    }
}

// MARK: - Gutter View (Legacy compatibility)

public class GutterView: NSView {
    public var lineCount: Int = 0
    public var annotations: [Int: GutterAnnotation] = [:]

    public struct GutterAnnotation {
        public enum Kind { case error, warning, proofStatus }
        public let kind: Kind
        public let icon: NSImage
        public let tooltip: String
    }

    public override func draw(_ dirtyRect: NSRect) {
        // Drawing handled by LineNumberRulerView
    }
}
