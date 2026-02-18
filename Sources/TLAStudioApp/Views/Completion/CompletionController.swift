import AppKit
import Combine

/// Controller that manages the completion popup lifecycle and keyboard interaction
@MainActor
class CompletionController {

    // MARK: - Properties

    /// The completion popup window
    private var popupWindow: CompletionPopupWindow?

    /// The text view being completed
    private weak var textView: NSTextView?

    /// Callback to get completions for the current position
    var completionProvider: ((Int) async -> [TLADetailedCompletionItem])?

    /// Callback when completion is inserted
    var onInsertCompletion: ((TLADetailedCompletionItem, NSRange) -> Void)?

    /// Debounce timer for auto-trigger
    private var debounceTimer: Timer?

    /// Current completion task (for cancellation)
    private var completionTask: Task<Void, Never>?

    /// Debounce interval in seconds
    private let debounceInterval: TimeInterval = 0.1

    /// Minimum characters to trigger completion
    private let minTriggerLength = 1

    /// Whether completion is currently active
    var isActive: Bool {
        popupWindow?.isVisible ?? false
    }

    /// Characters that trigger completion
    private let triggerCharacters: Set<Character> = Set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_\\")

    /// The range of the current completion prefix
    private var completionRange: NSRange = NSRange(location: NSNotFound, length: 0)

    /// Generation counter for tracking completion requests (prevents race conditions)
    private var completionGeneration: UInt64 = 0

    /// Maximum cursor distance from completion range before dismissing
    private let maxCursorTolerance = 20

    // MARK: - Initialization

    init(textView: NSTextView) {
        self.textView = textView
    }

    deinit {
        debounceTimer?.invalidate()
        completionTask?.cancel()
    }

    // MARK: - Public Methods

    /// Called when a character is typed - may trigger completion
    func handleCharacterTyped(_ character: Character) {
        // Cancel any pending trigger
        debounceTimer?.invalidate()

        if triggerCharacters.contains(character) {
            // Schedule completion trigger after debounce
            debounceTimer = Timer.scheduledTimer(withTimeInterval: debounceInterval, repeats: false) { [weak self] _ in
                Task { @MainActor in
                    self?.triggerCompletion()
                }
            }
        } else if isActive {
            // Update filter if popup is showing
            updateFilter()
        }
    }

    /// Called when backspace is pressed
    func handleBackspace() {
        if isActive {
            // Update filter or dismiss if prefix is empty
            updateFilter()
        }
    }

    /// Called when escape is pressed - returns true if completion was dismissed
    func handleEscape() -> Bool {
        if isActive {
            dismiss()
            return true
        }
        return false
    }

    /// Called when enter/return is pressed - returns true if completion was confirmed
    func handleReturn() -> Bool {
        if isActive, let item = popupWindow?.selectedItem {
            insertCompletion(item)
            return true
        }
        return false
    }

    /// Called when tab is pressed - returns true if completion was confirmed
    func handleTab() -> Bool {
        return handleReturn()
    }

    /// Called when up arrow is pressed - returns true if handled
    func handleUpArrow() -> Bool {
        if isActive {
            popupWindow?.selectPrevious()
            return true
        }
        return false
    }

    /// Called when down arrow is pressed - returns true if handled
    func handleDownArrow() -> Bool {
        if isActive {
            popupWindow?.selectNext()
            return true
        }
        return false
    }

    /// Manually trigger completion
    func triggerCompletion() {
        guard let textView = textView else { return }

        let cursorPosition = textView.selectedRange().location
        guard cursorPosition > 0 else { return }

        // Find the completion prefix
        let (prefix, range) = getCompletionPrefix(at: cursorPosition, in: textView)

        // Don't trigger for very short prefixes unless explicitly requested
        guard prefix.count >= minTriggerLength || prefix.starts(with: "\\") else {
            dismiss()
            return
        }

        completionRange = range

        // Cancel any pending completion task
        completionTask?.cancel()

        // Increment generation to track this specific request
        completionGeneration &+= 1
        let capturedGeneration = completionGeneration
        let capturedPrefix = prefix

        // Request completions
        completionTask = Task {
            guard !Task.isCancelled else { return }
            guard let provider = completionProvider else { return }

            let items = await provider(cursorPosition)

            guard !Task.isCancelled else { return }

            if items.isEmpty {
                dismiss()
                return
            }

            // Only show if this is still the current completion request
            if completionGeneration == capturedGeneration {
                showPopup(with: items, filterText: capturedPrefix)
            }
        }
    }

    /// Dismiss the completion popup
    func dismiss() {
        debounceTimer?.invalidate()
        completionTask?.cancel()
        popupWindow?.dismiss()
        // Clear closures to break any potential retain cycles
        popupWindow?.onSelect = nil
        popupWindow?.onDismiss = nil
        completionRange = NSRange(location: NSNotFound, length: 0)
    }

    /// Called when cursor moves - may dismiss completion
    func handleCursorMoved() {
        guard isActive, let textView = textView else { return }

        let cursorPosition = textView.selectedRange().location

        // Check if cursor moved outside completion range (with tolerance for typing ahead)
        if cursorPosition < completionRange.location ||
           cursorPosition > completionRange.location + completionRange.length + maxCursorTolerance {
            // Cursor moved too far, dismiss
            dismiss()
        } else {
            // Update filter
            updateFilter()
        }
    }

    // MARK: - Private Methods

    private func getCompletionPrefix(at position: Int, in textView: NSTextView) -> (String, NSRange) {
        let text = textView.string
        let nsString = text as NSString

        // Bounds check
        guard position > 0 && position <= nsString.length else {
            return ("", NSRange(location: position, length: 0))
        }

        var start = position

        // Move backwards to find start of identifier or TLA+ operator
        // NSRange uses UTF-16 code units, so we work with NSString
        while start > 0 {
            let charRange = NSRange(location: start - 1, length: 1)
            let charStr = nsString.substring(with: charRange)
            guard let char = charStr.first else { break }

            if char.isLetter || char.isNumber || char == "_" {
                start -= 1
            } else if char == "\\" && start > 1 {
                // Include backslash for TLA+ operators like \in, \cup, etc.
                start -= 1
                break
            } else {
                break
            }
        }

        let length = position - start
        let range = NSRange(location: start, length: length)

        if length > 0 {
            let prefix = nsString.substring(with: range)
            return (prefix, range)
        }

        return ("", NSRange(location: position, length: 0))
    }

    private func showPopup(with items: [TLADetailedCompletionItem], filterText: String) {
        guard let textView = textView, let window = textView.window else { return }

        // Create popup if needed
        if popupWindow == nil {
            popupWindow = CompletionPopupWindow()
            popupWindow?.onSelect = { [weak self] item in
                self?.insertCompletion(item)
            }
            popupWindow?.onDismiss = { [weak self] in
                self?.completionRange = NSRange(location: NSNotFound, length: 0)
            }
        }

        // Calculate position near cursor
        guard let layoutManager = textView.layoutManager,
              let textContainer = textView.textContainer else { return }

        let glyphRange = layoutManager.glyphRange(
            forCharacterRange: NSRange(location: completionRange.location, length: 0),
            actualCharacterRange: nil
        )
        var cursorRect = layoutManager.boundingRect(forGlyphRange: glyphRange, in: textContainer)
        cursorRect.origin.x += textView.textContainerOrigin.x
        cursorRect.origin.y += textView.textContainerOrigin.y

        // Convert to screen coordinates
        let viewPoint = NSPoint(x: cursorRect.minX, y: cursorRect.maxY + 2)
        let windowPoint = textView.convert(viewPoint, to: nil)
        let screenPoint = window.convertPoint(toScreen: windowPoint)

        // Show popup
        popupWindow?.show(at: screenPoint, with: items, filterText: filterText)
    }

    private func updateFilter() {
        guard isActive, let textView = textView else { return }

        let cursorPosition = textView.selectedRange().location
        let (prefix, _) = getCompletionPrefix(at: cursorPosition, in: textView)

        if prefix.isEmpty {
            dismiss()
        } else {
            popupWindow?.updateFilter(prefix)
        }
    }

    private func insertCompletion(_ item: TLADetailedCompletionItem) {
        guard let textView = textView else { return }

        // Determine what to insert
        var insertText = item.insertText ?? item.label

        // Process snippet markers: strip ${N:placeholder} patterns first, then find $0 cursor position
        var cursorOffset: Int? = nil

        // First: Strip ${N:placeholder} patterns -> replace with just the placeholder text
        while let openRange = insertText.range(of: "${") {
            // Find matching }
            guard let colonRange = insertText.range(of: ":", range: openRange.upperBound..<insertText.endIndex),
                  let closeRange = insertText.range(of: "}", range: colonRange.upperBound..<insertText.endIndex) else {
                break
            }
            let placeholder = String(insertText[colonRange.upperBound..<closeRange.lowerBound])
            insertText.replaceSubrange(openRange.lowerBound..<closeRange.upperBound, with: placeholder)
        }

        // Then: Handle $0 cursor marker (after placeholder stripping so offset is correct)
        if let markerRange = insertText.range(of: "$0") {
            cursorOffset = insertText.distance(from: insertText.startIndex, to: markerRange.lowerBound)
            insertText.removeSubrange(markerRange)
        }

        // Calculate the range to replace (the typed prefix)
        let cursorPosition = textView.selectedRange().location

        // Guard against invalid state (cursor moved before completion start)
        guard cursorPosition >= completionRange.location,
              completionRange.location != NSNotFound else {
            dismiss()
            return
        }

        let replaceRange = NSRange(
            location: completionRange.location,
            length: cursorPosition - completionRange.location
        )

        // Validate the range is within bounds
        let textLength = (textView.string as NSString).length
        guard replaceRange.location + replaceRange.length <= textLength else {
            dismiss()
            return
        }

        // Insert the completion
        if textView.shouldChangeText(in: replaceRange, replacementString: insertText) {
            textView.replaceCharacters(in: replaceRange, with: insertText)
            textView.didChangeText()

            // Position cursor at $0 marker location if present
            if let offset = cursorOffset {
                let newCursorPosition = replaceRange.location + offset
                textView.setSelectedRange(NSRange(location: newCursorPosition, length: 0))
            }

            // Notify callback
            onInsertCompletion?(item, replaceRange)
        }

        dismiss()
    }
}
