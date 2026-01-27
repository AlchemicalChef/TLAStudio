import AppKit

/// A non-activating popup window for displaying completion suggestions
@MainActor
class CompletionPopupWindow: NSPanel {

    // MARK: - Properties

    private let tableView: NSTableView
    private let scrollView: NSScrollView
    private let documentationView: NSTextView
    private let documentationScrollView: NSScrollView
    private let splitView: NSSplitView

    private var completions: [TLADetailedCompletionItem] = []
    private var filteredCompletions: [TLADetailedCompletionItem] = []
    private var filterText: String = ""

    var onSelect: ((TLADetailedCompletionItem) -> Void)?
    var onDismiss: (() -> Void)?

    /// Maximum number of visible rows (without scrolling)
    private let maxVisibleRows = 10

    /// Row height for completion items
    private let rowHeight: CGFloat = 22

    /// Minimum width for the popup
    private let minWidth: CGFloat = 350

    /// Maximum width for the popup
    private let maxWidth: CGFloat = 550

    /// Documentation panel width
    private let docPanelWidth: CGFloat = 350

    /// Whether documentation panel is visible
    private var showDocumentation: Bool = false

    // MARK: - Initialization

    init() {
        // Create table view
        tableView = NSTableView()
        tableView.headerView = nil
        tableView.intercellSpacing = NSSize(width: 0, height: 0)
        tableView.rowHeight = rowHeight
        tableView.backgroundColor = .clear
        tableView.selectionHighlightStyle = .regular
        tableView.allowsEmptySelection = false
        tableView.allowsMultipleSelection = false

        // Add column
        let column = NSTableColumn(identifier: NSUserInterfaceItemIdentifier("completion"))
        column.isEditable = false
        tableView.addTableColumn(column)

        // Create scroll view for table
        scrollView = NSScrollView()
        scrollView.documentView = tableView
        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = false
        scrollView.autohidesScrollers = true
        scrollView.borderType = .noBorder
        scrollView.drawsBackground = false

        // Create documentation view
        documentationView = NSTextView()
        documentationView.isEditable = false
        documentationView.isSelectable = true
        documentationView.backgroundColor = .clear
        documentationView.drawsBackground = false
        documentationView.textContainerInset = NSSize(width: 8, height: 8)
        documentationView.font = .systemFont(ofSize: 11)
        documentationView.textColor = .secondaryLabelColor

        // Create scroll view for documentation
        documentationScrollView = NSScrollView()
        documentationScrollView.documentView = documentationView
        documentationScrollView.hasVerticalScroller = true
        documentationScrollView.hasHorizontalScroller = false
        documentationScrollView.autohidesScrollers = true
        documentationScrollView.borderType = .noBorder
        documentationScrollView.drawsBackground = false

        // Create split view
        splitView = NSSplitView()
        splitView.isVertical = true
        splitView.dividerStyle = .thin
        splitView.addArrangedSubview(scrollView)

        // Calculate initial size
        let initialHeight = CGFloat(maxVisibleRows) * rowHeight + 4
        let contentRect = NSRect(x: 0, y: 0, width: minWidth, height: initialHeight)

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

        // Create content view with visual effect
        let visualEffect = NSVisualEffectView(frame: contentRect)
        visualEffect.material = .popover
        visualEffect.blendingMode = .behindWindow
        visualEffect.state = .active
        visualEffect.wantsLayer = true
        visualEffect.layer?.cornerRadius = 6
        visualEffect.layer?.masksToBounds = true

        // Add split view to visual effect view
        splitView.frame = visualEffect.bounds
        splitView.autoresizingMask = [.width, .height]
        visualEffect.addSubview(splitView)

        self.contentView = visualEffect

        // Configure table view delegate/data source
        tableView.delegate = self
        tableView.dataSource = self
        tableView.target = self
        tableView.doubleAction = #selector(handleDoubleClick)
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    // MARK: - Public Methods

    /// Show the completion popup at the specified screen location
    func show(at screenPoint: NSPoint, with items: [TLADetailedCompletionItem], filterText: String = "") {
        self.completions = items
        self.filterText = filterText
        applyFilter()

        guard !filteredCompletions.isEmpty else {
            dismiss()
            return
        }

        // Calculate size based on content
        let rowCount = min(filteredCompletions.count, maxVisibleRows)
        let tableHeight = CGFloat(rowCount) * rowHeight + 4

        var width = minWidth
        // Calculate width based on longest item
        for item in filteredCompletions.prefix(20) {
            let labelWidth = (item.label as NSString).size(withAttributes: [
                .font: NSFont.systemFont(ofSize: 12)
            ]).width
            let totalWidth = 32 + labelWidth + 100  // icon + label + detail
            width = max(width, min(totalWidth, maxWidth))
        }

        // Position the window
        var frame = self.frame
        frame.size.width = showDocumentation ? width + docPanelWidth : width
        frame.size.height = tableHeight
        frame.origin = NSPoint(x: screenPoint.x, y: screenPoint.y - tableHeight)

        // Ensure window stays on screen (use screen containing the point, not just main)
        let targetScreen = NSScreen.screens.first { $0.frame.contains(screenPoint) } ?? NSScreen.main
        if let screen = targetScreen {
            let screenFrame = screen.visibleFrame
            if frame.maxX > screenFrame.maxX {
                frame.origin.x = screenFrame.maxX - frame.width
            }
            if frame.minY < screenFrame.minY {
                frame.origin.y = screenPoint.y + 20  // Show above cursor
            }
        }

        setFrame(frame, display: true)
        tableView.reloadData()

        // Select first item
        if !filteredCompletions.isEmpty {
            tableView.selectRowIndexes(IndexSet(integer: 0), byExtendingSelection: false)
            tableView.scrollRowToVisible(0)
            updateDocumentation()
        }

        orderFront(nil)
    }

    /// Dismiss the completion popup
    func dismiss() {
        orderOut(nil)
        completions = []
        filteredCompletions = []
        onDismiss?()
    }

    /// Update the filter text and refresh the list
    func updateFilter(_ text: String) {
        filterText = text
        applyFilter()
        tableView.reloadData()

        if !filteredCompletions.isEmpty {
            tableView.selectRowIndexes(IndexSet(integer: 0), byExtendingSelection: false)
            updateDocumentation()
        } else {
            dismiss()
        }
    }

    /// Move selection up
    func selectPrevious() {
        guard !filteredCompletions.isEmpty else { return }
        let current = tableView.selectedRow
        let newRow = max(0, current - 1)
        tableView.selectRowIndexes(IndexSet(integer: newRow), byExtendingSelection: false)
        tableView.scrollRowToVisible(newRow)
        updateDocumentation()
    }

    /// Move selection down
    func selectNext() {
        guard !filteredCompletions.isEmpty else { return }
        let current = tableView.selectedRow
        let newRow = min(filteredCompletions.count - 1, current + 1)
        tableView.selectRowIndexes(IndexSet(integer: newRow), byExtendingSelection: false)
        tableView.scrollRowToVisible(newRow)
        updateDocumentation()
    }

    /// Confirm current selection
    func confirmSelection() {
        let row = tableView.selectedRow
        guard row >= 0 && row < filteredCompletions.count else { return }
        let item = filteredCompletions[row]
        onSelect?(item)
        dismiss()
    }

    /// Get the currently selected item
    var selectedItem: TLADetailedCompletionItem? {
        let row = tableView.selectedRow
        guard row >= 0 && row < filteredCompletions.count else { return nil }
        return filteredCompletions[row]
    }

    /// Toggle documentation panel
    func toggleDocumentation() {
        showDocumentation = !showDocumentation

        if showDocumentation {
            splitView.addArrangedSubview(documentationScrollView)
            var frame = self.frame
            frame.size.width += docPanelWidth
            setFrame(frame, display: true)
        } else {
            documentationScrollView.removeFromSuperview()
            var frame = self.frame
            frame.size.width -= docPanelWidth
            setFrame(frame, display: true)
        }

        updateDocumentation()
    }

    // MARK: - Private Methods

    private func applyFilter() {
        if filterText.isEmpty {
            filteredCompletions = completions
        } else {
            let lowercaseFilter = filterText.lowercased()
            filteredCompletions = completions.filter { item in
                // Check label
                if item.label.lowercased().contains(lowercaseFilter) {
                    return true
                }
                // Check filter text if available
                if let filterText = item.filterText, filterText.lowercased().contains(lowercaseFilter) {
                    return true
                }
                return false
            }

            // Sort by relevance (exact prefix match first)
            filteredCompletions.sort { a, b in
                let aPrefix = a.label.lowercased().hasPrefix(lowercaseFilter)
                let bPrefix = b.label.lowercased().hasPrefix(lowercaseFilter)
                if aPrefix != bPrefix {
                    return aPrefix
                }
                return a.sortPriority < b.sortPriority
            }
        }
    }

    private func updateDocumentation() {
        guard showDocumentation else { return }

        let row = tableView.selectedRow
        guard row >= 0 && row < filteredCompletions.count else {
            documentationView.string = ""
            return
        }

        let item = filteredCompletions[row]
        var text = ""

        // Add signature if available
        if let signature = item.signature {
            text += signature + "\n\n"
        }

        // Add documentation
        if let doc = item.documentation {
            text += doc
        }

        // Add detail if different from documentation
        if let detail = item.detail, detail != item.documentation {
            if !text.isEmpty {
                text += "\n\n"
            }
            text += detail
        }

        documentationView.string = text
    }

    @objc private func handleDoubleClick() {
        confirmSelection()
    }
}

// MARK: - NSTableViewDataSource

extension CompletionPopupWindow: NSTableViewDataSource {
    func numberOfRows(in tableView: NSTableView) -> Int {
        filteredCompletions.count
    }
}

// MARK: - NSTableViewDelegate

extension CompletionPopupWindow: NSTableViewDelegate {

    func tableView(_ tableView: NSTableView, viewFor tableColumn: NSTableColumn?, row: Int) -> NSView? {
        guard row < filteredCompletions.count else { return nil }
        let item = filteredCompletions[row]

        let cellId = NSUserInterfaceItemIdentifier("CompletionCell")
        let cell: CompletionItemCell

        if let existing = tableView.makeView(withIdentifier: cellId, owner: self) as? CompletionItemCell {
            cell = existing
        } else {
            cell = CompletionItemCell()
            cell.identifier = cellId
        }

        cell.configure(with: item, filterText: filterText)
        return cell
    }

    func tableViewSelectionDidChange(_ notification: Notification) {
        updateDocumentation()
    }
}

// MARK: - CompletionItemCell

/// Custom cell view for completion items
class CompletionItemCell: NSTableCellView {

    private let iconView: NSImageView
    private let labelField: NSTextField
    private let detailField: NSTextField

    override init(frame frameRect: NSRect) {
        iconView = NSImageView()
        iconView.imageScaling = .scaleProportionallyDown

        labelField = NSTextField(labelWithString: "")
        labelField.font = .systemFont(ofSize: 12)
        labelField.textColor = .labelColor
        labelField.lineBreakMode = .byTruncatingTail

        detailField = NSTextField(labelWithString: "")
        detailField.font = .systemFont(ofSize: 11)
        detailField.textColor = .secondaryLabelColor
        detailField.lineBreakMode = .byTruncatingTail

        super.init(frame: frameRect)

        addSubview(iconView)
        addSubview(labelField)
        addSubview(detailField)
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    override func layout() {
        super.layout()

        let iconSize: CGFloat = 16
        let padding: CGFloat = 4
        let labelWidth: CGFloat = 150

        iconView.frame = NSRect(
            x: padding,
            y: (bounds.height - iconSize) / 2,
            width: iconSize,
            height: iconSize
        )

        labelField.frame = NSRect(
            x: iconView.frame.maxX + padding,
            y: (bounds.height - labelField.intrinsicContentSize.height) / 2,
            width: labelWidth,
            height: labelField.intrinsicContentSize.height
        )

        detailField.frame = NSRect(
            x: labelField.frame.maxX + padding,
            y: (bounds.height - detailField.intrinsicContentSize.height) / 2,
            width: bounds.width - labelField.frame.maxX - padding * 2,
            height: detailField.intrinsicContentSize.height
        )
    }

    func configure(with item: TLADetailedCompletionItem, filterText: String) {
        // Set icon
        let iconName = item.iconName
        if let image = NSImage(systemSymbolName: iconName, accessibilityDescription: nil) {
            iconView.image = image
            iconView.contentTintColor = colorForKind(item.kind)
        }

        // Set label with highlight
        if filterText.isEmpty {
            labelField.stringValue = item.label
        } else {
            labelField.attributedStringValue = highlightedString(
                item.label,
                highlight: filterText
            )
        }

        // Set detail
        if let detail = item.detail {
            detailField.stringValue = detail
        } else if let sig = item.signature {
            detailField.stringValue = sig
        } else {
            detailField.stringValue = ""
        }
    }

    private func colorForKind(_ kind: TLACompletionKind) -> NSColor {
        switch kind {
        case .keyword:      return .systemPurple
        case .operator:     return .systemOrange
        case .variable:     return .systemBlue
        case .constant:     return .systemTeal
        case .module:       return .systemBrown
        case .snippet:      return .systemGray
        case .function:     return .systemGreen
        case .theorem:      return .systemIndigo
        case .proofTactic:  return .systemPink
        }
    }

    private func highlightedString(_ text: String, highlight: String) -> NSAttributedString {
        let attributed = NSMutableAttributedString(
            string: text,
            attributes: [
                .font: NSFont.systemFont(ofSize: 12),
                .foregroundColor: NSColor.labelColor
            ]
        )

        // Find and highlight matching ranges
        let lowercaseText = text.lowercased()
        let lowercaseHighlight = highlight.lowercased()
        var searchRange = lowercaseText.startIndex..<lowercaseText.endIndex

        while let range = lowercaseText.range(of: lowercaseHighlight, range: searchRange) {
            let nsRange = NSRange(range, in: text)
            attributed.addAttribute(.backgroundColor, value: NSColor.systemYellow.withAlphaComponent(0.3), range: nsRange)
            attributed.addAttribute(.font, value: NSFont.boldSystemFont(ofSize: 12), range: nsRange)
            searchRange = range.upperBound..<lowercaseText.endIndex
        }

        return attributed
    }
}
