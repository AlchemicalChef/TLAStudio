import AppKit
import SwiftUI
import SourceEditor

// MARK: - FindReplaceHostingView

/// NSView wrapper that hosts the SwiftUI FindReplacePanel.
///
/// This view bridges the SwiftUI find/replace interface with AppKit's view hierarchy,
/// allowing the find panel to be added to the editor's scroll view or window.
///
/// Usage:
/// ```swift
/// let manager = FindReplaceManager()
/// let hostingView = FindReplaceHostingView(manager: manager)
/// parentView.addSubview(hostingView)
/// hostingView.isVisible = true
/// ```
final class FindReplaceHostingView: NSView {

    // MARK: - Properties

    private var hostingView: NSHostingView<FindReplacePanel>?
    private let manager: FindReplaceManager

    /// The height of the panel when only the find row is visible.
    private static let findOnlyHeight: CGFloat = 36

    /// The height of the panel when both find and replace rows are visible.
    private static let findReplaceHeight: CGFloat = 70

    /// Controls the visibility of the find/replace panel.
    ///
    /// When set to `true`, the panel becomes visible and the search field
    /// receives keyboard focus. When set to `false`, the panel is hidden.
    var isVisible: Bool {
        get { !isHidden }
        set {
            isHidden = !newValue
            if newValue {
                focusSearchField()
            }
        }
    }

    // MARK: - Initialization

    /// Creates a new find/replace hosting view.
    ///
    /// - Parameter manager: The FindReplaceManager that coordinates find/replace operations.
    init(manager: FindReplaceManager) {
        self.manager = manager
        super.init(frame: .zero)
        setup()
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    // MARK: - Setup

    private func setup() {
        // Create the SwiftUI panel
        let panel = FindReplacePanel(manager: manager)
        let hosting = NSHostingView(rootView: panel)
        hosting.translatesAutoresizingMaskIntoConstraints = false

        addSubview(hosting)
        hostingView = hosting

        // Pin hosting view to all edges
        NSLayoutConstraint.activate([
            hosting.topAnchor.constraint(equalTo: topAnchor),
            hosting.leadingAnchor.constraint(equalTo: leadingAnchor),
            hosting.trailingAnchor.constraint(equalTo: trailingAnchor),
            hosting.bottomAnchor.constraint(equalTo: bottomAnchor)
        ])

        // Start hidden by default
        isHidden = true

        // Subscribe to manager changes to update intrinsic size
        setupManagerObservation()
    }

    private func setupManagerObservation() {
        // Observe showReplace changes to update intrinsic content size
        // The manager's showReplace property affects the panel height
        NotificationCenter.default.addObserver(
            self,
            selector: #selector(invalidateIntrinsicSize),
            name: .findReplacePanelHeightChanged,
            object: manager
        )
    }

    @objc private func invalidateIntrinsicSize() {
        invalidateIntrinsicContentSize()
        superview?.needsLayout = true
    }

    // MARK: - Layout

    override var intrinsicContentSize: NSSize {
        // Return appropriate height based on whether replace row is shown
        let height = manager.showReplace ? Self.findReplaceHeight : Self.findOnlyHeight
        return NSSize(width: NSView.noIntrinsicMetric, height: height)
    }

    override var isFlipped: Bool {
        // Use flipped coordinate system for easier positioning at top of container
        true
    }

    // MARK: - Focus Management

    /// Focuses the search text field.
    ///
    /// This method makes the search field the first responder, allowing
    /// immediate keyboard input when the panel becomes visible.
    func focusSearchField() {
        // Post notification to request focus - the SwiftUI view will handle this
        NotificationCenter.default.post(
            name: .findReplaceFocusSearchField,
            object: self
        )
    }

    /// Focuses the replace text field.
    ///
    /// This method makes the replace field the first responder when the user
    /// wants to enter replacement text.
    func focusReplaceField() {
        NotificationCenter.default.post(
            name: .findReplaceFocusReplaceField,
            object: self
        )
    }

    // MARK: - Cleanup

    deinit {
        NotificationCenter.default.removeObserver(self)
    }
}

// MARK: - TLASourceEditor Extension

extension TLASourceEditor {

    /// Shows the find/replace panel.
    ///
    /// Posts a notification that window controllers or parent views can observe
    /// to display the find/replace interface.
    func showFindReplace() {
        NotificationCenter.default.post(name: .showFindReplace, object: self)
    }

    /// Hides the find/replace panel.
    ///
    /// Posts a notification that window controllers or parent views can observe
    /// to hide the find/replace interface.
    func hideFindReplace() {
        NotificationCenter.default.post(name: .hideFindReplace, object: self)
    }

    /// Toggles the visibility of the find/replace panel.
    ///
    /// Posts a notification that window controllers or parent views can observe
    /// to toggle the find/replace interface visibility.
    func toggleFindReplace() {
        NotificationCenter.default.post(name: .toggleFindReplace, object: self)
    }
}

// MARK: - Notification Names

extension Notification.Name {

    // MARK: Panel Visibility

    /// Posted when the find/replace panel should be shown.
    ///
    /// The `object` of this notification is the `TLASourceEditor` instance
    /// requesting the panel.
    static let showFindReplace = Notification.Name("TLAShowFindReplace")

    /// Posted when the find/replace panel should be hidden.
    ///
    /// The `object` of this notification is the `TLASourceEditor` instance
    /// requesting the panel be hidden.
    static let hideFindReplace = Notification.Name("TLAHideFindReplace")

    /// Posted when the find/replace panel visibility should be toggled.
    ///
    /// The `object` of this notification is the `TLASourceEditor` instance
    /// requesting the toggle.
    static let toggleFindReplace = Notification.Name("TLAToggleFindReplace")

    // MARK: Panel Internal

    /// Posted when the find/replace panel height changes.
    ///
    /// The `object` of this notification is the `FindReplaceManager` instance.
    /// This notification is used internally to update the hosting view's
    /// intrinsic content size.
    static let findReplacePanelHeightChanged = Notification.Name("TLAFindReplacePanelHeightChanged")

    /// Posted to request focus on the search field.
    ///
    /// The `object` of this notification is the `FindReplaceHostingView` instance.
    static let findReplaceFocusSearchField = Notification.Name("TLAFindReplaceFocusSearchField")

    /// Posted to request focus on the replace field.
    ///
    /// The `object` of this notification is the `FindReplaceHostingView` instance.
    static let findReplaceFocusReplaceField = Notification.Name("TLAFindReplaceFocusReplaceField")
}
