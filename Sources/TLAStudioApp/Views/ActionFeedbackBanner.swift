import SwiftUI

// MARK: - Action Feedback

/// A transient, user-visible explanation for why an action didn't happen —
/// replaces the silent `NSSound.beep()` dead-ends the platform review flagged
/// (Decompose Proof, Rename, Find References, tooling-spec failures, …).
struct ActionFeedback: Identifiable, Equatable {
    enum Style {
        case info
        case warning
        case error
    }

    let id = UUID()
    let message: String
    let style: Style
}

// MARK: - Banner

/// Compact auto-dismissing banner shown at the top of the editor area.
/// Lifetime is owned by `TLADocument.reportActionFeedback` (4 s), so the view
/// is purely presentational.
struct ActionFeedbackBanner: View {
    let feedback: ActionFeedback

    var body: some View {
        HStack(spacing: 6) {
            Image(systemName: iconName)
                .foregroundColor(iconColor)
            Text(feedback.message)
                .font(.callout)
                .lineLimit(2)
                .fixedSize(horizontal: false, vertical: true)
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 7)
        .background(.regularMaterial, in: RoundedRectangle(cornerRadius: 8))
        .overlay(
            RoundedRectangle(cornerRadius: 8)
                .strokeBorder(iconColor.opacity(0.35), lineWidth: 1)
        )
        .shadow(color: .black.opacity(0.15), radius: 5, x: 0, y: 2)
        .padding(.top, 8)
        .frame(maxWidth: 480)
        .transition(.move(edge: .top).combined(with: .opacity))
    }

    private var iconName: String {
        switch feedback.style {
        case .info: return "info.circle.fill"
        case .warning: return "exclamationmark.triangle.fill"
        case .error: return "xmark.circle.fill"
        }
    }

    private var iconColor: Color {
        switch feedback.style {
        case .info: return .blue
        case .warning: return .orange
        case .error: return .red
        }
    }
}
