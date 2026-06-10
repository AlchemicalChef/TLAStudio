import SwiftUI

// MARK: - Status Iconography
//
// Single source of truth for severity/status SF Symbols and SwiftUI colors so
// the problems panel, hover popover, status bar, and proof views cannot drift.

extension TLADiagnosticSeverity {
    /// SF Symbol for this severity.
    var iconName: String {
        switch self {
        case .error: return "xmark.circle.fill"
        case .warning: return "exclamationmark.triangle.fill"
        case .information: return "info.circle.fill"
        case .hint: return "lightbulb.fill"
        }
    }

    /// Display color. Warning is orange everywhere, matching the editor
    /// squiggle (`DiagnosticHighlighter.underlineColor`).
    var color: Color {
        switch self {
        case .error: return .red
        case .warning: return .orange
        case .information: return .blue
        case .hint: return .green
        }
    }
}

extension ProofStatus {
    /// SF Symbol for this status (the canonical mapping is `symbolName`).
    var iconName: String { symbolName }

    /// Display color (SwiftUI twin of the gutter's `iconColor` NSColor).
    var color: Color {
        switch self {
        case .unknown: return .secondary
        case .pending: return .yellow
        case .proved: return .green
        case .failed: return .red
        case .timeout: return .orange
        case .omitted: return .gray
        case .trivial: return .green
        }
    }
}
