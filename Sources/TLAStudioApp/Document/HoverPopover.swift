import SwiftUI

// MARK: - Hover Popover

struct HoverPopover: View {
    let info: HoverInfo

    private var hasSymbolContent: Bool { !info.title.isEmpty }

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            if !info.diagnostics.isEmpty {
                diagnosticsSection
                if hasSymbolContent {
                    Divider()
                }
            }

            if hasSymbolContent {
                HStack(spacing: 6) {
                    kindIcon
                    Text(info.title)
                        .font(.system(.body, design: .monospaced).bold())
                    if let module = info.sourceModule {
                        Text("From \(module)")
                            .font(.caption2)
                            .padding(.horizontal, 4)
                            .padding(.vertical, 1)
                            .background(Color.secondary.opacity(0.15))
                            .cornerRadius(3)
                            .foregroundColor(.secondary)
                    }
                }

                if let signature = info.signature {
                    Text(signature)
                        .font(.system(.caption, design: .monospaced))
                        .foregroundColor(.secondary)
                }

                Text(info.description)
                    .font(.caption)
                    .foregroundColor(.primary)
            }
        }
        .padding(8)
        .frame(maxWidth: 420, alignment: .leading)
        .fixedSize(horizontal: false, vertical: true)
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(6)
        .shadow(color: .black.opacity(0.2), radius: 4, x: 0, y: 2)
    }

    // MARK: Diagnostics

    private var diagnosticsSection: some View {
        VStack(alignment: .leading, spacing: 6) {
            ForEach(Array(info.diagnostics.prefix(3))) { diagnostic in
                HStack(alignment: .firstTextBaseline, spacing: 6) {
                    severityIcon(for: diagnostic.severity)
                    VStack(alignment: .leading, spacing: 2) {
                        Text(diagnostic.message)
                            .font(.caption)
                            .foregroundColor(.primary)
                            .fixedSize(horizontal: false, vertical: true)
                        if let code = diagnostic.code {
                            Text(code)
                                .font(.caption2)
                                .padding(.horizontal, 4)
                                .padding(.vertical, 1)
                                .background(
                                    diagnostic.isSemantic
                                        ? Color.purple.opacity(0.15)
                                        : Color.secondary.opacity(0.15)
                                )
                                .cornerRadius(3)
                                .foregroundColor(diagnostic.isSemantic ? .purple : .secondary)
                        }
                    }
                }
            }
            if info.diagnostics.count > 3 {
                Text("+\(info.diagnostics.count - 3) more…")
                    .font(.caption2)
                    .foregroundColor(.secondary)
            }
        }
    }

    private func severityIcon(for severity: TLADiagnosticSeverity) -> some View {
        Image(systemName: severity.iconName)
            .foregroundColor(severity.color)
            .font(.caption)
    }

    @ViewBuilder
    private var kindIcon: some View {
        switch info.kind {
        case .keyword:
            Image(systemName: "k.square.fill").foregroundColor(.blue)
        case .operator:
            Image(systemName: "function").foregroundColor(.purple)
        case .variable:
            Image(systemName: "v.square").foregroundColor(.green)
        case .constant:
            Image(systemName: "c.square").foregroundColor(.orange)
        case .module:
            Image(systemName: "cube").foregroundColor(.blue)
        case .theorem:
            Image(systemName: "checkmark.seal").foregroundColor(.teal)
        case .definition:
            Image(systemName: "equal.square").foregroundColor(.indigo)
        }
    }
}
