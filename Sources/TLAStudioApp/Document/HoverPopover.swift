import SwiftUI

// MARK: - Hover Popover

struct HoverPopover: View {
    let info: HoverInfo

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            HStack(spacing: 6) {
                kindIcon
                Text(info.title)
                    .font(.system(.body, design: .monospaced).bold())
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
        .padding(8)
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(6)
        .shadow(color: .black.opacity(0.2), radius: 4, x: 0, y: 2)
        .fixedSize()
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
