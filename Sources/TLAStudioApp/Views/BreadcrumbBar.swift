import SwiftUI

// MARK: - Breadcrumb Bar

/// Navigation breadcrumb bar that shows the current location in the module hierarchy
struct BreadcrumbBar: View {
    let moduleName: String
    let currentSymbol: TLASymbol?
    let symbols: [TLASymbol]
    let onNavigateToModule: () -> Void
    let onNavigateToSymbol: (TLASymbol) -> Void

    @State private var showSymbolPicker = false

    var body: some View {
        HStack(spacing: 4) {
            // Module name
            Button(action: onNavigateToModule) {
                HStack(spacing: 2) {
                    Image(systemName: "doc.text")
                        .font(.caption)
                        .foregroundColor(.secondary)
                    Text(moduleName.isEmpty ? "Untitled" : moduleName)
                        .font(.system(size: 12))
                }
            }
            .buttonStyle(.plain)
            .foregroundColor(.primary)

            // Symbol chain
            if let symbol = currentSymbol {
                Image(systemName: "chevron.right")
                    .font(.system(size: 9, weight: .medium))
                    .foregroundColor(.secondary)

                Button(action: { showSymbolPicker.toggle() }) {
                    HStack(spacing: 4) {
                        symbolIcon(for: symbol.kind)
                            .font(.caption)
                            .foregroundColor(symbolColor(for: symbol.kind))
                        Text(symbol.name)
                            .font(.system(size: 12))
                        Image(systemName: "chevron.down")
                            .font(.system(size: 9, weight: .medium))
                            .foregroundColor(.secondary)
                    }
                }
                .buttonStyle(.plain)
                .foregroundColor(.primary)
                .popover(isPresented: $showSymbolPicker, arrowEdge: .bottom) {
                    symbolPickerContent
                }
            }

            Spacer()
        }
        .padding(.horizontal, 10)
        .padding(.vertical, 4)
        .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: - Symbol Picker

    private var symbolPickerContent: some View {
        VStack(alignment: .leading, spacing: 0) {
            ForEach(flattenedSymbols, id: \.id) { symbol in
                Button(action: {
                    onNavigateToSymbol(symbol)
                    showSymbolPicker = false
                }) {
                    HStack(spacing: 6) {
                        symbolIcon(for: symbol.kind)
                            .foregroundColor(symbolColor(for: symbol.kind))
                            .frame(width: 16)
                        Text(symbol.name)
                            .font(.system(size: 12))
                        Spacer()
                    }
                    .padding(.horizontal, 8)
                    .padding(.vertical, 4)
                    .contentShape(Rectangle())
                }
                .buttonStyle(.plain)
                .background(symbol.id == currentSymbol?.id ? Color.accentColor.opacity(0.2) : Color.clear)
            }
        }
        .frame(minWidth: 180, maxHeight: 300)
        .padding(.vertical, 4)
    }

    // MARK: - Helpers

    private var flattenedSymbols: [TLASymbol] {
        var result: [TLASymbol] = []
        func addSymbols(_ symbols: [TLASymbol]) {
            for symbol in symbols {
                // Skip module symbol in the list
                if symbol.kind != .module {
                    result.append(symbol)
                }
                addSymbols(symbol.children)
            }
        }
        addSymbols(symbols)
        return result
    }

    private func symbolIcon(for kind: TLASymbolKind) -> Image {
        switch kind {
        case .module:
            return Image(systemName: "doc.text")
        case .operator:
            return Image(systemName: "function")
        case .variable:
            return Image(systemName: "v.square")
        case .constant:
            return Image(systemName: "c.square")
        case .theorem:
            return Image(systemName: "t.square")
        case .definition:
            return Image(systemName: "d.square")
        case .instance:
            return Image(systemName: "arrow.right.square")
        case .assumption:
            return Image(systemName: "a.square")
        }
    }

    private func symbolColor(for kind: TLASymbolKind) -> Color {
        switch kind {
        case .module:
            return .blue
        case .operator:
            return .purple
        case .variable:
            return .orange
        case .constant:
            return .teal
        case .theorem:
            return .green
        case .definition:
            return .indigo
        case .instance:
            return .blue
        case .assumption:
            return .gray
        }
    }
}

// MARK: - Symbol Finder

extension BreadcrumbBar {

    /// Find the symbol containing the given line number
    static func findSymbolAtLine(_ line: Int, in symbols: [TLASymbol]) -> TLASymbol? {
        // Search for the innermost symbol containing this line
        func search(_ symbols: [TLASymbol]) -> TLASymbol? {
            for symbol in symbols.reversed() {
                let startLine = Int(symbol.range.start.line)
                let endLine = Int(symbol.range.end.line)

                if line >= startLine && line <= endLine {
                    // Check children first for more specific match
                    if let childMatch = search(symbol.children) {
                        return childMatch
                    }
                    // Return this symbol if no child matches
                    if symbol.kind != .module {
                        return symbol
                    }
                }
            }
            return nil
        }

        return search(symbols)
    }
}

// MARK: - Preview

#if DEBUG
struct BreadcrumbBar_Previews: PreviewProvider {
    static var previews: some View {
        VStack(spacing: 0) {
            BreadcrumbBar(
                moduleName: "TwoPhaseCommit",
                currentSymbol: TLASymbol(
                    name: "Init",
                    kind: .operator,
                    range: TLARange(
                        start: TLAPosition(line: 10, column: 0),
                        end: TLAPosition(line: 15, column: 0)
                    ),
                    selectionRange: nil,
                    children: []
                ),
                symbols: [],
                onNavigateToModule: {},
                onNavigateToSymbol: { _ in }
            )
            Divider()
            BreadcrumbBar(
                moduleName: "SimpleSpec",
                currentSymbol: nil,
                symbols: [],
                onNavigateToModule: {},
                onNavigateToSymbol: { _ in }
            )
        }
    }
}
#endif
