import SwiftUI

// MARK: - Navigator Sidebar

struct NavigatorSidebar: View {
    @ObservedObject var document: TLADocument
    @State private var selectedTab = 1 // Default to symbols

    private var symbolCount: Int {
        countSymbols(document.symbols)
    }

    private var problemCount: Int {
        document.diagnostics.count
    }

    var body: some View {
        VStack(spacing: 0) {
            // Custom tab bar with badges
            HStack(spacing: 4) {
                // File navigator tab with dirty indicator
                NavigatorTabButton(
                    icon: "folder",
                    isSelected: selectedTab == 0,
                    badge: document.hasUnautosavedChanges ? ("•", .orange) : nil,
                    action: { selectedTab = 0 }
                )
                .help("Files")

                // Symbols tab with count
                NavigatorTabButton(
                    icon: "list.bullet.indent",
                    isSelected: selectedTab == 1,
                    badge: symbolCount > 0 ? ("\(symbolCount)", .secondary) : nil,
                    action: { selectedTab = 1 }
                )
                .help("Symbols")

                // Search tab
                NavigatorTabButton(
                    icon: "magnifyingglass",
                    isSelected: selectedTab == 2,
                    badge: nil,
                    action: { selectedTab = 2 }
                )
                .help("Search (⇧⌘F)")
            }
            .padding(8)

            Divider()

            // Tab content
            switch selectedTab {
            case 0:
                FileNavigatorView(document: document)
            case 1:
                EnhancedSymbolOutline(document: document)
            case 2:
                SearchView(document: document)
            default:
                EmptyView()
            }
        }
    }

    private func countSymbols(_ symbols: [TLASymbol]) -> Int {
        symbols.reduce(0) { count, symbol in
            count + 1 + countSymbols(symbol.children)
        }
    }
}

// MARK: - Navigator Tab Button

struct NavigatorTabButton: View {
    let icon: String
    let isSelected: Bool
    var badge: (String, Color)?
    let action: () -> Void

    var body: some View {
        Button(action: action) {
            HStack(spacing: 2) {
                Image(systemName: icon)
                    .font(.system(size: 12))

                if let badge = badge {
                    Text(badge.0)
                        .font(.system(size: 9, weight: .medium))
                        .foregroundColor(badge.1 == .secondary ? .secondary : .white)
                        .padding(.horizontal, badge.0 == "•" ? 0 : 4)
                        .padding(.vertical, 1)
                        .background(badge.1 == .secondary ? Color.clear : badge.1)
                        .clipShape(Capsule())
                }
            }
            .frame(minWidth: 36, minHeight: 24)
            .background(isSelected ? Color.accentColor.opacity(0.2) : Color.clear)
            .cornerRadius(6)
        }
        .buttonStyle(.plain)
    }
}
