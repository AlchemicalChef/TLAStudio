import SwiftUI
import UniformTypeIdentifiers

// MARK: - File Navigator

/// Displays project files and related TLA+ files in a tree structure
struct FileNavigatorView: View {
    @ObservedObject var document: TLADocument
    @StateObject private var fileManager = ProjectFileManager()
    @State private var selectedFileURL: URL?
    @State private var expandedFolders: Set<URL> = []

    var body: some View {
        VStack(spacing: 0) {
            // Header with folder info
            fileHeaderView

            Divider()

            // File tree
            if fileManager.isLoading {
                ProgressView("Loading files...")
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
            } else if fileManager.projectFiles.isEmpty {
                emptyStateView
            } else {
                fileListView
            }
        }
        .onAppear {
            loadProjectFiles()
        }
        .onChange(of: document.fileURL) { _, _ in
            loadProjectFiles()
        }
    }

    // MARK: - Actions

    private func loadProjectFiles() {
        guard let fileURL = document.fileURL else {
            fileManager.projectFiles = []
            fileManager.projectFolder = nil
            return
        }
        fileManager.loadFiles(around: fileURL)
    }

    private func openFile(_ url: URL) {
        NSDocumentController.shared.openDocument(withContentsOf: url, display: true) { _, _, error in
            if let error = error {
                print("Error opening file: \(error)")
            }
        }
    }

    private func toggleFolder(_ url: URL) {
        if expandedFolders.contains(url) {
            expandedFolders.remove(url)
        } else {
            expandedFolders.insert(url)
        }
    }

    // MARK: - Header

    private var fileHeaderView: some View {
        HStack {
            if let folderURL = fileManager.projectFolder {
                Image(systemName: "folder.fill")
                    .foregroundColor(.accentColor)
                Text(folderURL.lastPathComponent)
                    .font(.headline)
                    .lineLimit(1)
            } else {
                Image(systemName: "doc.text")
                    .foregroundColor(.secondary)
                Text("Untitled Project")
                    .font(.headline)
                    .foregroundColor(.secondary)
            }
            Spacer()

            // Refresh button
            Button {
                loadProjectFiles()
            } label: {
                Image(systemName: "arrow.clockwise")
                    .font(.caption)
            }
            .buttonStyle(.plain)
            .help("Refresh file list")
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 8)
        .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: - Empty State

    private var emptyStateView: some View {
        VStack(spacing: 12) {
            Image(systemName: "folder.badge.questionmark")
                .font(.largeTitle)
                .foregroundColor(.secondary)

            Text("No Project Folder")
                .font(.headline)

            Text("Save the document to see related files")
                .font(.caption)
                .foregroundColor(.secondary)
                .multilineTextAlignment(.center)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .padding()
    }

    // MARK: - File List

    private var fileListView: some View {
        List(selection: $selectedFileURL) {
            // Current document (highlighted)
            if let currentURL = document.fileURL {
                FileRowView(
                    file: ProjectFile(url: currentURL, isDirectory: false),
                    isCurrentDocument: true,
                    isExpanded: .constant(false),
                    onToggleExpand: {},
                    onOpen: {}
                )
                .tag(currentURL)
            }

            // Related files
            ForEach(fileManager.projectFiles) { file in
                if file.url != document.fileURL {
                    fileRow(for: file)
                }
            }
        }
        .listStyle(.sidebar)
    }

    @ViewBuilder
    private func fileRow(for file: ProjectFile) -> some View {
        if file.isDirectory {
            DisclosureGroup(
                isExpanded: Binding(
                    get: { expandedFolders.contains(file.url) },
                    set: { isExpanded in
                        if isExpanded {
                            expandedFolders.insert(file.url)
                        } else {
                            expandedFolders.remove(file.url)
                        }
                    }
                )
            ) {
                ForEach(file.children) { child in
                    FileRowViewItem(
                        file: child,
                        expandedFolders: $expandedFolders,
                        onOpen: { openFile(child.url) }
                    )
                }
            } label: {
                FileRowView(
                    file: file,
                    isCurrentDocument: false,
                    isExpanded: .constant(expandedFolders.contains(file.url)),
                    onToggleExpand: { toggleFolder(file.url) },
                    onOpen: {}
                )
            }
        } else {
            FileRowView(
                file: file,
                isCurrentDocument: false,
                isExpanded: .constant(false),
                onToggleExpand: {},
                onOpen: { openFile(file.url) }
            )
            .tag(file.url)
        }
    }
}

// MARK: - File Row Item (Non-recursive)

struct FileRowViewItem: View {
    let file: ProjectFile
    @Binding var expandedFolders: Set<URL>
    let onOpen: () -> Void

    var body: some View {
        if file.isDirectory {
            DisclosureGroup(
                isExpanded: Binding(
                    get: { expandedFolders.contains(file.url) },
                    set: { isExpanded in
                        if isExpanded {
                            expandedFolders.insert(file.url)
                        } else {
                            expandedFolders.remove(file.url)
                        }
                    }
                )
            ) {
                ForEach(file.children) { child in
                    FileRowViewItem(
                        file: child,
                        expandedFolders: $expandedFolders,
                        onOpen: onOpen
                    )
                }
            } label: {
                FileRowView(
                    file: file,
                    isCurrentDocument: false,
                    isExpanded: .constant(expandedFolders.contains(file.url)),
                    onToggleExpand: {},
                    onOpen: {}
                )
            }
        } else {
            FileRowView(
                file: file,
                isCurrentDocument: false,
                isExpanded: .constant(false),
                onToggleExpand: {},
                onOpen: onOpen
            )
        }
    }
}

// MARK: - File Row View

struct FileRowView: View {
    let file: ProjectFile
    let isCurrentDocument: Bool
    @Binding var isExpanded: Bool
    let onToggleExpand: () -> Void
    let onOpen: () -> Void

    var body: some View {
        Button(action: {
            if file.isDirectory {
                onToggleExpand()
            } else {
                onOpen()
            }
        }) {
            HStack(spacing: 6) {
                fileIcon
                    .frame(width: 16)

                Text(file.name)
                    .font(.system(.body, design: file.isTLAFile ? .monospaced : .default))
                    .fontWeight(isCurrentDocument ? .semibold : .regular)
                    .lineLimit(1)

                Spacer()

                if isCurrentDocument {
                    Text("Current")
                        .font(.caption2)
                        .foregroundColor(.secondary)
                        .padding(.horizontal, 4)
                        .padding(.vertical, 2)
                        .background(Color.accentColor.opacity(0.2))
                        .cornerRadius(4)
                }
            }
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
    }

    @ViewBuilder
    private var fileIcon: some View {
        if file.isDirectory {
            Image(systemName: isExpanded ? "folder.fill" : "folder")
                .foregroundColor(.accentColor)
        } else if file.isTLAFile {
            Image(systemName: "doc.text.fill")
                .foregroundColor(.blue)
        } else if file.isConfigFile {
            Image(systemName: "gearshape.fill")
                .foregroundColor(.orange)
        } else {
            Image(systemName: "doc")
                .foregroundColor(.secondary)
        }
    }
}

// MARK: - Project File Model

struct ProjectFile: Identifiable {
    let id = UUID()
    let url: URL
    let isDirectory: Bool
    var children: [ProjectFile] = []

    var name: String { url.lastPathComponent }

    var isTLAFile: Bool {
        let ext = url.pathExtension.lowercased()
        return ext == "tla" || ext == "pcal"
    }

    var isConfigFile: Bool {
        let ext = url.pathExtension.lowercased()
        return ext == "cfg" || ext == "json"
    }
}

// MARK: - Project File Manager

@MainActor
class ProjectFileManager: ObservableObject {
    @Published var projectFiles: [ProjectFile] = []
    @Published var projectFolder: URL?
    @Published var isLoading = false

    private let supportedExtensions = ["tla", "pcal", "cfg", "json", "md", "txt"]

    func loadFiles(around fileURL: URL) {
        isLoading = true

        let folderURL = fileURL.deletingLastPathComponent()
        projectFolder = folderURL

        Task {
            let files = await scanDirectory(folderURL, depth: 2)
            await MainActor.run {
                self.projectFiles = files.sorted { $0.name.lowercased() < $1.name.lowercased() }
                self.isLoading = false
            }
        }
    }

    private func scanDirectory(_ url: URL, depth: Int) async -> [ProjectFile] {
        guard depth > 0 else { return [] }

        let fm = FileManager.default
        var results: [ProjectFile] = []

        do {
            let contents = try fm.contentsOfDirectory(
                at: url,
                includingPropertiesForKeys: [.isDirectoryKey],
                options: [.skipsHiddenFiles]
            )

            for itemURL in contents {
                let resourceValues = try? itemURL.resourceValues(forKeys: [.isDirectoryKey])
                let isDirectory = resourceValues?.isDirectory ?? false

                if isDirectory {
                    // Only include directories with relevant files
                    let children = await scanDirectory(itemURL, depth: depth - 1)
                    if !children.isEmpty {
                        var file = ProjectFile(url: itemURL, isDirectory: true)
                        file.children = children
                        results.append(file)
                    }
                } else {
                    // Only include supported file types
                    let ext = itemURL.pathExtension.lowercased()
                    if supportedExtensions.contains(ext) {
                        results.append(ProjectFile(url: itemURL, isDirectory: false))
                    }
                }
            }
        } catch {
            print("Error scanning directory: \(error)")
        }

        return results
    }
}

// MARK: - Enhanced Symbol Outline

/// Enhanced symbol outline with filtering and grouping
struct EnhancedSymbolOutline: View {
    @ObservedObject var document: TLADocument
    @State private var filterText = ""
    @State private var groupByKind = false
    @State private var showOnlyPublic = false
    @State private var expandedGroups: Set<TLASymbolKind> = Set(TLASymbolKind.allCases)

    private var filteredSymbols: [TLASymbol] {
        let symbols = document.symbols

        if filterText.isEmpty {
            return symbols
        }

        return filterSymbols(symbols, matching: filterText)
    }

    private var groupedSymbols: [(kind: TLASymbolKind, symbols: [TLASymbol])] {
        let allSymbols = flattenSymbols(filteredSymbols)

        var groups: [TLASymbolKind: [TLASymbol]] = [:]
        for symbol in allSymbols {
            groups[symbol.kind, default: []].append(symbol)
        }

        return TLASymbolKind.allCases.compactMap { kind in
            guard let symbols = groups[kind], !symbols.isEmpty else { return nil }
            return (kind: kind, symbols: symbols)
        }
    }

    var body: some View {
        VStack(spacing: 0) {
            // Search and options bar
            searchBar

            Divider()

            // Symbol list
            if filteredSymbols.isEmpty {
                emptyStateView
            } else if groupByKind {
                groupedListView
            } else {
                hierarchicalListView
            }
        }
    }

    // MARK: - Search Bar

    private var searchBar: some View {
        VStack(spacing: 8) {
            HStack {
                Image(systemName: "magnifyingglass")
                    .foregroundColor(.secondary)
                    .font(.caption)

                TextField("Filter symbols", text: $filterText)
                    .textFieldStyle(.plain)
                    .font(.caption)

                if !filterText.isEmpty {
                    Button {
                        filterText = ""
                    } label: {
                        Image(systemName: "xmark.circle.fill")
                            .foregroundColor(.secondary)
                    }
                    .buttonStyle(.plain)
                }
            }
            .padding(6)
            .background(Color(NSColor.textBackgroundColor))
            .cornerRadius(6)

            HStack {
                Toggle("Group", isOn: $groupByKind)
                    .toggleStyle(.checkbox)
                    .controlSize(.small)

                Spacer()

                Text("\(countSymbols(filteredSymbols)) symbols")
                    .font(.caption2)
                    .foregroundColor(.secondary)
            }
        }
        .padding(8)
    }

    // MARK: - Empty State

    private var emptyStateView: some View {
        VStack(spacing: 12) {
            Image(systemName: "list.bullet.indent")
                .font(.largeTitle)
                .foregroundColor(.secondary)

            if filterText.isEmpty {
                Text("No Symbols")
                    .font(.headline)
                Text("Symbols will appear here after parsing")
                    .font(.caption)
                    .foregroundColor(.secondary)
            } else {
                Text("No Matches")
                    .font(.headline)
                Text("No symbols match '\(filterText)'")
                    .font(.caption)
                    .foregroundColor(.secondary)
            }
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .padding()
    }

    // MARK: - Grouped List

    private var groupedListView: some View {
        List {
            ForEach(groupedSymbols, id: \.kind) { group in
                DisclosureGroup(
                    isExpanded: Binding(
                        get: { expandedGroups.contains(group.kind) },
                        set: { isExpanded in
                            if isExpanded {
                                expandedGroups.insert(group.kind)
                            } else {
                                expandedGroups.remove(group.kind)
                            }
                        }
                    )
                ) {
                    ForEach(group.symbols) { symbol in
                        SymbolRowView(symbol: symbol, document: document, showKindIcon: false)
                    }
                } label: {
                    HStack {
                        symbolKindIcon(group.kind)
                        Text(group.kind.pluralDisplayName)
                            .font(.subheadline)
                            .fontWeight(.medium)
                        Spacer()
                        Text("\(group.symbols.count)")
                            .font(.caption)
                            .foregroundColor(.secondary)
                    }
                }
            }
        }
        .listStyle(.sidebar)
    }

    // MARK: - Hierarchical List

    private var hierarchicalListView: some View {
        List {
            ForEach(filteredSymbols) { symbol in
                SymbolTreeRow(symbol: symbol, document: document, level: 0)
            }
        }
        .listStyle(.sidebar)
    }

    // MARK: - Helpers

    private func filterSymbols(_ symbols: [TLASymbol], matching query: String) -> [TLASymbol] {
        symbols.filter { symbol in
            symbolMatchesQuery(symbol, query: query)
        }
    }

    private func symbolMatchesQuery(_ symbol: TLASymbol, query: String) -> Bool {
        // Check if this symbol matches
        if symbol.name.localizedCaseInsensitiveContains(query) {
            return true
        }
        // Check if any child matches
        return symbol.children.contains { symbolMatchesQuery($0, query: query) }
    }

    private func flattenSymbols(_ symbols: [TLASymbol]) -> [TLASymbol] {
        symbols.flatMap { symbol in
            [symbol] + flattenSymbols(symbol.children)
        }
    }

    private func countSymbols(_ symbols: [TLASymbol]) -> Int {
        symbols.reduce(0) { count, symbol in
            count + 1 + countSymbols(symbol.children)
        }
    }

    @ViewBuilder
    private func symbolKindIcon(_ kind: TLASymbolKind) -> some View {
        switch kind {
        case .module:
            Image(systemName: "cube.fill").foregroundColor(.blue)
        case .operator:
            Image(systemName: "function").foregroundColor(.purple)
        case .variable:
            Image(systemName: "v.square.fill").foregroundColor(.green)
        case .constant:
            Image(systemName: "c.square.fill").foregroundColor(.orange)
        case .theorem:
            Image(systemName: "checkmark.seal.fill").foregroundColor(.teal)
        case .definition:
            Image(systemName: "equal.square.fill").foregroundColor(.indigo)
        case .instance:
            Image(systemName: "arrow.triangle.branch").foregroundColor(.cyan)
        case .assumption:
            Image(systemName: "exclamationmark.triangle.fill").foregroundColor(.yellow)
        }
    }
}

// MARK: - Symbol Row View

struct SymbolRowView: View {
    let symbol: TLASymbol
    @ObservedObject var document: TLADocument
    var showKindIcon: Bool = true

    var body: some View {
        Button(action: navigateToSymbol) {
            HStack(spacing: 6) {
                if showKindIcon {
                    symbolIcon
                        .frame(width: 16)
                }

                Text(symbol.name)
                    .font(.system(.body, design: .monospaced))
                    .lineLimit(1)

                Spacer()

                Text("Ln \(symbol.range.start.line + 1)")
                    .font(.caption2)
                    .foregroundColor(.secondary)
            }
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
    }

    private func navigateToSymbol() {
        let range = symbol.selectionRange ?? symbol.range
        let offset = document.offset(forLine: Int(range.start.line), column: Int(range.start.column))
        document.selectedRange = NSRange(location: offset, length: 0)
    }

    @ViewBuilder
    private var symbolIcon: some View {
        switch symbol.kind {
        case .module:
            Image(systemName: "cube").foregroundColor(.blue)
        case .operator:
            Image(systemName: "function").foregroundColor(.purple)
        case .variable:
            Image(systemName: "v.square").foregroundColor(.green)
        case .constant:
            Image(systemName: "c.square").foregroundColor(.orange)
        case .theorem:
            Image(systemName: "checkmark.seal").foregroundColor(.teal)
        case .definition:
            Image(systemName: "equal.square").foregroundColor(.indigo)
        case .instance:
            Image(systemName: "arrow.triangle.branch").foregroundColor(.cyan)
        case .assumption:
            Image(systemName: "exclamationmark.triangle").foregroundColor(.yellow)
        }
    }
}

// MARK: - Symbol Tree Row

struct SymbolTreeRow: View {
    let symbol: TLASymbol
    @ObservedObject var document: TLADocument
    let level: Int
    @State private var isExpanded = true

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            if symbol.children.isEmpty {
                SymbolRowView(symbol: symbol, document: document)
            } else {
                DisclosureGroup(isExpanded: $isExpanded) {
                    ForEach(symbol.children) { child in
                        SymbolTreeRow(symbol: child, document: document, level: level + 1)
                    }
                } label: {
                    SymbolRowView(symbol: symbol, document: document)
                }
            }
        }
    }
}

// MARK: - TLASymbolKind Extensions

extension TLASymbolKind: CaseIterable {
    static var allCases: [TLASymbolKind] {
        [.module, .constant, .variable, .operator, .definition, .theorem, .assumption, .instance]
    }

    var pluralDisplayName: String {
        switch self {
        case .module: return "Modules"
        case .operator: return "Operators"
        case .variable: return "Variables"
        case .constant: return "Constants"
        case .theorem: return "Theorems"
        case .definition: return "Definitions"
        case .instance: return "Instances"
        case .assumption: return "Assumptions"
        }
    }
}

