import SwiftUI
import os

// MARK: - Search Panel

/// Provides search functionality across the current document and related files
struct SearchView: View {
    @ObservedObject var document: TLADocument
    @StateObject private var searchManager = DocumentSearchManager()
    @State private var isSearching = false

    var body: some View {
        VStack(spacing: 0) {
            // Search input
            searchInputView

            Divider()

            // Search options
            searchOptionsView

            Divider()

            // Results
            if searchManager.query.isEmpty {
                emptySearchView
            } else if isSearching {
                ProgressView("Searching...")
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
            } else if searchManager.results.isEmpty {
                noResultsView
            } else {
                searchResultsView
            }
        }
        .onChange(of: document.content) { _, _ in
            // Re-search when document changes (if we have an active query)
            if !searchManager.query.isEmpty {
                performSearch()
            }
        }
    }

    // MARK: - Search Input

    private var searchInputView: some View {
        HStack(spacing: 8) {
            Image(systemName: "magnifyingglass")
                .foregroundColor(.secondary)

            TextField("Search in document", text: $searchManager.query)
                .textFieldStyle(.plain)
                .onSubmit {
                    performSearch()
                }

            if !searchManager.query.isEmpty {
                Button {
                    searchManager.query = ""
                    searchManager.results = []
                } label: {
                    Image(systemName: "xmark.circle.fill")
                        .foregroundColor(.secondary)
                }
                .buttonStyle(.plain)
            }
        }
        .padding(10)
        .background(Color(NSColor.textBackgroundColor))
        .cornerRadius(8)
        .padding(8)
    }

    // MARK: - Search Options

    private var searchOptionsView: some View {
        HStack(spacing: 12) {
            Toggle("Match Case", isOn: $searchManager.caseSensitive)
                .toggleStyle(.checkbox)
                .controlSize(.small)

            Toggle("Whole Word", isOn: $searchManager.wholeWord)
                .toggleStyle(.checkbox)
                .controlSize(.small)

            Toggle("Regex", isOn: $searchManager.useRegex)
                .toggleStyle(.checkbox)
                .controlSize(.small)

            Spacer()
        }
        .padding(.horizontal, 12)
        .padding(.vertical, 6)
        .onChange(of: searchManager.caseSensitive) { _, _ in performSearch() }
        .onChange(of: searchManager.wholeWord) { _, _ in performSearch() }
        .onChange(of: searchManager.useRegex) { _, _ in performSearch() }
    }

    // MARK: - Empty State

    private var emptySearchView: some View {
        VStack(spacing: 12) {
            Image(systemName: "magnifyingglass")
                .font(.largeTitle)
                .foregroundColor(.secondary)

            Text("Search Document")
                .font(.headline)

            Text("Enter text to search")
                .font(.caption)
                .foregroundColor(.secondary)

            // Quick search suggestions
            VStack(alignment: .leading, spacing: 4) {
                Text("Try searching for:")
                    .font(.caption2)
                    .foregroundColor(.secondary)

                ForEach(searchSuggestions, id: \.self) { suggestion in
                    Button {
                        searchManager.query = suggestion
                        performSearch()
                    } label: {
                        Text(suggestion)
                            .font(.caption)
                            .foregroundColor(.accentColor)
                    }
                    .buttonStyle(.plain)
                }
            }
            .padding(.top, 8)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .padding()
    }

    private var searchSuggestions: [String] {
        // Suggest based on document symbols
        let symbolNames = document.symbols.prefix(3).map { $0.name }
        if symbolNames.isEmpty {
            return ["VARIABLE", "Init", "Next"]
        }
        return Array(symbolNames)
    }

    // MARK: - No Results

    private var noResultsView: some View {
        VStack(spacing: 12) {
            Image(systemName: "doc.text.magnifyingglass")
                .font(.largeTitle)
                .foregroundColor(.secondary)

            Text("No Results")
                .font(.headline)

            Text("No matches found for '\(searchManager.query)'")
                .font(.caption)
                .foregroundColor(.secondary)
                .multilineTextAlignment(.center)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .padding()
    }

    // MARK: - Results View

    private var searchResultsView: some View {
        VStack(spacing: 0) {
            // Results count header
            HStack {
                Text("\(searchManager.results.count) results")
                    .font(.caption)
                    .foregroundColor(.secondary)

                Spacer()

                Button {
                    performSearch()
                } label: {
                    Image(systemName: "arrow.clockwise")
                        .font(.caption)
                }
                .buttonStyle(.plain)
                .help("Refresh search")
            }
            .padding(.horizontal, 12)
            .padding(.vertical, 6)
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Results list
            List {
                ForEach(searchManager.results) { result in
                    SearchResultRow(result: result, document: document)
                }
            }
            .listStyle(.sidebar)
        }
    }

    // MARK: - Actions

    private func performSearch() {
        guard !searchManager.query.isEmpty else {
            searchManager.results = []
            return
        }

        isSearching = true

        Task {
            let results = await searchManager.search(in: document.content)
            await MainActor.run {
                searchManager.results = results
                isSearching = false
            }
        }
    }
}

// MARK: - Search Result Row

struct SearchResultRow: View {
    let result: SearchResult
    @ObservedObject var document: TLADocument

    var body: some View {
        Button(action: navigateToResult) {
            VStack(alignment: .leading, spacing: 4) {
                // Line number
                HStack {
                    Text("Line \(result.line + 1)")
                        .font(.caption)
                        .fontWeight(.medium)
                        .foregroundColor(.accentColor)

                    Spacer()

                    Text("Col \(result.column + 1)")
                        .font(.caption2)
                        .foregroundColor(.secondary)
                }

                // Context with highlighted match
                Text(result.attributedContext)
                    .font(.system(.caption, design: .monospaced))
                    .lineLimit(2)
            }
            .padding(.vertical, 4)
            .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
    }

    private func navigateToResult() {
        document.selectedRange = NSRange(location: result.offset, length: result.length)
        // The editor should scroll to the selection automatically
    }
}

// MARK: - Search Result

struct SearchResult: Identifiable {
    let id = UUID()
    let line: Int
    let column: Int
    let offset: Int
    let length: Int
    let matchText: String
    let contextBefore: String
    let contextAfter: String

    var attributedContext: AttributedString {
        var result = AttributedString()

        // Before context (dimmed)
        var before = AttributedString(contextBefore)
        before.foregroundColor = .secondary
        result.append(before)

        // Match (highlighted)
        var match = AttributedString(matchText)
        match.foregroundColor = .primary
        match.backgroundColor = Color.yellow.opacity(0.3)
        match.font = .system(.caption, design: .monospaced).bold()
        result.append(match)

        // After context (dimmed)
        var after = AttributedString(contextAfter)
        after.foregroundColor = .secondary
        result.append(after)

        return result
    }
}

// MARK: - Document Search Manager

@MainActor
class DocumentSearchManager: ObservableObject {
    @Published var query = ""
    @Published var caseSensitive = false
    @Published var wholeWord = false
    @Published var useRegex = false
    @Published var results: [SearchResult] = []

    private let logger = Log.logger(category: "Search")
    private let contextLength = 30

    func search(in content: String) async -> [SearchResult] {
        guard !query.isEmpty else { return [] }

        // Capture values before detached task
        let pattern = buildPattern()
        let caseSensitive = self.caseSensitive
        let ctxLength = self.contextLength

        return await Task.detached {
            var searchResults: [SearchResult] = []

            do {
                var options: NSRegularExpression.Options = []

                if !caseSensitive {
                    options.insert(.caseInsensitive)
                }

                let regex = try NSRegularExpression(pattern: pattern, options: options)
                let nsContent = content as NSString
                let range = NSRange(location: 0, length: nsContent.length)

                let matches = regex.matches(in: content, options: [], range: range)

                for match in matches {
                    let matchRange = match.range

                    // Calculate line and column
                    let textBefore = nsContent.substring(with: NSRange(location: 0, length: matchRange.location))
                    let lines = textBefore.components(separatedBy: "\n")
                    let line = lines.count - 1
                    let column = lines.last?.count ?? 0

                    // Get match text
                    let matchText = nsContent.substring(with: matchRange)

                    // Get context
                    let contextStart = max(0, matchRange.location - ctxLength)
                    let contextEnd = min(nsContent.length, matchRange.location + matchRange.length + ctxLength)

                    let beforeRange = NSRange(location: contextStart, length: matchRange.location - contextStart)
                    let afterRange = NSRange(location: matchRange.location + matchRange.length,
                                            length: contextEnd - matchRange.location - matchRange.length)

                    var contextBefore = nsContent.substring(with: beforeRange)
                    var contextAfter = nsContent.substring(with: afterRange)

                    // Clean up context (remove newlines, trim)
                    contextBefore = contextBefore.replacingOccurrences(of: "\n", with: " ")
                    contextAfter = contextAfter.replacingOccurrences(of: "\n", with: " ")

                    if contextStart > 0 {
                        contextBefore = "..." + contextBefore.trimmingCharacters(in: .whitespaces)
                    }
                    if contextEnd < nsContent.length {
                        contextAfter = contextAfter.trimmingCharacters(in: .whitespaces) + "..."
                    }

                    let result = SearchResult(
                        line: line,
                        column: column,
                        offset: matchRange.location,
                        length: matchRange.length,
                        matchText: matchText,
                        contextBefore: contextBefore,
                        contextAfter: contextAfter
                    )

                    searchResults.append(result)
                }
            } catch {
                // Invalid regex - return empty results
                await MainActor.run {
                    self.logger.warning("Search regex error: \(error.localizedDescription)")
                }
            }

            return searchResults
        }.value
    }

    private func buildPattern() -> String {
        var pattern: String

        if useRegex {
            pattern = query
        } else {
            pattern = NSRegularExpression.escapedPattern(for: query)
        }

        if wholeWord {
            pattern = "\\b\(pattern)\\b"
        }

        return pattern
    }
}

// MARK: - Preview

#if DEBUG
struct SearchView_Previews: PreviewProvider {
    static var previews: some View {
        SearchView(document: TLADocument())
            .frame(width: 250, height: 400)
    }
}
#endif
