import AppKit

// MARK: - Document Navigator

/// Single home for "open (or focus) a document and navigate to a range".
///
/// Symbol/reference ranges carry tree-sitter BYTE columns; the conversion to
/// UTF-16 offsets must run against the *opened* document's content (wrong on
/// Unicode-bearing lines otherwise). All cross-file navigation should route
/// through here so the coordinate conversion lives in one place.
@MainActor
enum DocumentNavigator {

    /// Opens (or focuses) the document at `fileURL` and selects `range`.
    static func open(fileURL: URL, andSelect range: TLARange) {
        open(fileURL: fileURL) { _ in range }
    }

    /// Opens (or focuses) the document at `fileURL`, resolves the target
    /// range against the opened document (whose live state may be fresher
    /// than an on-disk index), then selects it.
    static func open(
        fileURL: URL,
        resolvingRange resolve: @escaping @MainActor (TLADocument) -> TLARange
    ) {
        NSDocumentController.shared.openDocument(
            withContentsOf: fileURL,
            display: true
        ) { opened, _, error in
            guard error == nil, let target = opened as? TLADocument else { return }
            Task { @MainActor in
                select(resolve(target), in: target)
            }
        }
    }

    /// Converts `range` (tree-sitter lines + byte columns) to a UTF-16 offset
    /// in `document.content` (falling back to the line start), selects it,
    /// and notifies the navigation delegate so the editor flashes/centers.
    static func select(_ range: TLARange, in document: TLADocument) {
        let converter = TextCoordinateMapper.TreeSitterRangeConverter(text: document.content)
        let location = converter.utf16Offset(
            line: Int(range.start.line),
            byteColumn: Int(range.start.column)
        ) ?? document.offset(forLine: Int(range.start.line), column: 0)
        document.selectedRange = NSRange(location: location, length: 0)
        document.delegate?.documentDidNavigate(document, to: range)
    }
}
