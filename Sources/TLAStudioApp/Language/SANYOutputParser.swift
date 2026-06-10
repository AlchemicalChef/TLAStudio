import Foundation

// MARK: - Semantic Diagnostic Discriminator

extension TLADiagnostic {
    /// Whether this diagnostic came from SANY semantic analysis
    /// (as opposed to tree-sitter syntax parsing).
    var isSemantic: Bool { code?.hasPrefix("SANY") == true }
}

// MARK: - SANY Output Parser

/// Parses `tla2sany.SANY` output into `TLADiagnostic`s for one document.
///
/// Format pinned against the bundled tla2tools.jar (SANY2 Version 2.2). Everything
/// is written to stdout; stderr is parsed too as a safety net. Representative output:
///
/// ```
/// ****** SANY2 Version 2.2 created 08 July 2020
///
/// Parsing file /path/Bad.tla
/// Semantic processing of module Bad
/// Semantic errors:
///
/// *** Errors: 2
///
/// line 3, col 7 to line 3, col 20 of module Bad
///
/// Unknown operator: `UndefinedThing'.
/// ```
///
/// Structure:
/// - Section headers `*** Errors: N` / `*** Abort messages: N` (→ `.error`) and
///   `*** Warnings: N` (→ `.warning`) introduce entries: one location line
///   (`line L, col C to line L, col C of module M`, `In module M`, or
///   `Unknown location`) followed by message lines.
/// - Parse failures additionally emit a pre-section `***Parse Error***` block that
///   carries the only precise position (`Encountered "tok" at line L, column C`);
///   the later section entry only says `Could not parse module M`, which is
///   suppressed as a duplicate.
/// - Locations are 1-based with inclusive end columns; `TLARange` is 0-based with
///   exclusive ends.
/// - Only diagnostics in the *current* document's module get real ranges; findings
///   in `EXTENDS`'d modules are summarized as a document-level diagnostic on line 0
///   so we never underline the wrong file. The owning file of a parse-error block
///   is inferred from the preceding `Parsing file …` progress line.
/// - Message text can itself contain location phrases mid-sentence ("This
///   duplicates the one at line 3, col 1 …"), so location matches are anchored to
///   the start of the line.
enum SANYOutputParser {

    /// `code` value tagged onto every SANY diagnostic; `TLADiagnostic.isSemantic`
    /// keys off this prefix.
    static let diagnosticCode = "SANY"

    // MARK: Section / location grammar

    private enum Section {
        case errors
        case aborts
        case warnings

        var severity: TLADiagnosticSeverity {
            switch self {
            case .errors, .aborts: return .error
            case .warnings: return .warning
            }
        }
    }

    /// A SANY location, in SANY's own coordinates (1-based, inclusive end column).
    private enum EntryLocation {
        case range(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int, module: String)
        case position(line: Int, column: Int, module: String?)
        case module(String)
        case unknown
    }

    private static let sectionRegex = regex(#"^\*\*\* (Errors|Abort messages|Warnings): \d+"#)
    private static let rangeLocationRegex = regex(
        #"^line (\d+), col(?:umn)? (\d+) to line (\d+), col(?:umn)? (\d+) of module ([A-Za-z0-9_]+)\.?$"#
    )
    private static let positionLocationRegex = regex(
        #"^line (\d+), col(?:umn)? (\d+)(?: of module ([A-Za-z0-9_]+))?\.?$"#
    )
    private static let inModuleLocationRegex = regex(#"^In module ([A-Za-z0-9_]+)\.?$"#)
    private static let unknownLocationRegex = regex(#"^Unknown location\.?$"#)
    private static let encounteredRegex = regex(#"Encountered "(.+?)" at line (\d+), column (\d+)"#)
    private static let atPositionRegex = regex(#"at line (\d+), column (\d+)"#)
    private static let parsedFileModuleRegex = regex(#"([A-Za-z0-9_]+)\.tla\b"#)
    private static let couldNotParseRegex = regex(#"^Could not parse module ([A-Za-z0-9_]+)"#)

    /// Progress/banner lines that carry no diagnostic content. A match also
    /// terminates any in-progress entry (they only appear between entries).
    private static let noisePrefixes = [
        "****** SANY2",
        "Semantic processing of module ",
        "Semantic errors",
        "Linting of module ",
        "Fatal errors while parsing",
        "Residual stack trace follows:"
    ]

    // MARK: Parsing

    /// Parse complete SANY output into diagnostics for the document whose module
    /// is `moduleName`.
    static func parse(stdout: String, stderr: String = "", moduleName: String) -> [TLADiagnostic] {
        var diagnostics: [TLADiagnostic] = []

        var section: Section?
        var pendingLocation: EntryLocation?
        var messageLines: [String] = []

        var inParseErrorBlock = false
        var parseErrorLines: [String] = []

        /// Module owning the most recently announced `Parsing file …`, used to
        /// attribute a following `***Parse Error***` block to the right file.
        var lastParsedModule: String?
        /// Modules for which a parse-error block was already emitted, so the
        /// redundant `Could not parse module M` section entry can be dropped.
        var parseErrorModules: Set<String> = []

        func flushEntry() {
            defer {
                pendingLocation = nil
                messageLines = []
            }
            guard let location = pendingLocation, let section else { return }
            let message = messageLines.joined(separator: " ")
                .trimmingCharacters(in: .whitespaces)
            guard !message.isEmpty else { return }

            if let match = firstMatch(couldNotParseRegex, in: message),
               parseErrorModules.contains(capture(match, 1, in: message)) {
                return
            }

            diagnostics.append(makeDiagnostic(
                location: location,
                message: message,
                severity: section.severity,
                moduleName: moduleName
            ))
        }

        func flushParseErrorBlock() {
            guard inParseErrorBlock else { return }
            inParseErrorBlock = false
            defer { parseErrorLines = [] }

            let message = parseErrorLines.joined(separator: " ")
                .trimmingCharacters(in: .whitespaces)
            guard !message.isEmpty else { return }

            // No module name appears inside the block itself; the preceding
            // `Parsing file` line names the file being parsed when it failed.
            let module = lastParsedModule ?? moduleName
            parseErrorModules.insert(module)

            var location = EntryLocation.module(module)
            for line in parseErrorLines {
                if let match = firstMatch(encounteredRegex, in: line) {
                    let token = capture(match, 1, in: line)
                    let lineNumber = Int(capture(match, 2, in: line)) ?? 1
                    let column = Int(capture(match, 3, in: line)) ?? 1
                    location = .range(
                        startLine: lineNumber,
                        startColumn: column,
                        endLine: lineNumber,
                        endColumn: column + max(0, token.count - 1),
                        module: module
                    )
                    break
                }
                if let match = firstMatch(atPositionRegex, in: line) {
                    let lineNumber = Int(capture(match, 1, in: line)) ?? 1
                    let column = Int(capture(match, 2, in: line)) ?? 1
                    location = .position(line: lineNumber, column: column, module: module)
                    break
                }
            }

            diagnostics.append(makeDiagnostic(
                location: location,
                message: message,
                severity: .error,
                moduleName: moduleName
            ))
        }

        let combined = stderr.isEmpty ? stdout : stdout + "\n" + stderr
        for rawLine in combined.components(separatedBy: "\n") {
            let line = rawLine.trimmingCharacters(in: .whitespacesAndNewlines)

            if inParseErrorBlock {
                // The block's message ends at the first blank line (the residual
                // stack trace that follows is parser-internal noise).
                if line.isEmpty || line == "Residual stack trace follows:" {
                    flushParseErrorBlock()
                } else {
                    parseErrorLines.append(line)
                }
                continue
            }

            if line == "***Parse Error***" {
                flushEntry()
                inParseErrorBlock = true
                continue
            }

            if line.hasPrefix("Parsing file ") {
                if let match = firstMatch(parsedFileModuleRegex, in: line) {
                    lastParsedModule = capture(match, 1, in: line)
                }
                flushEntry()
                continue
            }

            if let match = firstMatch(sectionRegex, in: line) {
                flushEntry()
                switch capture(match, 1, in: line) {
                case "Errors": section = .errors
                case "Abort messages": section = .aborts
                default: section = .warnings
                }
                continue
            }

            if noisePrefixes.contains(where: { line.hasPrefix($0) }) {
                flushEntry()
                continue
            }

            // Pre-section text (the "Fatal errors…" preamble repeats the same
            // entries that follow inside `*** Errors:`) is intentionally skipped.
            guard section != nil else { continue }

            if line.isEmpty { continue }

            if let location = entryLocation(in: line) {
                flushEntry()
                pendingLocation = location
                continue
            }

            if pendingLocation != nil {
                messageLines.append(line)
            }
        }

        flushParseErrorBlock()
        flushEntry()

        // Aborts can be reported under more than one section header; drop exact
        // repeats (TLADiagnostic equality ignores `id`).
        var unique: [TLADiagnostic] = []
        for diagnostic in diagnostics where !unique.contains(diagnostic) {
            unique.append(diagnostic)
        }
        return unique
    }

    // MARK: Location handling

    private static func entryLocation(in line: String) -> EntryLocation? {
        if let match = firstMatch(rangeLocationRegex, in: line) {
            return .range(
                startLine: Int(capture(match, 1, in: line)) ?? 1,
                startColumn: Int(capture(match, 2, in: line)) ?? 1,
                endLine: Int(capture(match, 3, in: line)) ?? 1,
                endColumn: Int(capture(match, 4, in: line)) ?? 1,
                module: capture(match, 5, in: line)
            )
        }
        if let match = firstMatch(inModuleLocationRegex, in: line) {
            return .module(capture(match, 1, in: line))
        }
        if firstMatch(unknownLocationRegex, in: line) != nil {
            return .unknown
        }
        if let match = firstMatch(positionLocationRegex, in: line) {
            let module = match.range(at: 3).location == NSNotFound
                ? nil
                : capture(match, 3, in: line)
            return .position(
                line: Int(capture(match, 1, in: line)) ?? 1,
                column: Int(capture(match, 2, in: line)) ?? 1,
                module: module
            )
        }
        return nil
    }

    private static func makeDiagnostic(
        location: EntryLocation,
        message: String,
        severity: TLADiagnosticSeverity,
        moduleName: String
    ) -> TLADiagnostic {
        func documentLevel(_ message: String) -> TLADiagnostic {
            TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 0)
                ),
                severity: severity,
                message: message,
                code: diagnosticCode
            )
        }

        // SANY coordinates are 1-based Ints; TLAPosition is 0-based UInt32.
        func position(line: Int, column: Int) -> TLAPosition {
            TLAPosition(line: UInt32(max(0, line)), column: UInt32(max(0, column)))
        }

        switch location {
        case .range(let startLine, let startColumn, let endLine, let endColumn, let module):
            guard module == moduleName else {
                return documentLevel("In module \(module): \(message)")
            }
            return TLADiagnostic(
                range: TLARange(
                    start: position(line: startLine - 1, column: startColumn - 1),
                    end: position(line: endLine - 1, column: endColumn)
                ),
                severity: severity,
                message: message,
                code: diagnosticCode
            )

        case .position(let line, let column, let module):
            // A bare position (no module) can only refer to the file SANY was
            // invoked on — the current document.
            let effectiveModule = module ?? moduleName
            guard effectiveModule == moduleName else {
                return documentLevel("In module \(effectiveModule): \(message)")
            }
            return TLADiagnostic(
                range: TLARange(
                    start: position(line: line - 1, column: column - 1),
                    end: position(line: line - 1, column: column)
                ),
                severity: severity,
                message: message,
                code: diagnosticCode
            )

        case .module(let module):
            guard module == moduleName else {
                return documentLevel("In module \(module): \(message)")
            }
            return documentLevel(message)

        case .unknown:
            return documentLevel(message)
        }
    }

    // MARK: Regex helpers

    private static func regex(_ pattern: String) -> NSRegularExpression {
        // Patterns are compile-time constants; a failure is a programmer error.
        try! NSRegularExpression(pattern: pattern)
    }

    private static func firstMatch(_ regex: NSRegularExpression, in line: String) -> NSTextCheckingResult? {
        regex.firstMatch(in: line, range: NSRange(line.startIndex..., in: line))
    }

    private static func capture(_ match: NSTextCheckingResult, _ index: Int, in line: String) -> String {
        // `Swift.Range` spelled explicitly: the UniFFI-generated `Range` type shadows it.
        guard let range = Swift.Range(match.range(at: index), in: line) else { return "" }
        return String(line[range])
    }
}
