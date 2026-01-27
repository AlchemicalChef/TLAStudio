import Foundation

// Import the generated UniFFI bindings when available
// The tla_coreFFI module provides the C FFI layer
#if canImport(tla_coreFFI)
import tla_coreFFI
#endif

// MARK: - TLACore Types

/// Position in a document (0-indexed)
struct TLAPosition: Equatable, Hashable {
    let line: UInt32
    let column: UInt32
}

/// Range in a document
struct TLARange: Equatable, Hashable {
    let start: TLAPosition
    let end: TLAPosition

    var nsRange: NSRange? {
        nil  // Computed when needed from source text
    }
}

/// Symbol kinds in TLA+
enum TLASymbolKind: Equatable {
    case module
    case `operator`
    case variable
    case constant
    case theorem
    case definition
    case instance
    case assumption
}

/// A symbol in the document
struct TLASymbol: Identifiable, Equatable {
    let id = UUID()
    let name: String
    let kind: TLASymbolKind
    let range: TLARange
    let selectionRange: TLARange?
    let children: [TLASymbol]

    static func == (lhs: TLASymbol, rhs: TLASymbol) -> Bool {
        lhs.name == rhs.name && lhs.kind == rhs.kind && lhs.range == rhs.range
    }
}

/// Diagnostic severity
enum TLADiagnosticSeverity: Equatable {
    case error
    case warning
    case information
    case hint
}

/// A diagnostic message
struct TLADiagnostic: Identifiable, Equatable {
    let id = UUID()
    let range: TLARange
    let severity: TLADiagnosticSeverity
    let message: String
    let code: String?

    static func == (lhs: TLADiagnostic, rhs: TLADiagnostic) -> Bool {
        lhs.range == rhs.range && lhs.severity == rhs.severity && lhs.message == rhs.message
    }
}

/// Syntax highlight token
struct TLAHighlightToken: Equatable {
    let range: TLARange
    let tokenType: String
    let modifiers: [String]
}

/// Completion item kind
enum TLACompletionKind: Equatable {
    case keyword
    case `operator`
    case variable
    case constant
    case module
    case snippet
    case function
    case theorem
    case proofTactic
}

/// A completion suggestion
struct TLACompletionItem: Identifiable, Equatable {
    let id = UUID()
    let label: String
    let kind: TLACompletionKind
    let detail: String?
    let insertText: String?

    static func == (lhs: TLACompletionItem, rhs: TLACompletionItem) -> Bool {
        lhs.label == rhs.label && lhs.kind == rhs.kind
    }
}

/// Context where the cursor is located for completion filtering
enum TLACompletionContext: Equatable {
    case topLevel           // At module level
    case afterExtends       // After EXTENDS keyword
    case afterInstance      // After INSTANCE keyword
    case inExpression       // Inside an expression
    case inProof            // Inside a PROOF block
    case afterSetOperator   // After \in or \subseteq
    case inLetDef           // Inside LET definition area
    case afterWith          // After WITH in INSTANCE
    case unknown
}

/// Detailed completion item with full documentation
struct TLADetailedCompletionItem: Identifiable, Equatable {
    let id = UUID()
    let label: String
    let kind: TLACompletionKind
    let detail: String?
    let documentation: String?
    let insertText: String?
    let filterText: String?
    let sortPriority: UInt32
    let signature: String?

    static func == (lhs: TLADetailedCompletionItem, rhs: TLADetailedCompletionItem) -> Bool {
        lhs.label == rhs.label && lhs.kind == rhs.kind
    }

    /// Icon name (SF Symbol) for this completion kind
    var iconName: String {
        switch kind {
        case .keyword:      return "textformat"
        case .operator:     return "function"
        case .variable:     return "v.square"
        case .constant:     return "c.square"
        case .module:       return "shippingbox"
        case .snippet:      return "doc.text"
        case .function:     return "f.square"
        case .theorem:      return "checkmark.seal"
        case .proofTactic:  return "arrow.right.square"
        }
    }

    /// Icon color for this completion kind
    var iconColor: String {
        switch kind {
        case .keyword:      return "purple"
        case .operator:     return "orange"
        case .variable:     return "blue"
        case .constant:     return "teal"
        case .module:       return "brown"
        case .snippet:      return "gray"
        case .function:     return "green"
        case .theorem:      return "indigo"
        case .proofTactic:  return "pink"
        }
    }
}

/// Signature help information for operator calls
struct TLASignatureHelp: Equatable {
    let signatures: [TLASignatureInfo]
    let activeSignature: UInt32
    let activeParameter: UInt32
}

/// Information about a single signature
struct TLASignatureInfo: Equatable {
    let label: String
    let documentation: String?
    let parameters: [TLAParameterInfo]
}

/// Information about a single parameter
struct TLAParameterInfo: Equatable {
    let label: String
    let documentation: String?
}

/// Result of parsing a document
final class TLAParseResult: @unchecked Sendable {
    let isValid: Bool
    let diagnostics: [TLADiagnostic]
    let source: String

    // Lazy-computed and cached line array to avoid repeated splitting
    private var _lines: [String]?
    private let linesLock = NSLock()

    /// Get cached lines array, computing only once per parse result
    var lines: [String] {
        linesLock.lock()
        defer { linesLock.unlock() }
        if let cached = _lines {
            return cached
        }
        let computed = source.components(separatedBy: "\n")
        _lines = computed
        return computed
    }

    /// Number of lines in the source (cached)
    var lineCount: Int {
        lines.count
    }

    init(isValid: Bool, diagnostics: [TLADiagnostic], source: String) {
        self.isValid = isValid
        self.diagnostics = diagnostics
        self.source = source
    }
}

// MARK: - TLACore Protocol

/// Protocol for TLA+ language services
protocol TLACoreProtocol: Sendable {
    func parse(_ source: String) async throws -> TLAParseResult
    func getSymbols(from result: TLAParseResult) async -> [TLASymbol]
    func getHighlights(from result: TLAParseResult, in range: TLARange) async -> [TLAHighlightToken]
    func getCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLACompletionItem]
    func analyzeContext(from result: TLAParseResult, at position: TLAPosition) async -> TLACompletionContext
    func getDetailedCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLADetailedCompletionItem]
    func getSignatureHelp(from result: TLAParseResult, at position: TLAPosition) async -> TLASignatureHelp?
}

// MARK: - TLACore Error

enum TLACoreError: Error, LocalizedError {
    case parseFailed(String)
    case invalidEncoding
    case internalError(String)

    var errorDescription: String? {
        switch self {
        case .parseFailed(let message):
            return "Parse failed: \(message)"
        case .invalidEncoding:
            return "Invalid encoding"
        case .internalError(let message):
            return "Internal error: \(message)"
        }
    }
}

// MARK: - Parse Result LRU Cache

/// Doubly-linked list node for O(1) LRU cache operations
private final class LRUNode<Key: Hashable, Value> {
    let key: Key
    var value: Value
    var prev: LRUNode?
    var next: LRUNode?

    init(key: Key, value: Value) {
        self.key = key
        self.value = value
    }
}

/// Thread-safe LRU cache for TLAParseResult with O(1) get/set operations using doubly-linked list
private final class ParseResultLRUCache {
    private let capacity: Int
    private var cache: [Int: LRUNode<Int, TLAParseResult>] = [:]
    private let lock = NSLock()

    // Sentinel nodes for doubly-linked list (head = oldest, tail = newest)
    private let head = LRUNode<Int, TLAParseResult>(key: -1, value: TLAParseResult(isValid: false, diagnostics: [], source: ""))
    private let tail = LRUNode<Int, TLAParseResult>(key: -1, value: TLAParseResult(isValid: false, diagnostics: [], source: ""))

    init(capacity: Int) {
        self.capacity = capacity
        head.next = tail
        tail.prev = head
    }

    func get(_ key: Int) -> TLAParseResult? {
        lock.lock()
        defer { lock.unlock() }
        guard let node = cache[key] else { return nil }
        // Move to end (most recently used) - O(1) operation
        moveToTail(node)
        return node.value
    }

    func set(_ key: Int, value: TLAParseResult) {
        lock.lock()
        defer { lock.unlock() }
        if let node = cache[key] {
            // Update existing - O(1)
            node.value = value
            moveToTail(node)
        } else {
            // Evict oldest if at capacity - O(1)
            while cache.count >= capacity {
                if let oldest = head.next, oldest !== tail {
                    removeNode(oldest)
                    cache.removeValue(forKey: oldest.key)
                } else {
                    break
                }
            }

            // Add new node - O(1)
            let node = LRUNode(key: key, value: value)
            cache[key] = node
            addToTail(node)
        }
    }

    func clear() {
        lock.lock()
        defer { lock.unlock() }
        cache.removeAll()
        head.next = tail
        tail.prev = head
    }

    // MARK: - Doubly-Linked List Operations (all O(1), must be called with lock held)

    private func removeNode(_ node: LRUNode<Int, TLAParseResult>) {
        node.prev?.next = node.next
        node.next?.prev = node.prev
        node.prev = nil
        node.next = nil
    }

    private func addToTail(_ node: LRUNode<Int, TLAParseResult>) {
        node.prev = tail.prev
        node.next = tail
        tail.prev?.next = node
        tail.prev = node
    }

    private func moveToTail(_ node: LRUNode<Int, TLAParseResult>) {
        removeNode(node)
        addToTail(node)
    }
}

// MARK: - Generic LRU Cache for ParseResult

/// Thread-safe generic LRU cache with O(1) get/set/eviction operations
/// Used by RustTLACore to cache ParseResult objects with proper LRU eviction
private final class GenericLRUCache<Key: Hashable, Value> {
    private let capacity: Int
    private var cache: [Key: GenericLRUNode<Key, Value>] = [:]
    private let lock = NSLock()

    /// Sentinel node for doubly-linked list (head = most recently used)
    private var head: GenericLRUNode<Key, Value>?
    private var tail: GenericLRUNode<Key, Value>?

    init(capacity: Int) {
        self.capacity = capacity
    }

    /// Get value for key, marking it as most recently used. O(1)
    func get(_ key: Key) -> Value? {
        lock.lock()
        defer { lock.unlock() }
        guard let node = cache[key] else { return nil }
        moveToFront(node)
        return node.value
    }

    /// Set value for key, evicting LRU entry if at capacity. O(1)
    func set(_ key: Key, value: Value) {
        lock.lock()
        defer { lock.unlock() }
        if let node = cache[key] {
            // Update existing
            node.value = value
            moveToFront(node)
        } else {
            // Evict oldest if at capacity
            while cache.count >= capacity {
                removeLRU()
            }

            // Add new node
            let node = GenericLRUNode(key: key, value: value)
            cache[key] = node
            addToFront(node)
        }
    }

    // MARK: - Private List Operations (all O(1), must be called with lock held)

    private func addToFront(_ node: GenericLRUNode<Key, Value>) {
        node.prev = nil
        node.next = head
        head?.prev = node
        head = node
        if tail == nil {
            tail = node
        }
    }

    private func removeNode(_ node: GenericLRUNode<Key, Value>) {
        if node === head {
            head = node.next
        }
        if node === tail {
            tail = node.prev
        }
        node.prev?.next = node.next
        node.next?.prev = node.prev
        node.prev = nil
        node.next = nil
    }

    private func moveToFront(_ node: GenericLRUNode<Key, Value>) {
        guard node !== head else { return }
        removeNode(node)
        addToFront(node)
    }

    private func removeLRU() {
        guard let lru = tail else { return }
        cache.removeValue(forKey: lru.key)
        removeNode(lru)
    }
}

/// Node for GenericLRUCache
private final class GenericLRUNode<Key: Hashable, Value> {
    let key: Key
    var value: Value
    var prev: GenericLRUNode?
    var next: GenericLRUNode?

    init(key: Key, value: Value) {
        self.key = key
        self.value = value
    }
}

// MARK: - TLACore Wrapper (Main Interface)

/// Thread-safe wrapper for TLA+ language services
@MainActor
final class TLACoreWrapper: ObservableObject {
    static let shared = TLACoreWrapper()

    private let core: any TLACoreProtocol

    /// LRU cache for parse results - uses content hash as key to avoid storing large strings
    private var parseCache: ParseResultLRUCache

    private init() {
        // Use the factory to get the best available implementation
        // This will try Rust tree-sitter first, then fall back to regex
        self.core = TLACoreFactory.create()
        self.parseCache = ParseResultLRUCache(capacity: 10)
    }

    /// Parse TLA+ source code
    func parse(_ content: String) async throws -> TLAParseResult {
        // Use content hash as cache key to avoid storing large strings
        let contentHash = content.hashValue

        // Check cache
        if let cached = parseCache.get(contentHash) {
            // Verify the cached result matches (hash collision check)
            if cached.source == content {
                return cached
            }
        }

        let result = try await core.parse(content)

        // Cache result with LRU eviction
        parseCache.set(contentHash, value: result)

        return result
    }

    /// Get symbols from parse result
    func getSymbols(from result: TLAParseResult) async -> [TLASymbol] {
        await core.getSymbols(from: result)
    }

    /// Get syntax highlights for a range
    func getHighlights(from result: TLAParseResult, in range: TLARange) async -> [TLAHighlightToken] {
        await core.getHighlights(from: result, in: range)
    }

    /// Get all highlights for a document
    func getAllHighlights(from result: TLAParseResult) async -> [TLAHighlightToken] {
        let lineArray = result.lines
        let endLine = UInt32(max(0, lineArray.count - 1))
        let endColumn = UInt32(lineArray.last?.count ?? 0)

        let fullRange = TLARange(
            start: TLAPosition(line: 0, column: 0),
            end: TLAPosition(line: endLine, column: endColumn)
        )

        return await core.getHighlights(from: result, in: fullRange)
    }

    /// Get completions at a position
    func getCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLACompletionItem] {
        await core.getCompletions(from: result, at: position)
    }

    /// Analyze the completion context at a position
    func analyzeContext(from result: TLAParseResult, at position: TLAPosition) async -> TLACompletionContext {
        await core.analyzeContext(from: result, at: position)
    }

    /// Get detailed completions with documentation and sorting
    func getDetailedCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLADetailedCompletionItem] {
        await core.getDetailedCompletions(from: result, at: position)
    }

    /// Get signature help for an operator call
    func getSignatureHelp(from result: TLAParseResult, at position: TLAPosition) async -> TLASignatureHelp? {
        await core.getSignatureHelp(from: result, at: position)
    }

    /// Clear parse cache
    func clearCache() {
        parseCache.clear()
    }

    /// Find definition location for a symbol name
    /// Returns the range where the symbol is defined, or nil if not found
    func findDefinition(named name: String, in symbols: [TLASymbol]) -> TLARange? {
        // Search through symbols recursively
        func searchSymbols(_ symbols: [TLASymbol]) -> TLARange? {
            for symbol in symbols {
                if symbol.name == name {
                    return symbol.selectionRange ?? symbol.range
                }
                // Search children
                if let found = searchSymbols(symbol.children) {
                    return found
                }
            }
            return nil
        }
        return searchSymbols(symbols)
    }

    /// Get the word at a given position in the source text
    func wordAt(position: TLAPosition, in source: String) -> String? {
        let lines = source.components(separatedBy: "\n")
        guard Int(position.line) < lines.count else { return nil }

        let line = lines[Int(position.line)]
        let column = Int(position.column)
        guard column <= line.count else { return nil }

        // Find word boundaries
        let lineChars = Array(line)
        var start = column
        var end = column

        // Move start backwards to find word start
        while start > 0 && isIdentifierChar(lineChars[start - 1]) {
            start -= 1
        }

        // Move end forwards to find word end
        while end < lineChars.count && isIdentifierChar(lineChars[end]) {
            end += 1
        }

        guard start < end else { return nil }

        let word = String(lineChars[start..<end])
        return word.isEmpty ? nil : word
    }

    private func isIdentifierChar(_ char: Character) -> Bool {
        char.isLetter || char.isNumber || char == "_"
    }

    /// Get completions for current context
    func getContextCompletions(at offset: Int, in source: String, symbols: [TLASymbol]) -> [String] {
        // Get the partial word being typed
        let prefix = getPartialWord(at: offset, in: source)

        var completions: [String] = []

        // Add matching keywords
        let keywords = [
            "EXTENDS", "INSTANCE", "LOCAL", "WITH",
            "VARIABLE", "VARIABLES", "CONSTANT", "CONSTANTS",
            "ASSUME", "ASSUMPTION", "AXIOM", "THEOREM", "LEMMA",
            "PROOF", "BY", "DEF", "DEFS", "OBVIOUS", "OMITTED", "QED",
            "PICK", "HAVE", "TAKE", "WITNESS", "SUFFICES", "USE", "HIDE", "DEFINE",
            "NEW", "STATE", "ACTION", "TEMPORAL",
            "IF", "THEN", "ELSE", "CASE", "OTHER", "LET", "IN",
            "CHOOSE", "EXCEPT", "DOMAIN", "SUBSET", "UNION",
            "ENABLED", "UNCHANGED",
            "TRUE", "FALSE", "BOOLEAN"
        ]

        // Add standard modules
        let standardModules = [
            "Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags", "TLC", "TLAPS"
        ]

        // Add common standard library functions
        let standardFunctions = [
            "Nat", "Int", "Seq", "Len", "Head", "Tail", "Append", "SubSeq",
            "IsFiniteSet", "Cardinality", "Print", "Assert"
        ]

        // Filter by prefix
        let lowerPrefix = prefix.lowercased()

        for kw in keywords {
            if kw.lowercased().hasPrefix(lowerPrefix) {
                completions.append(kw)
            }
        }

        for mod in standardModules {
            if mod.lowercased().hasPrefix(lowerPrefix) {
                completions.append(mod)
            }
        }

        for fn in standardFunctions {
            if fn.lowercased().hasPrefix(lowerPrefix) {
                completions.append(fn)
            }
        }

        // Add matching user-defined symbols
        func addSymbols(_ syms: [TLASymbol]) {
            for symbol in syms {
                if symbol.name.lowercased().hasPrefix(lowerPrefix) {
                    completions.append(symbol.name)
                }
                addSymbols(symbol.children)
            }
        }
        addSymbols(symbols)

        // Remove duplicates and sort
        return Array(Set(completions)).sorted()
    }

    private func getPartialWord(at offset: Int, in source: String) -> String {
        guard offset > 0 else { return "" }

        let chars = Array(source)
        var start = offset - 1

        // Move backwards to find start of word
        while start >= 0 && isIdentifierChar(chars[start]) {
            start -= 1
        }

        start += 1
        guard start < offset else { return "" }

        return String(chars[start..<offset])
    }

    /// Get hover documentation for a word at a position
    func getHoverDocumentation(at position: TLAPosition, in source: String, symbols: [TLASymbol]) -> HoverInfo? {
        guard let word = wordAt(position: position, in: source) else {
            return nil
        }

        // Check built-in documentation first
        if let builtin = TLADocumentation.builtins[word] {
            return HoverInfo(title: word, description: builtin.description, signature: builtin.signature, kind: .keyword)
        }

        // Check for user-defined symbol
        if let symbol = findSymbolByName(word, in: symbols) {
            return HoverInfo(
                title: symbol.name,
                description: "User-defined \(symbolKindName(symbol.kind))",
                signature: nil,
                kind: hoverKind(from: symbol.kind)
            )
        }

        return nil
    }

    private func findSymbolByName(_ name: String, in symbols: [TLASymbol]) -> TLASymbol? {
        for symbol in symbols {
            if symbol.name == name {
                return symbol
            }
            if let found = findSymbolByName(name, in: symbol.children) {
                return found
            }
        }
        return nil
    }

    private func symbolKindName(_ kind: TLASymbolKind) -> String {
        switch kind {
        case .module: return "module"
        case .operator: return "operator"
        case .variable: return "variable"
        case .constant: return "constant"
        case .theorem: return "theorem"
        case .definition: return "definition"
        case .instance: return "instance"
        case .assumption: return "assumption"
        }
    }

    private func hoverKind(from symbolKind: TLASymbolKind) -> HoverInfo.Kind {
        switch symbolKind {
        case .module: return .module
        case .operator: return .operator
        case .variable: return .variable
        case .constant: return .constant
        case .theorem: return .theorem
        case .definition: return .definition
        case .instance: return .module
        case .assumption: return .keyword
        }
    }
}

// MARK: - Hover Info

struct HoverInfo {
    enum Kind {
        case keyword, `operator`, variable, constant, module, theorem, definition
    }

    let title: String
    let description: String
    let signature: String?
    let kind: Kind
}

// MARK: - TLA+ Documentation

enum TLADocumentation {
    struct Entry {
        let description: String
        let signature: String?
    }

    static let builtins: [String: Entry] = [
        // Keywords
        "EXTENDS": Entry(description: "Import definitions from other modules", signature: "EXTENDS Module1, Module2, ..."),
        "INSTANCE": Entry(description: "Create an instance of a module with substitutions", signature: "INSTANCE Module WITH param1 <- expr1, ..."),
        "LOCAL": Entry(description: "Mark a definition as local (not exported)", signature: "LOCAL Op == ..."),
        "VARIABLE": Entry(description: "Declare state variables", signature: "VARIABLE var1, var2, ..."),
        "VARIABLES": Entry(description: "Declare state variables", signature: "VARIABLES var1, var2, ..."),
        "CONSTANT": Entry(description: "Declare constants (parameters)", signature: "CONSTANT const1, const2, ..."),
        "CONSTANTS": Entry(description: "Declare constants (parameters)", signature: "CONSTANTS const1, const2, ..."),
        "ASSUME": Entry(description: "State an assumption about constants", signature: "ASSUME expression"),
        "ASSUMPTION": Entry(description: "State a named assumption", signature: "ASSUMPTION Name == expression"),
        "THEOREM": Entry(description: "State a theorem to be proved", signature: "THEOREM Name == expression"),
        "LEMMA": Entry(description: "State a lemma (minor theorem)", signature: "LEMMA Name == expression"),
        "PROOF": Entry(description: "Begin a proof block", signature: "PROOF ..."),
        "BY": Entry(description: "Proof step using facts/definitions", signature: "BY fact1, fact2 DEF def1, def2"),
        "OBVIOUS": Entry(description: "Trivially true proof step", signature: "OBVIOUS"),
        "OMITTED": Entry(description: "Proof omitted (to be filled later)", signature: "OMITTED"),
        "QED": Entry(description: "End of proof", signature: "QED"),

        // Control flow
        "IF": Entry(description: "Conditional expression", signature: "IF condition THEN expr1 ELSE expr2"),
        "THEN": Entry(description: "Then branch of conditional", signature: nil),
        "ELSE": Entry(description: "Else branch of conditional", signature: nil),
        "CASE": Entry(description: "Case expression", signature: "CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3"),
        "OTHER": Entry(description: "Default case in CASE expression", signature: nil),
        "LET": Entry(description: "Local definitions", signature: "LET x == expr1 IN expr2"),
        "IN": Entry(description: "Body of LET expression", signature: nil),

        // Operators
        "CHOOSE": Entry(description: "Hilbert's choice operator - pick an arbitrary element satisfying predicate", signature: "CHOOSE x \\in S : P(x)"),
        "EXCEPT": Entry(description: "Function/record update", signature: "[f EXCEPT ![a] = b]"),
        "DOMAIN": Entry(description: "Domain of a function", signature: "DOMAIN f"),
        "SUBSET": Entry(description: "Power set (set of all subsets)", signature: "SUBSET S"),
        "UNION": Entry(description: "Generalized union of a set of sets", signature: "UNION S"),
        "ENABLED": Entry(description: "True if action is enabled in current state", signature: "ENABLED Action"),
        "UNCHANGED": Entry(description: "Variables unchanged in this step", signature: "UNCHANGED <<var1, var2>>"),

        // Boolean
        "TRUE": Entry(description: "Boolean true", signature: nil),
        "FALSE": Entry(description: "Boolean false", signature: nil),
        "BOOLEAN": Entry(description: "The set {TRUE, FALSE}", signature: nil),

        // Temporal
        "WF_": Entry(description: "Weak fairness - if continuously enabled, eventually taken", signature: "WF_vars(Action)"),
        "SF_": Entry(description: "Strong fairness - if infinitely often enabled, eventually taken", signature: "SF_vars(Action)"),

        // Set operators (backslash notation)
        "\\in": Entry(description: "Set membership", signature: "x \\in S"),
        "\\notin": Entry(description: "Not a member of set", signature: "x \\notin S"),
        "\\subseteq": Entry(description: "Subset or equal", signature: "A \\subseteq B"),
        "\\subset": Entry(description: "Proper subset", signature: "A \\subset B"),
        "\\cup": Entry(description: "Set union", signature: "A \\cup B"),
        "\\cap": Entry(description: "Set intersection", signature: "A \\cap B"),
        "\\union": Entry(description: "Set union (alias)", signature: "A \\union B"),
        "\\intersect": Entry(description: "Set intersection (alias)", signature: "A \\intersect B"),
        "\\X": Entry(description: "Cartesian product", signature: "A \\X B"),
        "\\times": Entry(description: "Cartesian product (alias)", signature: "A \\times B"),

        // Quantifiers
        "\\E": Entry(description: "Existential quantifier", signature: "\\E x \\in S : P(x)"),
        "\\A": Entry(description: "Universal quantifier", signature: "\\A x \\in S : P(x)"),
        "\\EE": Entry(description: "Temporal existential quantifier", signature: "\\EE x : F"),
        "\\AA": Entry(description: "Temporal universal quantifier", signature: "\\AA x : F"),

        // Logic
        "\\lnot": Entry(description: "Logical negation", signature: "\\lnot P"),
        "\\neg": Entry(description: "Logical negation (alias)", signature: "\\neg P"),
        "\\lor": Entry(description: "Logical disjunction (OR)", signature: "P \\lor Q"),
        "\\land": Entry(description: "Logical conjunction (AND)", signature: "P \\land Q"),
        "\\implies": Entry(description: "Logical implication", signature: "P \\implies Q"),
        "\\equiv": Entry(description: "Logical equivalence", signature: "P \\equiv Q"),

        // Standard modules
        "Naturals": Entry(description: "Natural numbers module - defines Nat, +, -, *, \\div, %, <, >, <=, >=", signature: "EXTENDS Naturals"),
        "Integers": Entry(description: "Integers module - extends Naturals with negative integers", signature: "EXTENDS Integers"),
        "Reals": Entry(description: "Real numbers module", signature: "EXTENDS Reals"),
        "Sequences": Entry(description: "Sequence operations - Seq, Len, Head, Tail, Append, \\o, SubSeq", signature: "EXTENDS Sequences"),
        "FiniteSets": Entry(description: "Finite set operations - IsFiniteSet, Cardinality", signature: "EXTENDS FiniteSets"),
        "Bags": Entry(description: "Bag (multiset) operations", signature: "EXTENDS Bags"),
        "TLC": Entry(description: "TLC model checker utilities - Print, Assert, @@, :>, etc.", signature: "EXTENDS TLC"),

        // Common from Naturals
        "Nat": Entry(description: "The set of natural numbers {0, 1, 2, ...}", signature: nil),
        "Int": Entry(description: "The set of integers {..., -2, -1, 0, 1, 2, ...}", signature: nil),

        // Common from Sequences
        "Seq": Entry(description: "Set of all sequences over S", signature: "Seq(S)"),
        "Len": Entry(description: "Length of a sequence", signature: "Len(seq)"),
        "Head": Entry(description: "First element of a sequence", signature: "Head(seq)"),
        "Tail": Entry(description: "All but the first element", signature: "Tail(seq)"),
        "Append": Entry(description: "Append element to sequence", signature: "Append(seq, elem)"),
        "SubSeq": Entry(description: "Subsequence from index m to n", signature: "SubSeq(seq, m, n)"),

        // Common from FiniteSets
        "IsFiniteSet": Entry(description: "True if set is finite", signature: "IsFiniteSet(S)"),
        "Cardinality": Entry(description: "Number of elements in finite set", signature: "Cardinality(S)"),
    ]
}

// MARK: - Fallback Implementation

/// Fallback TLA+ parser using regex-based highlighting
/// Used when Rust TLACore is not available
final class FallbackTLACore: TLACoreProtocol, @unchecked Sendable {

    func parse(_ source: String) async throws -> TLAParseResult {
        // Simple validation - check for module structure
        let hasModuleHeader = source.contains("---- MODULE") || source.contains("---- MODULE")
        let hasModuleFooter = source.contains("====")

        var diagnostics: [TLADiagnostic] = []

        if !hasModuleHeader && !source.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
            diagnostics.append(TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 0)
                ),
                severity: .warning,
                message: "Missing module header",
                code: "W001"
            ))
        }

        if hasModuleHeader && !hasModuleFooter {
            diagnostics.append(TLADiagnostic(
                range: TLARange(
                    start: TLAPosition(line: 0, column: 0),
                    end: TLAPosition(line: 0, column: 0)
                ),
                severity: .warning,
                message: "Missing module footer (====)",
                code: "W002"
            ))
        }

        return TLAParseResult(
            isValid: diagnostics.filter { $0.severity == .error }.isEmpty,
            diagnostics: diagnostics,
            source: source
        )
    }

    func getSymbols(from result: TLAParseResult) async -> [TLASymbol] {
        var symbols: [TLASymbol] = []
        let lines = result.lines

        // Extract module name
        let modulePattern = #"----+\s+MODULE\s+(\w+)\s+----+"#
        if let moduleMatch = result.source.range(of: modulePattern, options: .regularExpression) {
            let moduleLine = String(result.source[moduleMatch])
            if let nameMatch = moduleLine.range(of: #"\w+"#, options: .regularExpression, range: moduleLine.range(of: "MODULE")!.upperBound..<moduleLine.endIndex) {
                let name = String(moduleLine[nameMatch])
                symbols.append(TLASymbol(
                    name: name,
                    kind: .module,
                    range: TLARange(start: TLAPosition(line: 0, column: 0), end: TLAPosition(line: 0, column: UInt32(moduleLine.count))),
                    selectionRange: nil,
                    children: []
                ))
            }
        }

        // Extract operators (definitions)
        let operatorPattern = #"^(\w+)\s*(?:\([^)]*\))?\s*=="#
        for (lineNum, line) in lines.enumerated() {
            if let range = line.range(of: operatorPattern, options: .regularExpression) {
                let match = String(line[range])
                if let nameEnd = match.firstIndex(where: { $0 == " " || $0 == "(" || $0 == "=" }) {
                    let name = String(match[match.startIndex..<nameEnd])
                    if !["IF", "THEN", "ELSE", "LET", "IN", "CASE", "OTHER"].contains(name) {
                        symbols.append(TLASymbol(
                            name: name,
                            kind: .operator,
                            range: TLARange(
                                start: TLAPosition(line: UInt32(lineNum), column: 0),
                                end: TLAPosition(line: UInt32(lineNum), column: UInt32(line.count))
                            ),
                            selectionRange: nil,
                            children: []
                        ))
                    }
                }
            }
        }

        // Extract VARIABLES
        let variablePattern = #"VARIABLES?\s+([^\n]+)"#
        if let varMatch = result.source.range(of: variablePattern, options: .regularExpression) {
            let varDecl = String(result.source[varMatch])
            let afterKeyword = varDecl.replacingOccurrences(of: #"^VARIABLES?\s+"#, with: "", options: .regularExpression)
            let varNames = afterKeyword.components(separatedBy: ",").map { $0.trimmingCharacters(in: .whitespaces) }
            for name in varNames where !name.isEmpty {
                symbols.append(TLASymbol(
                    name: name,
                    kind: .variable,
                    range: TLARange(start: TLAPosition(line: 0, column: 0), end: TLAPosition(line: 0, column: 0)),
                    selectionRange: nil,
                    children: []
                ))
            }
        }

        // Extract CONSTANTS
        let constantPattern = #"CONSTANTS?\s+([^\n]+)"#
        if let constMatch = result.source.range(of: constantPattern, options: .regularExpression) {
            let constDecl = String(result.source[constMatch])
            let afterKeyword = constDecl.replacingOccurrences(of: #"^CONSTANTS?\s+"#, with: "", options: .regularExpression)
            let constNames = afterKeyword.components(separatedBy: ",").map { $0.trimmingCharacters(in: .whitespaces) }
            for name in constNames where !name.isEmpty {
                symbols.append(TLASymbol(
                    name: name,
                    kind: .constant,
                    range: TLARange(start: TLAPosition(line: 0, column: 0), end: TLAPosition(line: 0, column: 0)),
                    selectionRange: nil,
                    children: []
                ))
            }
        }

        return symbols
    }

    func getHighlights(from result: TLAParseResult, in range: TLARange) async -> [TLAHighlightToken] {
        var tokens: [TLAHighlightToken] = []
        let lines = result.lines

        let startLine = Int(range.start.line)
        let endLine = min(Int(range.end.line), lines.count - 1)

        for lineNum in startLine...max(startLine, endLine) {
            guard lineNum < lines.count else { continue }
            let line = lines[lineNum]
            tokens.append(contentsOf: highlightLine(line, lineNumber: UInt32(lineNum)))
        }

        return tokens
    }

    private func highlightLine(_ line: String, lineNumber: UInt32) -> [TLAHighlightToken] {
        var tokens: [TLAHighlightToken] = []

        // Keywords
        let keywords = [
            "EXTENDS", "LOCAL", "INSTANCE", "WITH",
            "VARIABLE", "VARIABLES", "CONSTANT", "CONSTANTS",
            "ASSUME", "ASSUMPTION", "AXIOM", "THEOREM", "LEMMA",
            "PROOF", "BY", "DEF", "DEFS", "OBVIOUS", "OMITTED", "QED",
            "PICK", "HAVE", "TAKE", "WITNESS", "SUFFICES",
            "NEW", "STATE", "ACTION", "TEMPORAL",
            "IF", "THEN", "ELSE", "CASE", "OTHER", "LET", "IN",
            "CHOOSE", "EXCEPT", "DOMAIN", "SUBSET", "UNION",
            "ENABLED", "UNCHANGED", "WF_", "SF_",
            "TRUE", "FALSE"
        ]

        for keyword in keywords {
            var searchRange = line.startIndex..<line.endIndex
            while let range = line.range(of: "\\b\(keyword)\\b", options: .regularExpression, range: searchRange) {
                let startCol = line.distance(from: line.startIndex, to: range.lowerBound)
                let endCol = line.distance(from: line.startIndex, to: range.upperBound)
                tokens.append(TLAHighlightToken(
                    range: TLARange(
                        start: TLAPosition(line: lineNumber, column: UInt32(startCol)),
                        end: TLAPosition(line: lineNumber, column: UInt32(endCol))
                    ),
                    tokenType: "keyword",
                    modifiers: []
                ))
                searchRange = range.upperBound..<line.endIndex
            }
        }

        // Comments (\\* and (* *))
        if let commentStart = line.range(of: "\\\\\\*", options: .regularExpression) {
            let startCol = line.distance(from: line.startIndex, to: commentStart.lowerBound)
            tokens.append(TLAHighlightToken(
                range: TLARange(
                    start: TLAPosition(line: lineNumber, column: UInt32(startCol)),
                    end: TLAPosition(line: lineNumber, column: UInt32(line.count))
                ),
                tokenType: "comment",
                modifiers: []
            ))
        }

        // Strings
        let stringPattern = #""[^"]*""#
        var searchRange = line.startIndex..<line.endIndex
        while let range = line.range(of: stringPattern, options: .regularExpression, range: searchRange) {
            let startCol = line.distance(from: line.startIndex, to: range.lowerBound)
            let endCol = line.distance(from: line.startIndex, to: range.upperBound)
            tokens.append(TLAHighlightToken(
                range: TLARange(
                    start: TLAPosition(line: lineNumber, column: UInt32(startCol)),
                    end: TLAPosition(line: lineNumber, column: UInt32(endCol))
                ),
                tokenType: "string",
                modifiers: []
            ))
            searchRange = range.upperBound..<line.endIndex
        }

        // Numbers
        let numberPattern = #"\b\d+\b"#
        searchRange = line.startIndex..<line.endIndex
        while let range = line.range(of: numberPattern, options: .regularExpression, range: searchRange) {
            let startCol = line.distance(from: line.startIndex, to: range.lowerBound)
            let endCol = line.distance(from: line.startIndex, to: range.upperBound)
            tokens.append(TLAHighlightToken(
                range: TLARange(
                    start: TLAPosition(line: lineNumber, column: UInt32(startCol)),
                    end: TLAPosition(line: lineNumber, column: UInt32(endCol))
                ),
                tokenType: "number",
                modifiers: []
            ))
            searchRange = range.upperBound..<line.endIndex
        }

        // Operators
        let operatorPattern = #"[/\\]{2}|\\in|\\notin|\\subseteq|\\cup|\\cap|=>|<=>|~|#|\\E|\\A|\\X|:=|'|->|<-"#
        searchRange = line.startIndex..<line.endIndex
        while let range = line.range(of: operatorPattern, options: .regularExpression, range: searchRange) {
            let startCol = line.distance(from: line.startIndex, to: range.lowerBound)
            let endCol = line.distance(from: line.startIndex, to: range.upperBound)
            tokens.append(TLAHighlightToken(
                range: TLARange(
                    start: TLAPosition(line: lineNumber, column: UInt32(startCol)),
                    end: TLAPosition(line: lineNumber, column: UInt32(endCol))
                ),
                tokenType: "operator",
                modifiers: []
            ))
            searchRange = range.upperBound..<line.endIndex
        }

        // Module header/footer
        if line.contains("----") && line.contains("MODULE") {
            tokens.append(TLAHighlightToken(
                range: TLARange(
                    start: TLAPosition(line: lineNumber, column: 0),
                    end: TLAPosition(line: lineNumber, column: UInt32(line.count))
                ),
                tokenType: "keyword",
                modifiers: ["declaration"]
            ))
        }
        if line.hasPrefix("====") {
            tokens.append(TLAHighlightToken(
                range: TLARange(
                    start: TLAPosition(line: lineNumber, column: 0),
                    end: TLAPosition(line: lineNumber, column: UInt32(line.count))
                ),
                tokenType: "keyword",
                modifiers: ["declaration"]
            ))
        }

        return tokens
    }

    func getCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLACompletionItem] {
        // Return TLA+ keywords
        let keywords: [(String, String)] = [
            ("CONSTANT", "Declare constants"),
            ("CONSTANTS", "Declare constants"),
            ("VARIABLE", "Declare variables"),
            ("VARIABLES", "Declare variables"),
            ("EXTENDS", "Extend other modules"),
            ("INSTANCE", "Instantiate a module"),
            ("LOCAL", "Local definition"),
            ("THEOREM", "Declare a theorem"),
            ("LEMMA", "Declare a lemma"),
            ("ASSUME", "Make an assumption"),
            ("ASSUMPTION", "Declare an assumption"),
            ("AXIOM", "Declare an axiom"),
            ("PROOF", "Begin a proof"),
            ("BY", "Proof by"),
            ("OBVIOUS", "Obvious proof step"),
            ("OMITTED", "Omitted proof"),
            ("QED", "End of proof"),
            ("IF", "Conditional"),
            ("THEN", "Then branch"),
            ("ELSE", "Else branch"),
            ("CASE", "Case expression"),
            ("OTHER", "Default case"),
            ("LET", "Let binding"),
            ("IN", "In expression"),
            ("CHOOSE", "Choice operator"),
            ("EXCEPT", "Record update"),
            ("DOMAIN", "Domain of function"),
            ("SUBSET", "Powerset"),
            ("UNION", "Union of sets"),
            ("ENABLED", "Action enabled"),
            ("UNCHANGED", "Unchanged variables"),
        ]

        return keywords.map { (label, detail) in
            TLACompletionItem(
                label: label,
                kind: .keyword,
                detail: detail,
                insertText: nil
            )
        }
    }

    func analyzeContext(from result: TLAParseResult, at position: TLAPosition) async -> TLACompletionContext {
        // Simple context analysis based on line content
        let lines = result.lines
        let lineNum = Int(position.line)
        guard lineNum < lines.count else { return .unknown }

        let line = lines[lineNum]
        let trimmed = line.trimmingCharacters(in: .whitespaces)

        if trimmed.starts(with: "EXTENDS") {
            return .afterExtends
        }
        if trimmed.starts(with: "INSTANCE") {
            if line.contains(" WITH ") {
                return .afterWith
            }
            return .afterInstance
        }
        if trimmed.starts(with: "PROOF") || trimmed.starts(with: "BY") ||
           trimmed.starts(with: "QED") || trimmed.starts(with: "OBVIOUS") {
            return .inProof
        }
        if trimmed.isEmpty {
            return .topLevel
        }
        return .inExpression
    }

    func getDetailedCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLADetailedCompletionItem] {
        // Return basic keyword completions with documentation
        let keywords: [(String, String, String)] = [
            ("EXTENDS", "Import definitions from other modules", "EXTENDS Module1, Module2"),
            ("INSTANCE", "Create parameterized module instance", "INSTANCE Module WITH param <- value"),
            ("CONSTANT", "Declare module constants", "CONSTANT const1, const2"),
            ("VARIABLE", "Declare state variables", "VARIABLE var1, var2"),
            ("THEOREM", "Declare a theorem to be proved", "THEOREM Name == expression"),
            ("IF", "Conditional expression", "IF cond THEN e1 ELSE e2"),
            ("LET", "Local definitions", "LET x == e1 IN e2"),
            ("CHOOSE", "Hilbert's choice operator", "CHOOSE x \\in S : P(x)"),
        ]

        return keywords.enumerated().map { (idx, kw) in
            TLADetailedCompletionItem(
                label: kw.0,
                kind: .keyword,
                detail: nil,
                documentation: kw.1,
                insertText: nil,
                filterText: nil,
                sortPriority: UInt32(idx),
                signature: kw.2
            )
        }
    }

    func getSignatureHelp(from result: TLAParseResult, at position: TLAPosition) async -> TLASignatureHelp? {
        // Fallback doesn't implement signature help
        return nil
    }
}

// MARK: - Rust TLACore Implementation

/// TLA+ parser using the Rust tree-sitter implementation via UniFFI
/// This provides accurate, incremental parsing with the tree-sitter-tlaplus grammar
final class RustTLACore: TLACoreProtocol, @unchecked Sendable {
    private let core: TlaCore
    /// LRU cache for ParseResults with proper O(1) eviction
    /// Note: GenericLRUCache is thread-safe with internal NSLock
    private let parseResultCache = GenericLRUCache<ObjectIdentifier, ParseResult>(capacity: 20)

    init() throws {
        self.core = try TlaCore()
    }

    func parse(_ source: String) async throws -> TLAParseResult {
        do {
            let result = try core.parse(source: source)
            let diagnostics = result.getDiagnostics().map { convertDiagnostic($0) }

            let tlaResult = TLAParseResult(
                isValid: result.isValid(),
                diagnostics: diagnostics,
                source: source
            )

            // Cache the ParseResult for later use with getSymbols/getHighlights
            // GenericLRUCache is already thread-safe with its own lock
            let key = ObjectIdentifier(tlaResult)
            parseResultCache.set(key, value: result)

            return tlaResult
        } catch let error as ParseError {
            throw TLACoreError.parseFailed(error.localizedDescription)
        }
    }

    func getSymbols(from result: TLAParseResult) async -> [TLASymbol] {
        guard let parseResult = getCachedParseResult(for: result) else {
            // Re-parse if cache miss
            guard let newResult = try? core.parse(source: result.source) else {
                return []
            }
            return core.getSymbols(result: newResult).map { convertSymbol($0) }
        }
        return core.getSymbols(result: parseResult).map { convertSymbol($0) }
    }

    func getHighlights(from result: TLAParseResult, in range: TLARange) async -> [TLAHighlightToken] {
        guard let parseResult = getCachedParseResult(for: result) else {
            // Re-parse if cache miss
            guard let newResult = try? core.parse(source: result.source) else {
                return []
            }
            let rustRange = Range(
                start: Position(line: range.start.line, column: range.start.column),
                end: Position(line: range.end.line, column: range.end.column)
            )
            return core.getHighlights(result: newResult, range: rustRange).map { convertHighlightToken($0) }
        }

        let rustRange = Range(
            start: Position(line: range.start.line, column: range.start.column),
            end: Position(line: range.end.line, column: range.end.column)
        )
        return core.getHighlights(result: parseResult, range: rustRange).map { convertHighlightToken($0) }
    }

    func getCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLACompletionItem] {
        guard let parseResult = getCachedParseResult(for: result) else {
            // Re-parse if cache miss
            guard let newResult = try? core.parse(source: result.source) else {
                return []
            }
            let rustPosition = Position(line: position.line, column: position.column)
            return core.getCompletions(result: newResult, position: rustPosition).map { convertCompletionItem($0) }
        }

        let rustPosition = Position(line: position.line, column: position.column)
        return core.getCompletions(result: parseResult, position: rustPosition).map { convertCompletionItem($0) }
    }

    func analyzeContext(from result: TLAParseResult, at position: TLAPosition) async -> TLACompletionContext {
        guard let parseResult = getCachedParseResult(for: result) else {
            guard let newResult = try? core.parse(source: result.source) else {
                return .unknown
            }
            let rustPosition = Position(line: position.line, column: position.column)
            return convertCompletionContext(core.analyzeContext(result: newResult, position: rustPosition))
        }

        let rustPosition = Position(line: position.line, column: position.column)
        return convertCompletionContext(core.analyzeContext(result: parseResult, position: rustPosition))
    }

    func getDetailedCompletions(from result: TLAParseResult, at position: TLAPosition) async -> [TLADetailedCompletionItem] {
        guard let parseResult = getCachedParseResult(for: result) else {
            guard let newResult = try? core.parse(source: result.source) else {
                return []
            }
            let rustPosition = Position(line: position.line, column: position.column)
            return core.getDetailedCompletions(result: newResult, position: rustPosition).map { convertDetailedCompletionItem($0) }
        }

        let rustPosition = Position(line: position.line, column: position.column)
        return core.getDetailedCompletions(result: parseResult, position: rustPosition).map { convertDetailedCompletionItem($0) }
    }

    func getSignatureHelp(from result: TLAParseResult, at position: TLAPosition) async -> TLASignatureHelp? {
        guard let parseResult = getCachedParseResult(for: result) else {
            guard let newResult = try? core.parse(source: result.source) else {
                return nil
            }
            let rustPosition = Position(line: position.line, column: position.column)
            return core.getSignatureHelp(result: newResult, position: rustPosition).map { convertSignatureHelp($0) }
        }

        let rustPosition = Position(line: position.line, column: position.column)
        return core.getSignatureHelp(result: parseResult, position: rustPosition).map { convertSignatureHelp($0) }
    }

    // MARK: - Private Helpers

    private func getCachedParseResult(for tlaResult: TLAParseResult) -> ParseResult? {
        let key = ObjectIdentifier(tlaResult)
        // GenericLRUCache is already thread-safe with its own lock
        return parseResultCache.get(key)
    }

    private func convertDiagnostic(_ d: Diagnostic) -> TLADiagnostic {
        TLADiagnostic(
            range: convertRange(d.range),
            severity: convertSeverity(d.severity),
            message: d.message,
            code: d.code
        )
    }

    private func convertSymbol(_ s: Symbol) -> TLASymbol {
        TLASymbol(
            name: s.name,
            kind: convertSymbolKind(s.kind),
            range: convertRange(s.range),
            selectionRange: s.selectionRange.map { convertRange($0) },
            children: s.children.map { convertSymbol($0) }
        )
    }

    private func convertHighlightToken(_ t: HighlightToken) -> TLAHighlightToken {
        TLAHighlightToken(
            range: convertRange(t.range),
            tokenType: t.tokenType,
            modifiers: t.modifiers
        )
    }

    private func convertCompletionItem(_ c: CompletionItem) -> TLACompletionItem {
        TLACompletionItem(
            label: c.label,
            kind: convertCompletionKind(c.kind),
            detail: c.detail,
            insertText: c.insertText
        )
    }

    private func convertRange(_ r: Range) -> TLARange {
        TLARange(
            start: TLAPosition(line: r.start.line, column: r.start.column),
            end: TLAPosition(line: r.end.line, column: r.end.column)
        )
    }

    private func convertSeverity(_ s: DiagnosticSeverity) -> TLADiagnosticSeverity {
        switch s {
        case .error: return .error
        case .warning: return .warning
        case .information: return .information
        case .hint: return .hint
        }
    }

    private func convertSymbolKind(_ k: SymbolKind) -> TLASymbolKind {
        switch k {
        case .module: return .module
        case .`operator`: return .operator
        case .variable: return .variable
        case .constant: return .constant
        case .theorem: return .theorem
        case .definition: return .definition
        case .instance: return .instance
        case .assumption: return .assumption
        }
    }

    private func convertCompletionKind(_ k: CompletionKind) -> TLACompletionKind {
        switch k {
        case .keyword: return .keyword
        case .`operator`: return .operator
        case .variable: return .variable
        case .constant: return .constant
        case .module: return .module
        case .snippet: return .snippet
        case .function: return .function
        case .theorem: return .theorem
        case .proofTactic: return .proofTactic
        }
    }

    private func convertCompletionContext(_ c: CompletionContext) -> TLACompletionContext {
        switch c {
        case .topLevel: return .topLevel
        case .afterExtends: return .afterExtends
        case .afterInstance: return .afterInstance
        case .inExpression: return .inExpression
        case .inProof: return .inProof
        case .afterSetOperator: return .afterSetOperator
        case .inLetDef: return .inLetDef
        case .afterWith: return .afterWith
        case .unknown: return .unknown
        }
    }

    private func convertDetailedCompletionItem(_ c: DetailedCompletionItem) -> TLADetailedCompletionItem {
        TLADetailedCompletionItem(
            label: c.label,
            kind: convertCompletionKind(c.kind),
            detail: c.detail,
            documentation: c.documentation,
            insertText: c.insertText,
            filterText: c.filterText,
            sortPriority: c.sortPriority,
            signature: c.signature
        )
    }

    private func convertSignatureHelp(_ s: SignatureHelp) -> TLASignatureHelp {
        TLASignatureHelp(
            signatures: s.signatures.map { convertSignatureInfo($0) },
            activeSignature: s.activeSignature,
            activeParameter: s.activeParameter
        )
    }

    private func convertSignatureInfo(_ s: SignatureInfo) -> TLASignatureInfo {
        TLASignatureInfo(
            label: s.label,
            documentation: s.documentation,
            parameters: s.parameters.map { convertParameterInfo($0) }
        )
    }

    private func convertParameterInfo(_ p: ParameterInfo) -> TLAParameterInfo {
        TLAParameterInfo(
            label: p.label,
            documentation: p.documentation
        )
    }
}

// MARK: - TLACore Factory

// MARK: - Folding Range

/// A foldable region in the document
struct TLAFoldingRange: Equatable {
    enum Kind {
        case comment      // Block comments (* ... *)
        case region       // Operator definitions, PROOF blocks
        case imports      // EXTENDS
    }

    let startLine: Int
    let endLine: Int
    let kind: Kind
    let collapsedText: String?  // Text to show when collapsed (e.g., "...")
}

// MARK: - Folding Range Detection Extension

extension TLACoreWrapper {

    /// Get all foldable regions in the document
    func getFoldingRanges(in source: String) -> [TLAFoldingRange] {
        var ranges: [TLAFoldingRange] = []
        let lines = source.components(separatedBy: "\n")

        // Track block comment regions (* ... *)
        var blockCommentStart: Int?
        var inBlockComment = false

        for (lineNum, line) in lines.enumerated() {
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            // Block comments (* ... *)
            if !inBlockComment && trimmed.contains("(*") && !trimmed.contains("*)") {
                blockCommentStart = lineNum
                inBlockComment = true
            } else if inBlockComment && trimmed.contains("*)") {
                if let start = blockCommentStart, lineNum > start {
                    ranges.append(TLAFoldingRange(
                        startLine: start,
                        endLine: lineNum,
                        kind: .comment,
                        collapsedText: "(* ... *)"
                    ))
                }
                inBlockComment = false
                blockCommentStart = nil
            }

            // Single-line block comments
            if trimmed.contains("(*") && trimmed.contains("*)") && !inBlockComment {
                // Don't fold single-line comments
                continue
            }

            // PROOF blocks
            if trimmed.hasPrefix("PROOF") {
                // Find matching QED
                for qedLine in (lineNum + 1)..<lines.count {
                    let qedTrimmed = lines[qedLine].trimmingCharacters(in: .whitespaces)
                    if qedTrimmed.hasPrefix("QED") || qedTrimmed == "QED" {
                        if qedLine > lineNum {
                            ranges.append(TLAFoldingRange(
                                startLine: lineNum,
                                endLine: qedLine,
                                kind: .region,
                                collapsedText: "PROOF ... QED"
                            ))
                        }
                        break
                    }
                }
            }

            // Multi-line operator definitions (Op == ...)
            let operatorPattern = #"^\s*\w+\s*(?:\([^)]*\))?\s*=="#
            if line.range(of: operatorPattern, options: .regularExpression) != nil {
                // Check if this is a multi-line definition
                let startIndent = line.prefix(while: { $0 == " " || $0 == "\t" }).count

                // Find the end of this operator (next definition at same or lower indent, or blank line + definition)
                for nextLine in (lineNum + 1)..<lines.count {
                    let nextContent = lines[nextLine]
                    let nextTrimmed = nextContent.trimmingCharacters(in: .whitespaces)

                    // Skip blank lines
                    if nextTrimmed.isEmpty {
                        continue
                    }

                    let nextIndent = nextContent.prefix(while: { $0 == " " || $0 == "\t" }).count

                    // Another top-level definition starts
                    if nextIndent <= startIndent && nextContent.range(of: operatorPattern, options: .regularExpression) != nil {
                        // End is the previous non-blank line
                        var endLine = nextLine - 1
                        while endLine > lineNum && lines[endLine].trimmingCharacters(in: .whitespaces).isEmpty {
                            endLine -= 1
                        }
                        if endLine > lineNum {
                            let opName = extractOperatorName(from: line)
                            ranges.append(TLAFoldingRange(
                                startLine: lineNum,
                                endLine: endLine,
                                kind: .region,
                                collapsedText: opName != nil ? "\(opName!) == ..." : "..."
                            ))
                        }
                        break
                    }

                    // Module footer
                    if nextTrimmed.hasPrefix("====") {
                        var endLine = nextLine - 1
                        while endLine > lineNum && lines[endLine].trimmingCharacters(in: .whitespaces).isEmpty {
                            endLine -= 1
                        }
                        if endLine > lineNum {
                            let opName = extractOperatorName(from: line)
                            ranges.append(TLAFoldingRange(
                                startLine: lineNum,
                                endLine: endLine,
                                kind: .region,
                                collapsedText: opName != nil ? "\(opName!) == ..." : "..."
                            ))
                        }
                        break
                    }
                }
            }

            // PlusCal algorithm blocks
            if trimmed.contains("--algorithm") || trimmed.contains("(*--algorithm") {
                // Find end algorithm or closing *)
                for endLine in (lineNum + 1)..<lines.count {
                    let endTrimmed = lines[endLine].trimmingCharacters(in: .whitespaces)
                    if endTrimmed.contains("end algorithm") {
                        if endLine > lineNum {
                            ranges.append(TLAFoldingRange(
                                startLine: lineNum,
                                endLine: endLine,
                                kind: .region,
                                collapsedText: "--algorithm ... end algorithm"
                            ))
                        }
                        break
                    }
                }
            }
        }

        // Remove duplicate/overlapping ranges, keeping the larger ones
        return deduplicateFoldingRanges(ranges)
    }

    private func extractOperatorName(from line: String) -> String? {
        let pattern = #"^\s*(\w+)\s*(?:\([^)]*\))?\s*=="#
        guard let range = line.range(of: pattern, options: .regularExpression) else {
            return nil
        }

        let match = String(line[range])
        // Extract just the name
        let namePattern = #"(\w+)"#
        if let nameRange = match.range(of: namePattern, options: .regularExpression) {
            return String(match[nameRange])
        }
        return nil
    }

    private func deduplicateFoldingRanges(_ ranges: [TLAFoldingRange]) -> [TLAFoldingRange] {
        // Sort by start line, then by size (larger first)
        let sorted = ranges.sorted { a, b in
            if a.startLine != b.startLine {
                return a.startLine < b.startLine
            }
            return (a.endLine - a.startLine) > (b.endLine - b.startLine)
        }

        var result: [TLAFoldingRange] = []
        var coveredLines = Set<Int>()

        for range in sorted {
            // Check if this range's start is already covered by another range
            if !coveredLines.contains(range.startLine) {
                result.append(range)
                // Mark lines as covered
                for line in range.startLine...range.endLine {
                    coveredLines.insert(line)
                }
            }
        }

        return result.sorted { $0.startLine < $1.startLine }
    }
}

/// Factory to create the best available TLACore implementation
enum TLACoreFactory {
    /// Indicates if Rust tree-sitter implementation is being used
    static private(set) var isUsingRustCore = false

    /// Create the preferred TLACore implementation
    /// Tries Rust implementation first, falls back to regex-based if unavailable
    static func create() -> any TLACoreProtocol {
        // Try to create RustTLACore
        do {
            let rustCore = try RustTLACore()
            isUsingRustCore = true
            NSLog("[TLACore] Using Rust tree-sitter implementation")
            return rustCore
        } catch {
            isUsingRustCore = false
            NSLog("[TLACore] Rust core unavailable (\(error)), using fallback regex implementation")
            return FallbackTLACore()
        }
    }
}
