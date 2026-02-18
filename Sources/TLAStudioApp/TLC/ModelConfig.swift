import Foundation

// MARK: - Model Configuration

/// Configuration for TLC model checking
struct ModelConfig: Codable, Identifiable, Sendable {
    let id: UUID
    var name: String

    // Specification
    var specFile: URL
    var configFile: URL?

    // Init and Next (required for TLC)
    var initPredicate: String
    var nextAction: String

    // Constants
    var constants: [String: ConstantValue]

    // What to check
    var invariants: [String]
    var temporalProperties: [String]
    var stateConstraint: String?
    var actionConstraint: String?

    // Symmetry optimization
    var symmetrySets: [String: [String]]

    // Execution
    var workers: Int
    var checkDeadlock: Bool
    var depthFirst: Bool
    var maxDepth: Int?

    // Checkpointing
    var checkpointInterval: TimeInterval
    var checkpointDir: URL?
    var checkpointEnabled: Bool
    var autoCleanupCheckpoints: Bool

    // Large state space support
    /// Use disk-based fingerprint storage when memory pressure is expected.
    /// Trades speed (~3-5x slower) for unlimited fingerprint capacity.
    var useDiskStorage: Bool
    /// Allow fallback to JVM-based TLC when native image hits memory limits.
    /// JVM has no 32GB heap cap but 2-3s startup overhead.
    var useJVMFallback: Bool

    init(
        id: UUID = UUID(),
        name: String = "Default",
        specFile: URL,
        configFile: URL? = nil,
        initPredicate: String = "Init",
        nextAction: String = "Next",
        constants: [String: ConstantValue] = [:],
        invariants: [String] = [],
        temporalProperties: [String] = [],
        stateConstraint: String? = nil,
        actionConstraint: String? = nil,
        symmetrySets: [String: [String]] = [:],
        workers: Int = 4,
        checkDeadlock: Bool = true,
        depthFirst: Bool = false,
        maxDepth: Int? = nil,
        checkpointInterval: TimeInterval = 300,
        checkpointDir: URL? = nil,
        checkpointEnabled: Bool = true,
        autoCleanupCheckpoints: Bool = false,
        useDiskStorage: Bool = false,
        useJVMFallback: Bool = true
    ) {
        self.id = id
        self.name = name
        self.specFile = specFile
        self.configFile = configFile
        self.initPredicate = initPredicate
        self.nextAction = nextAction
        self.constants = constants
        self.invariants = invariants
        self.temporalProperties = temporalProperties
        self.stateConstraint = stateConstraint
        self.actionConstraint = actionConstraint
        self.symmetrySets = symmetrySets
        self.workers = workers
        self.checkDeadlock = checkDeadlock
        self.depthFirst = depthFirst
        self.maxDepth = maxDepth
        self.checkpointInterval = checkpointInterval
        self.checkpointDir = checkpointDir
        self.checkpointEnabled = checkpointEnabled
        self.autoCleanupCheckpoints = autoCleanupCheckpoints
        self.useDiskStorage = useDiskStorage
        self.useJVMFallback = useJVMFallback
    }
}

// MARK: - Constant Values

/// Represents a constant value in TLA+ model configuration
enum ConstantValue: Codable, Equatable, Sendable {
    case int(Int)
    case string(String)
    case bool(Bool)
    case set([ConstantValue])
    case modelValue(String)
    case symmetrySet(String)

    // MARK: - Codable

    enum CodingKeys: String, CodingKey {
        case type, value
    }

    init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        let type = try container.decode(String.self, forKey: .type)

        switch type {
        case "int":
            let value = try container.decode(Int.self, forKey: .value)
            self = .int(value)
        case "string":
            let value = try container.decode(String.self, forKey: .value)
            self = .string(value)
        case "bool":
            let value = try container.decode(Bool.self, forKey: .value)
            self = .bool(value)
        case "set":
            let value = try container.decode([ConstantValue].self, forKey: .value)
            self = .set(value)
        case "modelValue":
            let value = try container.decode(String.self, forKey: .value)
            self = .modelValue(value)
        case "symmetrySet":
            let value = try container.decode(String.self, forKey: .value)
            self = .symmetrySet(value)
        default:
            throw DecodingError.dataCorruptedError(
                forKey: .type,
                in: container,
                debugDescription: "Unknown constant value type: \(type)"
            )
        }
    }

    func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)

        switch self {
        case .int(let value):
            try container.encode("int", forKey: .type)
            try container.encode(value, forKey: .value)
        case .string(let value):
            try container.encode("string", forKey: .type)
            try container.encode(value, forKey: .value)
        case .bool(let value):
            try container.encode("bool", forKey: .type)
            try container.encode(value, forKey: .value)
        case .set(let value):
            try container.encode("set", forKey: .type)
            try container.encode(value, forKey: .value)
        case .modelValue(let value):
            try container.encode("modelValue", forKey: .type)
            try container.encode(value, forKey: .value)
        case .symmetrySet(let value):
            try container.encode("symmetrySet", forKey: .type)
            try container.encode(value, forKey: .value)
        }
    }

    // MARK: - Formatting

    /// Format for TLC config file output
    var tlcFormat: String {
        switch self {
        case .int(let value):
            return "\(value)"
        case .string(let value):
            let escaped = value.replacingOccurrences(of: "\\", with: "\\\\")
                .replacingOccurrences(of: "\"", with: "\\\"")
            return "\"\(escaped)\""
        case .bool(let value):
            return value ? "TRUE" : "FALSE"
        case .set(let values):
            let formatted = values.map { $0.tlcFormat }.joined(separator: ", ")
            return "{\(formatted)}"
        case .modelValue(let value):
            return value
        case .symmetrySet(let value):
            return value
        }
    }
}

// MARK: - Model Check Progress

/// Progress update during model checking
struct ModelCheckProgress: Codable, Sendable {
    let sessionId: UUID
    let phase: Phase
    let statesFound: UInt64
    let distinctStates: UInt64
    let statesLeft: UInt64
    let duration: TimeInterval
    let statesPerSecond: Double
    let currentAction: String?
    let coverage: [ActionCoverage]
    let memoryUsed: UInt64

    enum Phase: String, Codable, Sendable {
        case parsing
        case computing
        case checkingLiveness
        case done
        case error
    }

    init(
        sessionId: UUID,
        phase: Phase,
        statesFound: UInt64 = 0,
        distinctStates: UInt64 = 0,
        statesLeft: UInt64 = 0,
        duration: TimeInterval = 0,
        statesPerSecond: Double = 0,
        currentAction: String? = nil,
        coverage: [ActionCoverage] = [],
        memoryUsed: UInt64 = 0
    ) {
        self.sessionId = sessionId
        self.phase = phase
        self.statesFound = statesFound
        self.distinctStates = distinctStates
        self.statesLeft = statesLeft
        self.duration = duration
        self.statesPerSecond = statesPerSecond
        self.currentAction = currentAction
        self.coverage = coverage
        self.memoryUsed = memoryUsed
    }
}

// MARK: - Action Coverage

/// Coverage statistics for a single action
struct ActionCoverage: Codable, Identifiable, Sendable {
    var id: String { actionName }
    let actionName: String
    let count: UInt64
    let distinctStates: UInt64
}

// MARK: - Model Check Result

/// Final result of model checking
struct ModelCheckResult {
    let sessionId: UUID
    let success: Bool
    let statesFound: UInt64
    let distinctStates: UInt64
    let duration: TimeInterval
    let coverage: [ActionCoverage]
    let errorTrace: ErrorTrace?
    let message: String?

    /// Lazy error trace for large counterexamples (streams from disk)
    /// Use this instead of errorTrace when dealing with traces > 1000 states
    let lazyErrorTrace: LazyErrorTrace?

    /// Whether the model check failed due to out of memory
    let outOfMemory: Bool

    /// Whether JVM retry is suggested (true if native image hit 32GB limit and JVM is available)
    let suggestJVMRetry: Bool

    init(
        sessionId: UUID,
        success: Bool,
        statesFound: UInt64,
        distinctStates: UInt64,
        duration: TimeInterval,
        coverage: [ActionCoverage],
        errorTrace: ErrorTrace?,
        message: String?,
        lazyErrorTrace: LazyErrorTrace? = nil,
        outOfMemory: Bool = false,
        suggestJVMRetry: Bool = false
    ) {
        self.sessionId = sessionId
        self.success = success
        self.statesFound = statesFound
        self.distinctStates = distinctStates
        self.duration = duration
        self.coverage = coverage
        self.errorTrace = errorTrace
        self.message = message
        self.lazyErrorTrace = lazyErrorTrace
        self.outOfMemory = outOfMemory
        self.suggestJVMRetry = suggestJVMRetry
    }

    /// Check if there's any error trace (lazy or in-memory)
    var hasErrorTrace: Bool {
        errorTrace != nil || lazyErrorTrace != nil
    }

    /// Get the error trace state count (from either lazy or in-memory)
    var errorTraceStateCount: Int {
        if let lazy = lazyErrorTrace {
            return lazy.stateCount
        }
        return errorTrace?.states.count ?? 0
    }
}

// MARK: - Config File Generation

extension ModelConfig {

    // MARK: - Input Sanitization

    /// Validates that a string is a valid TLA+ identifier (used for names in config directives).
    /// Valid identifiers match `^[A-Za-z_][A-Za-z0-9_]*$`.
    private static func sanitizeTLCIdentifier(_ name: String) -> String? {
        let pattern = #"^[A-Za-z_][A-Za-z0-9_]*$"#
        guard name.range(of: pattern, options: .regularExpression) != nil else {
            return nil
        }
        return name
    }

    /// Validates that a TLC expression does not contain newlines or TLC directives.
    /// Rejects strings that could inject additional config directives.
    private static func sanitizeTLCExpression(_ expr: String) -> String? {
        // Reject newlines which could inject additional directives.
        // Note: Swift treats \r\n as a single grapheme cluster, so
        // .contains("\n") won't match it. Check Unicode scalars instead.
        guard !expr.unicodeScalars.contains(where: { $0 == "\n" || $0 == "\r" }) else {
            return nil
        }
        return expr
    }

    /// Generate a TLC config file from this configuration
    func generateConfigFile() -> String {
        var lines: [String] = []

        // Header
        lines.append("\\* Generated by TLA+ Studio")
        lines.append("\\* Model: \(name)")
        lines.append("")

        // Init and Next (required) — must be valid identifiers
        if let sanitizedInit = Self.sanitizeTLCExpression(initPredicate) {
            lines.append("INIT \(sanitizedInit)")
        }
        if let sanitizedNext = Self.sanitizeTLCExpression(nextAction) {
            lines.append("NEXT \(sanitizedNext)")
        }
        lines.append("")

        // Constants
        if !constants.isEmpty {
            lines.append("\\* Constants")
            for (name, value) in constants.sorted(by: { $0.key < $1.key }) {
                guard let sanitizedName = Self.sanitizeTLCIdentifier(name) else { continue }
                let formattedValue = value.tlcFormat
                guard Self.sanitizeTLCExpression(formattedValue) != nil else { continue }
                lines.append("CONSTANT \(sanitizedName) = \(formattedValue)")
            }
            lines.append("")
        }

        // Invariants
        if !invariants.isEmpty {
            lines.append("\\* Invariants")
            for inv in invariants where !inv.isEmpty {
                guard let sanitizedInv = Self.sanitizeTLCExpression(inv) else { continue }
                lines.append("INVARIANT \(sanitizedInv)")
            }
            lines.append("")
        }

        // Temporal properties
        if !temporalProperties.isEmpty {
            lines.append("\\* Properties")
            for prop in temporalProperties where !prop.isEmpty {
                guard let sanitizedProp = Self.sanitizeTLCExpression(prop) else { continue }
                lines.append("PROPERTY \(sanitizedProp)")
            }
            lines.append("")
        }

        // Constraints
        if let constraint = stateConstraint, !constraint.isEmpty {
            if let sanitizedConstraint = Self.sanitizeTLCExpression(constraint) {
                lines.append("\\* State constraint")
                lines.append("CONSTRAINT \(sanitizedConstraint)")
                lines.append("")
            }
        }

        if let constraint = actionConstraint, !constraint.isEmpty {
            if let sanitizedConstraint = Self.sanitizeTLCExpression(constraint) {
                lines.append("\\* Action constraint")
                lines.append("ACTION_CONSTRAINT \(sanitizedConstraint)")
                lines.append("")
            }
        }

        // Symmetry
        if !symmetrySets.isEmpty {
            lines.append("\\* Symmetry")
            for (setName, _) in symmetrySets.sorted(by: { $0.key < $1.key }) {
                guard let sanitizedName = Self.sanitizeTLCIdentifier(setName) else { continue }
                lines.append("SYMMETRY \(sanitizedName)")
            }
            lines.append("")
        }

        return lines.joined(separator: "\n")
    }

    /// Write config file to a specific URL
    func write(to url: URL) throws {
        let content = generateConfigFile()
        try content.write(to: url, atomically: true, encoding: .utf8)
    }

    /// Write config file to a temporary location
    func writeTempConfigFile() throws -> URL {
        let tempDir = FileManager.default.temporaryDirectory
        let configURL = tempDir.appendingPathComponent("\(id.uuidString).cfg")
        try write(to: configURL)
        return configURL
    }

    // MARK: - Config File Parsing

    /// Parse an existing .cfg file and extract configuration
    static func parse(from url: URL) -> ParsedConfig? {
        guard let content = try? String(contentsOf: url, encoding: .utf8) else {
            return nil
        }
        return parse(content: content)
    }

    /// Parse config content string
    static func parse(content: String) -> ParsedConfig {
        var result = ParsedConfig()
        let lines = content.components(separatedBy: .newlines)

        for line in lines {
            let trimmed = line.trimmingCharacters(in: .whitespaces)

            // Skip comments and empty lines
            if trimmed.isEmpty || trimmed.hasPrefix("\\*") {
                continue
            }

            // Parse different directives
            if trimmed.hasPrefix("INIT ") {
                result.initPredicate = String(trimmed.dropFirst(5)).trimmingCharacters(in: .whitespaces)
            } else if trimmed.hasPrefix("NEXT ") {
                result.nextAction = String(trimmed.dropFirst(5)).trimmingCharacters(in: .whitespaces)
            } else if trimmed.hasPrefix("SPECIFICATION ") {
                // SPECIFICATION Spec implies Init and Next from Spec definition
                result.specification = String(trimmed.dropFirst(14)).trimmingCharacters(in: .whitespaces)
            } else if trimmed.hasPrefix("INVARIANT ") {
                let inv = String(trimmed.dropFirst(10)).trimmingCharacters(in: .whitespaces)
                if !inv.isEmpty {
                    result.invariants.append(inv)
                }
            } else if trimmed.hasPrefix("PROPERTY ") {
                let prop = String(trimmed.dropFirst(9)).trimmingCharacters(in: .whitespaces)
                if !prop.isEmpty {
                    result.temporalProperties.append(prop)
                }
            } else if trimmed.hasPrefix("CONSTRAINT ") {
                result.stateConstraint = String(trimmed.dropFirst(11)).trimmingCharacters(in: .whitespaces)
            } else if trimmed.hasPrefix("ACTION_CONSTRAINT ") {
                result.actionConstraint = String(trimmed.dropFirst(18)).trimmingCharacters(in: .whitespaces)
            } else if trimmed.hasPrefix("CONSTANT ") || trimmed.hasPrefix("CONSTANTS") {
                // Parse CONSTANT name = value or CONSTANTS block
                parseConstants(from: trimmed, into: &result)
            } else if trimmed.contains("=") && !trimmed.hasPrefix("SYMMETRY") {
                // Likely a constant definition like "NumNodes = 2"
                parseConstantAssignment(from: trimmed, into: &result)
            }
        }

        return result
    }

    private static func parseConstants(from line: String, into result: inout ParsedConfig) {
        var content = line
        if content.hasPrefix("CONSTANT ") {
            content = String(content.dropFirst(9))
        } else if content.hasPrefix("CONSTANTS ") {
            content = String(content.dropFirst(10))
        } else if content == "CONSTANTS" {
            return // Just the keyword, constants follow on next lines
        }

        parseConstantAssignment(from: content, into: &result)
    }

    private static func parseConstantAssignment(from line: String, into result: inout ParsedConfig) {
        // Parse "name = value" format
        let parts = line.split(separator: "=", maxSplits: 1)
        guard parts.count == 2 else { return }

        let name = String(parts[0]).trimmingCharacters(in: .whitespaces)
        let valueStr = String(parts[1]).trimmingCharacters(in: .whitespaces)

        // Skip if name is empty or starts with comment
        guard !name.isEmpty, !name.hasPrefix("\\*") else { return }

        // Parse the value
        let value = parseConstantValue(valueStr)
        result.constants[name] = value
    }

    private static func parseConstantValue(_ str: String) -> ConstantValue {
        let trimmed = str.trimmingCharacters(in: .whitespaces)

        // Try integer
        if let intVal = Int(trimmed) {
            return .int(intVal)
        }

        // Boolean
        if trimmed == "TRUE" {
            return .bool(true)
        }
        if trimmed == "FALSE" {
            return .bool(false)
        }

        // Set like {a, b, c} or {1, 2, 3}
        if trimmed.hasPrefix("{") && trimmed.hasSuffix("}") {
            // For model values, keep as string for now
            return .modelValue(trimmed)
        }

        // Default to string/model value
        return .string(trimmed)
    }

    /// Parsed configuration from a .cfg file
    struct ParsedConfig {
        var initPredicate: String = "Init"
        var nextAction: String = "Next"
        var specification: String?
        var constants: [String: ConstantValue] = [:]
        var invariants: [String] = []
        var temporalProperties: [String] = []
        var stateConstraint: String?
        var actionConstraint: String?
    }
}
