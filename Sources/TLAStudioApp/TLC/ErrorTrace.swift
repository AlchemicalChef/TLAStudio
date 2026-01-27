import Foundation

// MARK: - Error Trace

/// A counterexample trace produced by TLC when an error is found
struct ErrorTrace: Codable {
    let type: ErrorType
    let message: String
    let states: [TraceState]
    let loopStart: Int?  // For liveness violations (back loop index)
    let violatedProperty: String?

    enum ErrorType: String, Codable {
        case invariantViolation
        case deadlock
        case livenessViolation
        case assertionFailure
        case evaluationError
        case temporal

        var displayName: String {
            switch self {
            case .invariantViolation:
                return "Invariant Violation"
            case .deadlock:
                return "Deadlock"
            case .livenessViolation:
                return "Liveness Violation"
            case .assertionFailure:
                return "Assertion Failure"
            case .evaluationError:
                return "Evaluation Error"
            case .temporal:
                return "Temporal Property Violation"
            }
        }
    }

    init(
        type: ErrorType,
        message: String,
        states: [TraceState] = [],
        loopStart: Int? = nil,
        violatedProperty: String? = nil
    ) {
        self.type = type
        self.message = message
        self.states = states
        self.loopStart = loopStart
        self.violatedProperty = violatedProperty
    }
}

// MARK: - Trace State

/// A single state in an error trace
struct TraceState: Codable, Identifiable {
    let id: Int
    let action: String?
    let variables: [String: StateValue]
    let location: SourceLocation?

    /// Pre-computed sorted variable names for efficient iteration.
    /// Computed once at init time, avoiding O(n log n) sort on every view render.
    let sortedVariableNames: [String]

    init(
        id: Int,
        action: String? = nil,
        variables: [String: StateValue] = [:],
        location: SourceLocation? = nil
    ) {
        self.id = id
        self.action = action
        self.variables = variables
        self.location = location
        // Pre-compute sorted keys once
        self.sortedVariableNames = variables.keys.sorted()
    }

    // Custom Codable to handle sortedVariableNames
    enum CodingKeys: String, CodingKey {
        case id, action, variables, location
    }

    init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        id = try container.decode(Int.self, forKey: .id)
        action = try container.decodeIfPresent(String.self, forKey: .action)
        variables = try container.decode([String: StateValue].self, forKey: .variables)
        location = try container.decodeIfPresent(SourceLocation.self, forKey: .location)
        // Compute sorted keys after decoding
        sortedVariableNames = variables.keys.sorted()
    }

    func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(id, forKey: .id)
        try container.encodeIfPresent(action, forKey: .action)
        try container.encode(variables, forKey: .variables)
        try container.encodeIfPresent(location, forKey: .location)
        // Don't encode sortedVariableNames - it's derived
    }

    /// Get the display name for this state
    var displayName: String {
        if id == 0 {
            return "Initial State"
        } else if let action = action {
            return "State \(id): \(action)"
        } else {
            return "State \(id)"
        }
    }

    /// Get changed variables compared to previous state
    func changedVariables(from previous: TraceState?) -> Set<String> {
        guard let previous = previous else {
            return Set(variables.keys)
        }

        var changed: Set<String> = []
        for (name, value) in variables {
            if previous.variables[name] != value {
                changed.insert(name)
            }
        }
        return changed
    }
}

// MARK: - Source Location

/// A location in the TLA+ source file
struct SourceLocation: Codable, Equatable {
    let file: String?
    let line: Int
    let column: Int
    let endLine: Int?
    let endColumn: Int?

    init(file: String? = nil, line: Int, column: Int, endLine: Int? = nil, endColumn: Int? = nil) {
        self.file = file
        self.line = line
        self.column = column
        self.endLine = endLine
        self.endColumn = endColumn
    }

    var displayString: String {
        if let file = file {
            return "\(file):\(line):\(column)"
        }
        return "line \(line), column \(column)"
    }
}

// MARK: - State Value

/// A value in a TLA+ state (supports all TLA+ data types)
indirect enum StateValue: Codable, Equatable {
    case int(Int)
    case string(String)
    case bool(Bool)
    case set(Set<StateValueWrapper>)
    case sequence([StateValue])
    case record([String: StateValue])
    case tuple([StateValue])
    case function([StateValueWrapper: StateValue])
    case modelValue(String)

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
            let value = try container.decode([StateValue].self, forKey: .value)
            self = .set(Set(value.map { StateValueWrapper($0) }))
        case "sequence":
            let value = try container.decode([StateValue].self, forKey: .value)
            self = .sequence(value)
        case "record":
            let value = try container.decode([String: StateValue].self, forKey: .value)
            self = .record(value)
        case "tuple":
            let value = try container.decode([StateValue].self, forKey: .value)
            self = .tuple(value)
        case "function":
            // Functions are encoded as array of [key, value] pairs
            let pairs = try container.decode([[StateValue]].self, forKey: .value)
            var dict: [StateValueWrapper: StateValue] = [:]
            for pair in pairs where pair.count == 2 {
                dict[StateValueWrapper(pair[0])] = pair[1]
            }
            self = .function(dict)
        case "modelValue":
            let value = try container.decode(String.self, forKey: .value)
            self = .modelValue(value)
        default:
            throw DecodingError.dataCorruptedError(
                forKey: .type,
                in: container,
                debugDescription: "Unknown state value type: \(type)"
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
            try container.encode(value.map { $0.value }, forKey: .value)
        case .sequence(let value):
            try container.encode("sequence", forKey: .type)
            try container.encode(value, forKey: .value)
        case .record(let value):
            try container.encode("record", forKey: .type)
            try container.encode(value, forKey: .value)
        case .tuple(let value):
            try container.encode("tuple", forKey: .type)
            try container.encode(value, forKey: .value)
        case .function(let value):
            try container.encode("function", forKey: .type)
            let pairs = value.map { [$0.key.value, $0.value] }
            try container.encode(pairs, forKey: .value)
        case .modelValue(let value):
            try container.encode("modelValue", forKey: .type)
            try container.encode(value, forKey: .value)
        }
    }

    // MARK: - Display

    /// Format for display in UI
    var displayString: String {
        switch self {
        case .int(let value):
            return "\(value)"
        case .string(let value):
            return "\"\(value)\""
        case .bool(let value):
            return value ? "TRUE" : "FALSE"
        case .set(let values):
            if values.isEmpty {
                return "{}"
            }
            let formatted = values.map { $0.value.displayString }.sorted().joined(separator: ", ")
            return "{\(formatted)}"
        case .sequence(let values):
            if values.isEmpty {
                return "<<>>"
            }
            let formatted = values.map { $0.displayString }.joined(separator: ", ")
            return "<<\(formatted)>>"
        case .record(let fields):
            if fields.isEmpty {
                return "[]"
            }
            let formatted = fields.sorted(by: { $0.key < $1.key })
                .map { "\($0.key) |-> \($0.value.displayString)" }
                .joined(separator: ", ")
            return "[\(formatted)]"
        case .tuple(let values):
            let formatted = values.map { $0.displayString }.joined(separator: ", ")
            return "<<\(formatted)>>"
        case .function(let mapping):
            if mapping.isEmpty {
                return "[x \\in {} |-> x]"
            }
            let formatted = mapping
                .map { "\($0.key.value.displayString) :> \($0.value.displayString)" }
                .joined(separator: " @@ ")
            return formatted
        case .modelValue(let value):
            return value
        }
    }
}

// MARK: - StateValueWrapper

/// Wrapper to make StateValue hashable for use in Set and Dictionary
struct StateValueWrapper: Codable, Hashable {
    let value: StateValue

    init(_ value: StateValue) {
        self.value = value
    }

    func hash(into hasher: inout Hasher) {
        // Use content-based hashing instead of displayString conversion
        value.hashContent(into: &hasher)
    }

    static func == (lhs: StateValueWrapper, rhs: StateValueWrapper) -> Bool {
        lhs.value == rhs.value
    }
}

// MARK: - StateValue Hashing Extension

extension StateValue {
    /// Recursive content-based hashing that avoids string allocation.
    /// Uses type tags to differentiate between value types.
    func hashContent(into hasher: inout Hasher) {
        switch self {
        case .int(let v):
            hasher.combine(0)  // Type tag for int
            hasher.combine(v)
        case .string(let v):
            hasher.combine(1)  // Type tag for string
            hasher.combine(v)
        case .bool(let v):
            hasher.combine(2)  // Type tag for bool
            hasher.combine(v)
        case .set(let values):
            hasher.combine(3)  // Type tag for set
            hasher.combine(values.count)
            // Sets are unordered, so sort by hash for consistent ordering
            for wrapper in values.sorted(by: { $0.hashValue < $1.hashValue }) {
                wrapper.value.hashContent(into: &hasher)
            }
        case .sequence(let values):
            hasher.combine(4)  // Type tag for sequence
            hasher.combine(values.count)
            for v in values {
                v.hashContent(into: &hasher)
            }
        case .record(let fields):
            hasher.combine(5)  // Type tag for record
            hasher.combine(fields.count)
            for (key, value) in fields.sorted(by: { $0.key < $1.key }) {
                hasher.combine(key)
                value.hashContent(into: &hasher)
            }
        case .tuple(let values):
            hasher.combine(6)  // Type tag for tuple
            hasher.combine(values.count)
            for v in values {
                v.hashContent(into: &hasher)
            }
        case .function(let mapping):
            hasher.combine(7)  // Type tag for function
            hasher.combine(mapping.count)
            for (key, value) in mapping.sorted(by: { $0.key.hashValue < $1.key.hashValue }) {
                key.value.hashContent(into: &hasher)
                value.hashContent(into: &hasher)
            }
        case .modelValue(let v):
            hasher.combine(8)  // Type tag for modelValue
            hasher.combine(v)
        }
    }
}
