import Foundation

// MARK: - Trace Explorer Expressions

enum TraceExpressionError: LocalizedError, Equatable {
    case unexpectedToken(String)
    case unexpectedEndOfInput
    case unknownIdentifier(String)
    case invalidOperation(String)
    case invalidFunction(String)
    case invalidIndex(String)

    var errorDescription: String? {
        switch self {
        case .unexpectedToken(let token):
            return "Unexpected token: \(token)"
        case .unexpectedEndOfInput:
            return "Unexpected end of expression"
        case .unknownIdentifier(let name):
            return "Unknown identifier: \(name)"
        case .invalidOperation(let message):
            return message
        case .invalidFunction(let name):
            return "Unsupported function: \(name)"
        case .invalidIndex(let message):
            return message
        }
    }
}

private enum TraceExpressionToken: Equatable {
    case identifier(String)
    case int(Int)
    case string(String)
    case lParen
    case rParen
    case lBracket
    case rBracket
    case comma
    case dot
    case plus
    case minus
    case star
    case slash
    case percent
    case eq
    case neq
    case lt
    case lte
    case gt
    case gte
    case and
    case or
    case not
    case eof

    var displayName: String {
        switch self {
        case .identifier(let value): return value
        case .int(let value): return "\(value)"
        case .string(let value): return "\"\(value)\""
        case .lParen: return "("
        case .rParen: return ")"
        case .lBracket: return "["
        case .rBracket: return "]"
        case .comma: return ","
        case .dot: return "."
        case .plus: return "+"
        case .minus: return "-"
        case .star: return "*"
        case .slash: return "/"
        case .percent: return "%"
        case .eq: return "="
        case .neq: return "/="
        case .lt: return "<"
        case .lte: return "<="
        case .gt: return ">"
        case .gte: return ">="
        case .and: return "/\\"
        case .or: return "\\/"
        case .not: return "~"
        case .eof: return "EOF"
        }
    }
}

private struct TraceExpressionTokenizer {
    private let characters: [Character]
    private var index = 0

    init(_ expression: String) {
        self.characters = Array(expression)
    }

    mutating func tokenize() throws -> [TraceExpressionToken] {
        var tokens: [TraceExpressionToken] = []

        while let character = current {
            if character.isWhitespace {
                advance()
                continue
            }

            switch character {
            case "(":
                tokens.append(.lParen)
                advance()
            case ")":
                tokens.append(.rParen)
                advance()
            case "[":
                tokens.append(.lBracket)
                advance()
            case "]":
                tokens.append(.rBracket)
                advance()
            case ",":
                tokens.append(.comma)
                advance()
            case ".":
                tokens.append(.dot)
                advance()
            case "+":
                tokens.append(.plus)
                advance()
            case "-":
                tokens.append(.minus)
                advance()
            case "*":
                tokens.append(.star)
                advance()
            case "%":
                tokens.append(.percent)
                advance()
            case "~", "!":
                tokens.append(.not)
                advance()
            case "=":
                tokens.append(.eq)
                advance()
            case "<":
                advance()
                if match("=") {
                    tokens.append(.lte)
                } else {
                    tokens.append(.lt)
                }
            case ">":
                advance()
                if match("=") {
                    tokens.append(.gte)
                } else {
                    tokens.append(.gt)
                }
            case "/":
                advance()
                if match("=") {
                    tokens.append(.neq)
                } else if match("\\") {
                    tokens.append(.and)
                } else if match("/") {
                    tokens.append(.slash)
                } else {
                    tokens.append(.slash)
                }
            case "\\":
                advance()
                if match("/") {
                    tokens.append(.or)
                } else {
                    throw TraceExpressionError.unexpectedToken("\\")
                }
            case "&":
                advance()
                guard match("&") else {
                    throw TraceExpressionError.unexpectedToken("&")
                }
                tokens.append(.and)
            case "|":
                advance()
                guard match("|") else {
                    throw TraceExpressionError.unexpectedToken("|")
                }
                tokens.append(.or)
            case "\"":
                tokens.append(.string(try parseString()))
            default:
                if character.isNumber {
                    tokens.append(.int(parseInt()))
                } else if character.isLetter || character == "_" {
                    tokens.append(.identifier(parseIdentifier()))
                } else {
                    throw TraceExpressionError.unexpectedToken(String(character))
                }
            }
        }

        tokens.append(.eof)
        return tokens
    }

    private var current: Character? {
        guard index < characters.count else { return nil }
        return characters[index]
    }

    @discardableResult
    private mutating func advance() -> Character? {
        defer { index += 1 }
        return current
    }

    private mutating func match(_ expected: Character) -> Bool {
        guard current == expected else { return false }
        advance()
        return true
    }

    private mutating func parseInt() -> Int {
        let start = index
        while let current, current.isNumber {
            advance()
        }
        return Int(String(characters[start..<index])) ?? 0
    }

    private mutating func parseIdentifier() -> String {
        let start = index
        while let current, current.isLetter || current.isNumber || current == "_" {
            advance()
        }
        return String(characters[start..<index])
    }

    private mutating func parseString() throws -> String {
        guard current == "\"" else {
            throw TraceExpressionError.unexpectedToken(current.map(String.init) ?? "EOF")
        }
        advance()

        var result = ""
        while let current {
            if current == "\"" {
                advance()
                return result
            }

            if current == "\\" {
                advance()
                guard let escaped = self.current else {
                    throw TraceExpressionError.unexpectedEndOfInput
                }
                switch escaped {
                case "\"": result.append("\"")
                case "\\": result.append("\\")
                case "n": result.append("\n")
                case "t": result.append("\t")
                default: result.append(escaped)
                }
                advance()
                continue
            }

            result.append(current)
            advance()
        }

        throw TraceExpressionError.unexpectedEndOfInput
    }
}

private indirect enum TraceExpressionNode: Equatable {
    case literal(StateValue)
    case identifier(String)
    case function(name: String, arguments: [TraceExpressionNode])
    case unary(TraceUnaryOperator, TraceExpressionNode)
    case binary(TraceExpressionNode, TraceBinaryOperator, TraceExpressionNode)
    case field(TraceExpressionNode, String)
    case index(TraceExpressionNode, TraceExpressionNode)
}

private enum TraceUnaryOperator: Equatable {
    case not
    case negate
}

private enum TraceBinaryOperator: Equatable {
    case add
    case subtract
    case multiply
    case divide
    case modulo
    case equal
    case notEqual
    case lessThan
    case lessThanOrEqual
    case greaterThan
    case greaterThanOrEqual
    case and
    case or
}

private struct TraceExpressionParser {
    private let tokens: [TraceExpressionToken]
    private var index = 0

    init(tokens: [TraceExpressionToken]) {
        self.tokens = tokens
    }

    mutating func parse() throws -> TraceExpressionNode {
        let expression = try parseOr()
        guard current == .eof else {
            throw TraceExpressionError.unexpectedToken(current.displayName)
        }
        return expression
    }

    private var current: TraceExpressionToken {
        tokens[min(index, tokens.count - 1)]
    }

    @discardableResult
    private mutating func advance() -> TraceExpressionToken {
        defer { index += 1 }
        return current
    }

    private mutating func consume(_ token: TraceExpressionToken) throws {
        guard current == token else {
            throw TraceExpressionError.unexpectedToken(current.displayName)
        }
        advance()
    }

    private mutating func parseOr() throws -> TraceExpressionNode {
        var expression = try parseAnd()

        while current == .or {
            advance()
            expression = .binary(expression, .or, try parseAnd())
        }

        return expression
    }

    private mutating func parseAnd() throws -> TraceExpressionNode {
        var expression = try parseComparison()

        while current == .and {
            advance()
            expression = .binary(expression, .and, try parseComparison())
        }

        return expression
    }

    private mutating func parseComparison() throws -> TraceExpressionNode {
        var expression = try parseAdditive()

        while true {
            let operation: TraceBinaryOperator
            switch current {
            case .eq: operation = .equal
            case .neq: operation = .notEqual
            case .lt: operation = .lessThan
            case .lte: operation = .lessThanOrEqual
            case .gt: operation = .greaterThan
            case .gte: operation = .greaterThanOrEqual
            default: return expression
            }
            advance()
            expression = .binary(expression, operation, try parseAdditive())
        }
    }

    private mutating func parseAdditive() throws -> TraceExpressionNode {
        var expression = try parseMultiplicative()

        while true {
            let operation: TraceBinaryOperator
            switch current {
            case .plus: operation = .add
            case .minus: operation = .subtract
            default: return expression
            }
            advance()
            expression = .binary(expression, operation, try parseMultiplicative())
        }
    }

    private mutating func parseMultiplicative() throws -> TraceExpressionNode {
        var expression = try parseUnary()

        while true {
            let operation: TraceBinaryOperator
            switch current {
            case .star: operation = .multiply
            case .slash: operation = .divide
            case .percent: operation = .modulo
            default: return expression
            }
            advance()
            expression = .binary(expression, operation, try parseUnary())
        }
    }

    private mutating func parseUnary() throws -> TraceExpressionNode {
        switch current {
        case .not:
            advance()
            return .unary(.not, try parseUnary())
        case .minus:
            advance()
            return .unary(.negate, try parseUnary())
        case .identifier(let name) where name.uppercased() == "DOMAIN":
            advance()
            return .function(name: name, arguments: [try parseUnary()])
        default:
            return try parsePostfix()
        }
    }

    private mutating func parsePostfix() throws -> TraceExpressionNode {
        var expression = try parsePrimary()

        while true {
            switch current {
            case .dot:
                advance()
                guard case .identifier(let field) = current else {
                    throw TraceExpressionError.unexpectedToken(current.displayName)
                }
                advance()
                expression = .field(expression, field)
            case .lBracket:
                advance()
                let indexExpression = try parseOr()
                try consume(.rBracket)
                expression = .index(expression, indexExpression)
            default:
                return expression
            }
        }
    }

    private mutating func parsePrimary() throws -> TraceExpressionNode {
        switch current {
        case .int(let value):
            advance()
            return .literal(.int(value))
        case .string(let value):
            advance()
            return .literal(.string(value))
        case .identifier(let name):
            advance()
            if name == "TRUE" {
                return .literal(.bool(true))
            }
            if name == "FALSE" {
                return .literal(.bool(false))
            }

            if current == .lParen {
                advance()
                var arguments: [TraceExpressionNode] = []
                if current != .rParen {
                    arguments.append(try parseOr())
                    while current == .comma {
                        advance()
                        arguments.append(try parseOr())
                    }
                }
                try consume(.rParen)
                return .function(name: name, arguments: arguments)
            }

            return .identifier(name)
        case .lParen:
            advance()
            let expression = try parseOr()
            try consume(.rParen)
            return expression
        case .eof:
            throw TraceExpressionError.unexpectedEndOfInput
        default:
            throw TraceExpressionError.unexpectedToken(current.displayName)
        }
    }
}

enum TraceExplorerExpressionEngine {

    static func evaluate(_ expression: String, with variables: [String: StateValue]) throws -> StateValue {
        var tokenizer = TraceExpressionTokenizer(expression)
        let tokens = try tokenizer.tokenize()
        var parser = TraceExpressionParser(tokens: tokens)
        let node = try parser.parse()
        return try evaluate(node, with: variables)
    }

    private static func evaluate(_ node: TraceExpressionNode, with variables: [String: StateValue]) throws -> StateValue {
        switch node {
        case .literal(let value):
            return value
        case .identifier(let name):
            guard let value = variables[name] else {
                throw TraceExpressionError.unknownIdentifier(name)
            }
            return value
        case .field(let base, let field):
            let baseValue = try evaluate(base, with: variables)
            guard case .record(let fields) = baseValue else {
                throw TraceExpressionError.invalidOperation("Field access requires a record value")
            }
            guard let value = fields[field] else {
                throw TraceExpressionError.invalidOperation("Record has no field named \(field)")
            }
            return value
        case .index(let base, let indexNode):
            let baseValue = try evaluate(base, with: variables)
            let indexValue = try evaluate(indexNode, with: variables)
            return try index(baseValue, with: indexValue)
        case .function(let name, let arguments):
            let evaluatedArguments = try arguments.map { try evaluate($0, with: variables) }
            return try call(function: name, arguments: evaluatedArguments)
        case .unary(let operation, let expression):
            let value = try evaluate(expression, with: variables)
            switch operation {
            case .not:
                let boolean = try boolValue(from: value)
                return .bool(!boolean)
            case .negate:
                let integer = try intValue(from: value)
                return .int(-integer)
            }
        case .binary(let lhs, let operation, let rhs):
            let leftValue = try evaluate(lhs, with: variables)
            let rightValue = try evaluate(rhs, with: variables)
            return try apply(operation: operation, lhs: leftValue, rhs: rightValue)
        }
    }

    private static func apply(operation: TraceBinaryOperator, lhs: StateValue, rhs: StateValue) throws -> StateValue {
        switch operation {
        case .add:
            let left = try intValue(from: lhs)
            let right = try intValue(from: rhs)
            return .int(left + right)
        case .subtract:
            let left = try intValue(from: lhs)
            let right = try intValue(from: rhs)
            return .int(left - right)
        case .multiply:
            let left = try intValue(from: lhs)
            let right = try intValue(from: rhs)
            return .int(left * right)
        case .divide:
            let left = try intValue(from: lhs)
            let divisor = try intValue(from: rhs)
            guard divisor != 0 else {
                throw TraceExpressionError.invalidOperation("Division by zero")
            }
            return .int(left / divisor)
        case .modulo:
            let left = try intValue(from: lhs)
            let divisor = try intValue(from: rhs)
            guard divisor != 0 else {
                throw TraceExpressionError.invalidOperation("Modulo by zero")
            }
            return .int(left % divisor)
        case .equal:
            return .bool(lhs == rhs)
        case .notEqual:
            return .bool(lhs != rhs)
        case .lessThan:
            return .bool(try compare(lhs, rhs) < 0)
        case .lessThanOrEqual:
            return .bool(try compare(lhs, rhs) <= 0)
        case .greaterThan:
            return .bool(try compare(lhs, rhs) > 0)
        case .greaterThanOrEqual:
            return .bool(try compare(lhs, rhs) >= 0)
        case .and:
            let left = try boolValue(from: lhs)
            let right = try boolValue(from: rhs)
            return .bool(left && right)
        case .or:
            let left = try boolValue(from: lhs)
            let right = try boolValue(from: rhs)
            return .bool(left || right)
        }
    }

    private static func call(function name: String, arguments: [StateValue]) throws -> StateValue {
        switch name.uppercased() {
        case "LEN":
            guard arguments.count == 1 else {
                throw TraceExpressionError.invalidOperation("Len expects exactly one argument")
            }
            switch arguments[0] {
            case .sequence(let values), .tuple(let values):
                return .int(values.count)
            case .string(let value):
                return .int(value.count)
            default:
                throw TraceExpressionError.invalidOperation("Len requires a sequence, tuple, or string")
            }
        case "CARDINALITY":
            guard arguments.count == 1 else {
                throw TraceExpressionError.invalidOperation("Cardinality expects exactly one argument")
            }
            switch arguments[0] {
            case .set(let values):
                return .int(values.count)
            case .record(let fields):
                return .int(fields.count)
            case .function(let mapping):
                return .int(mapping.count)
            case .sequence(let values), .tuple(let values):
                return .int(values.count)
            default:
                throw TraceExpressionError.invalidOperation("Cardinality requires a finite container value")
            }
        case "HEAD":
            guard arguments.count == 1 else {
                throw TraceExpressionError.invalidOperation("Head expects exactly one argument")
            }
            guard case .sequence(let values) = arguments[0], let first = values.first else {
                throw TraceExpressionError.invalidOperation("Head requires a non-empty sequence")
            }
            return first
        case "TAIL":
            guard arguments.count == 1 else {
                throw TraceExpressionError.invalidOperation("Tail expects exactly one argument")
            }
            guard case .sequence(let values) = arguments[0], !values.isEmpty else {
                throw TraceExpressionError.invalidOperation("Tail requires a non-empty sequence")
            }
            return .sequence(Array(values.dropFirst()))
        case "DOMAIN":
            guard arguments.count == 1 else {
                throw TraceExpressionError.invalidOperation("DOMAIN expects exactly one argument")
            }
            switch arguments[0] {
            case .record(let fields):
                return .set(Set(fields.keys.map { StateValueWrapper(.modelValue($0)) }))
            case .function(let mapping):
                return .set(Set(mapping.keys))
            case .sequence(let values), .tuple(let values):
                let domain = (1...values.count).map { StateValueWrapper(.int($0)) }
                return .set(Set(domain))
            default:
                throw TraceExpressionError.invalidOperation("DOMAIN requires a function-like value")
            }
        default:
            throw TraceExpressionError.invalidFunction(name)
        }
    }

    private static func index(_ base: StateValue, with index: StateValue) throws -> StateValue {
        switch base {
        case .sequence(let values), .tuple(let values):
            let position = try intValue(from: index)
            guard position >= 1, position <= values.count else {
                throw TraceExpressionError.invalidIndex("Sequence index \(position) is out of bounds")
            }
            return values[position - 1]
        case .record(let fields):
            let key = try stringKey(from: index)
            guard let value = fields[key] else {
                throw TraceExpressionError.invalidIndex("Record has no key \(key)")
            }
            return value
        case .function(let mapping):
            let key = StateValueWrapper(index)
            guard let value = mapping[key] else {
                throw TraceExpressionError.invalidIndex("Function has no value for \(index.displayString)")
            }
            return value
        default:
            throw TraceExpressionError.invalidOperation("Indexing requires a sequence, record, or function value")
        }
    }

    private static func intValue(from value: StateValue) throws -> Int {
        guard case .int(let integer) = value else {
            throw TraceExpressionError.invalidOperation("Expected integer value")
        }
        return integer
    }

    private static func boolValue(from value: StateValue) throws -> Bool {
        guard case .bool(let boolean) = value else {
            throw TraceExpressionError.invalidOperation("Expected boolean value")
        }
        return boolean
    }

    private static func stringKey(from value: StateValue) throws -> String {
        switch value {
        case .string(let string):
            return string
        case .modelValue(let string):
            return string
        default:
            throw TraceExpressionError.invalidOperation("Expected string-like key value")
        }
    }

    private static func compare(_ lhs: StateValue, _ rhs: StateValue) throws -> Int {
        switch (lhs, rhs) {
        case (.int(let left), .int(let right)):
            return left == right ? 0 : (left < right ? -1 : 1)
        case (.string(let left), .string(let right)):
            if left == right { return 0 }
            return left < right ? -1 : 1
        case (.modelValue(let left), .modelValue(let right)):
            if left == right { return 0 }
            return left < right ? -1 : 1
        default:
            throw TraceExpressionError.invalidOperation("Comparison requires matching integer or string values")
        }
    }
}
