import Foundation

// MARK: - TLA Service Protocol

/// XPC protocol for TLC and TLAPS operations.
/// The service runs in a separate process for crash isolation and resource management.
@objc protocol TLAServiceProtocol {

    // MARK: - Parsing

    /// Parse a TLA+ specification
    func parseModule(
        content: String,
        reply: @escaping (Data?, Error?) -> Void
    )

    /// Get symbols from parsed module
    func getSymbols(
        content: String,
        reply: @escaping ([SymbolInfo]) -> Void
    )

    /// Get diagnostics (errors, warnings)
    func getDiagnostics(
        content: String,
        reply: @escaping ([DiagnosticInfo]) -> Void
    )

    // MARK: - Model Checking (TLC)

    /// Start model checking
    func startModelCheck(
        specPath: String,
        configPath: String?,
        options: ModelCheckOptionsInfo,
        reply: @escaping (String?, Error?) -> Void  // Returns session ID
    )

    /// Stop model checking
    func stopModelCheck(sessionId: String)

    /// Get model check progress
    func getModelCheckProgress(
        sessionId: String,
        reply: @escaping (ModelCheckProgressInfo?) -> Void
    )

    // MARK: - Proof Checking (TLAPS)

    /// Check all proofs in a specification
    func checkAllProofs(
        specPath: String,
        options: ProofCheckOptionsInfo,
        reply: @escaping (String?, Error?) -> Void  // Returns session ID
    )

    /// Check a single proof step
    func checkProofStep(
        specPath: String,
        line: Int,
        column: Int,
        backend: String,
        reply: @escaping (ProofResultInfo?, Error?) -> Void
    )

    /// Stop proof checking
    func stopProofCheck(sessionId: String)

    /// Get proof check progress
    func getProofCheckProgress(
        sessionId: String,
        reply: @escaping (ProofCheckProgressInfo?) -> Void
    )

    // MARK: - PlusCal

    /// Translate PlusCal to TLA+
    func translatePlusCal(
        content: String,
        reply: @escaping (String?, Error?) -> Void
    )
}

// MARK: - Data Transfer Objects

/// These are simple structs that can be serialized over XPC.
/// They mirror the richer types in the main app.

@objc class SymbolInfo: NSObject, NSSecureCoding {
    @objc let name: String
    @objc let kind: String  // "operator", "variable", "constant", "theorem"
    @objc let startLine: Int
    @objc let startColumn: Int
    @objc let endLine: Int
    @objc let endColumn: Int

    static var supportsSecureCoding: Bool { true }

    init(name: String, kind: String, startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) {
        self.name = name
        self.kind = kind
        self.startLine = startLine
        self.startColumn = startColumn
        self.endLine = endLine
        self.endColumn = endColumn
    }

    required init?(coder: NSCoder) {
        name = coder.decodeObject(of: NSString.self, forKey: "name") as String? ?? ""
        kind = coder.decodeObject(of: NSString.self, forKey: "kind") as String? ?? ""
        startLine = coder.decodeInteger(forKey: "startLine")
        startColumn = coder.decodeInteger(forKey: "startColumn")
        endLine = coder.decodeInteger(forKey: "endLine")
        endColumn = coder.decodeInteger(forKey: "endColumn")
    }

    func encode(with coder: NSCoder) {
        coder.encode(name, forKey: "name")
        coder.encode(kind, forKey: "kind")
        coder.encode(startLine, forKey: "startLine")
        coder.encode(startColumn, forKey: "startColumn")
        coder.encode(endLine, forKey: "endLine")
        coder.encode(endColumn, forKey: "endColumn")
    }
}

@objc class DiagnosticInfo: NSObject, NSSecureCoding {
    @objc let message: String
    @objc let severity: String  // "error", "warning", "info", "hint"
    @objc let startLine: Int
    @objc let startColumn: Int
    @objc let endLine: Int
    @objc let endColumn: Int
    @objc let code: String?

    static var supportsSecureCoding: Bool { true }

    init(message: String, severity: String, startLine: Int, startColumn: Int, endLine: Int, endColumn: Int, code: String? = nil) {
        self.message = message
        self.severity = severity
        self.startLine = startLine
        self.startColumn = startColumn
        self.endLine = endLine
        self.endColumn = endColumn
        self.code = code
    }

    required init?(coder: NSCoder) {
        message = coder.decodeObject(of: NSString.self, forKey: "message") as String? ?? ""
        severity = coder.decodeObject(of: NSString.self, forKey: "severity") as String? ?? "error"
        startLine = coder.decodeInteger(forKey: "startLine")
        startColumn = coder.decodeInteger(forKey: "startColumn")
        endLine = coder.decodeInteger(forKey: "endLine")
        endColumn = coder.decodeInteger(forKey: "endColumn")
        code = coder.decodeObject(of: NSString.self, forKey: "code") as String?
    }

    func encode(with coder: NSCoder) {
        coder.encode(message, forKey: "message")
        coder.encode(severity, forKey: "severity")
        coder.encode(startLine, forKey: "startLine")
        coder.encode(startColumn, forKey: "startColumn")
        coder.encode(endLine, forKey: "endLine")
        coder.encode(endColumn, forKey: "endColumn")
        coder.encode(code, forKey: "code")
    }
}

@objc class ModelCheckOptionsInfo: NSObject, NSSecureCoding {
    @objc var workers: Int = 4
    @objc var checkDeadlock: Bool = true
    @objc var depthFirst: Bool = false
    @objc var maxDepth: Int = 0  // 0 = unlimited

    static var supportsSecureCoding: Bool { true }

    override init() {
        super.init()
    }

    required init?(coder: NSCoder) {
        workers = coder.decodeInteger(forKey: "workers")
        checkDeadlock = coder.decodeBool(forKey: "checkDeadlock")
        depthFirst = coder.decodeBool(forKey: "depthFirst")
        maxDepth = coder.decodeInteger(forKey: "maxDepth")
    }

    func encode(with coder: NSCoder) {
        coder.encode(workers, forKey: "workers")
        coder.encode(checkDeadlock, forKey: "checkDeadlock")
        coder.encode(depthFirst, forKey: "depthFirst")
        coder.encode(maxDepth, forKey: "maxDepth")
    }
}

@objc class ModelCheckProgressInfo: NSObject, NSSecureCoding {
    @objc let sessionId: String
    @objc let phase: String
    @objc let statesFound: Int64
    @objc let distinctStates: Int64
    @objc let statesLeft: Int64
    @objc let duration: Double
    @objc let statesPerSecond: Double
    @objc let isComplete: Bool
    @objc let errorMessage: String?

    static var supportsSecureCoding: Bool { true }

    init(sessionId: String, phase: String, statesFound: Int64, distinctStates: Int64,
         statesLeft: Int64, duration: Double, statesPerSecond: Double,
         isComplete: Bool, errorMessage: String?) {
        self.sessionId = sessionId
        self.phase = phase
        self.statesFound = statesFound
        self.distinctStates = distinctStates
        self.statesLeft = statesLeft
        self.duration = duration
        self.statesPerSecond = statesPerSecond
        self.isComplete = isComplete
        self.errorMessage = errorMessage
    }

    required init?(coder: NSCoder) {
        sessionId = coder.decodeObject(of: NSString.self, forKey: "sessionId") as String? ?? ""
        phase = coder.decodeObject(of: NSString.self, forKey: "phase") as String? ?? ""
        statesFound = coder.decodeInt64(forKey: "statesFound")
        distinctStates = coder.decodeInt64(forKey: "distinctStates")
        statesLeft = coder.decodeInt64(forKey: "statesLeft")
        duration = coder.decodeDouble(forKey: "duration")
        statesPerSecond = coder.decodeDouble(forKey: "statesPerSecond")
        isComplete = coder.decodeBool(forKey: "isComplete")
        errorMessage = coder.decodeObject(of: NSString.self, forKey: "errorMessage") as String?
    }

    func encode(with coder: NSCoder) {
        coder.encode(sessionId, forKey: "sessionId")
        coder.encode(phase, forKey: "phase")
        coder.encode(statesFound, forKey: "statesFound")
        coder.encode(distinctStates, forKey: "distinctStates")
        coder.encode(statesLeft, forKey: "statesLeft")
        coder.encode(duration, forKey: "duration")
        coder.encode(statesPerSecond, forKey: "statesPerSecond")
        coder.encode(isComplete, forKey: "isComplete")
        coder.encode(errorMessage, forKey: "errorMessage")
    }
}

@objc class ProofCheckOptionsInfo: NSObject, NSSecureCoding {
    @objc var defaultBackend: String = "auto"
    @objc var timeout: Double = 30.0
    @objc var threads: Int = 4

    static var supportsSecureCoding: Bool { true }

    override init() {
        super.init()
    }

    required init?(coder: NSCoder) {
        defaultBackend = coder.decodeObject(of: NSString.self, forKey: "defaultBackend") as String? ?? "auto"
        timeout = coder.decodeDouble(forKey: "timeout")
        threads = coder.decodeInteger(forKey: "threads")
    }

    func encode(with coder: NSCoder) {
        coder.encode(defaultBackend, forKey: "defaultBackend")
        coder.encode(timeout, forKey: "timeout")
        coder.encode(threads, forKey: "threads")
    }
}

@objc class ProofCheckProgressInfo: NSObject, NSSecureCoding {
    @objc let sessionId: String
    @objc let totalObligations: Int
    @objc let provedCount: Int
    @objc let failedCount: Int
    @objc let pendingCount: Int
    @objc let isComplete: Bool

    static var supportsSecureCoding: Bool { true }

    init(sessionId: String, totalObligations: Int, provedCount: Int,
         failedCount: Int, pendingCount: Int, isComplete: Bool) {
        self.sessionId = sessionId
        self.totalObligations = totalObligations
        self.provedCount = provedCount
        self.failedCount = failedCount
        self.pendingCount = pendingCount
        self.isComplete = isComplete
    }

    required init?(coder: NSCoder) {
        sessionId = coder.decodeObject(of: NSString.self, forKey: "sessionId") as String? ?? ""
        totalObligations = coder.decodeInteger(forKey: "totalObligations")
        provedCount = coder.decodeInteger(forKey: "provedCount")
        failedCount = coder.decodeInteger(forKey: "failedCount")
        pendingCount = coder.decodeInteger(forKey: "pendingCount")
        isComplete = coder.decodeBool(forKey: "isComplete")
    }

    func encode(with coder: NSCoder) {
        coder.encode(sessionId, forKey: "sessionId")
        coder.encode(totalObligations, forKey: "totalObligations")
        coder.encode(provedCount, forKey: "provedCount")
        coder.encode(failedCount, forKey: "failedCount")
        coder.encode(pendingCount, forKey: "pendingCount")
        coder.encode(isComplete, forKey: "isComplete")
    }
}

@objc class ProofResultInfo: NSObject, NSSecureCoding {
    @objc let fingerprint: String
    @objc let status: String  // "proved", "failed", "timeout", "omitted"
    @objc let backend: String
    @objc let duration: Double
    @objc let errorMessage: String?

    static var supportsSecureCoding: Bool { true }

    init(fingerprint: String, status: String, backend: String, duration: Double, errorMessage: String?) {
        self.fingerprint = fingerprint
        self.status = status
        self.backend = backend
        self.duration = duration
        self.errorMessage = errorMessage
    }

    required init?(coder: NSCoder) {
        fingerprint = coder.decodeObject(of: NSString.self, forKey: "fingerprint") as String? ?? ""
        status = coder.decodeObject(of: NSString.self, forKey: "status") as String? ?? ""
        backend = coder.decodeObject(of: NSString.self, forKey: "backend") as String? ?? ""
        duration = coder.decodeDouble(forKey: "duration")
        errorMessage = coder.decodeObject(of: NSString.self, forKey: "errorMessage") as String?
    }

    func encode(with coder: NSCoder) {
        coder.encode(fingerprint, forKey: "fingerprint")
        coder.encode(status, forKey: "status")
        coder.encode(backend, forKey: "backend")
        coder.encode(duration, forKey: "duration")
        coder.encode(errorMessage, forKey: "errorMessage")
    }
}

// MARK: - XPC Connection Manager

/// Manages connection to the TLA Service XPC process
class TLAServiceConnection {
    static let shared = TLAServiceConnection()

    private var connection: NSXPCConnection?
    private let queue = DispatchQueue(label: "com.tlastudio.serviceconnection")

    private init() {}

    /// Get the service proxy
    func service() -> TLAServiceProtocol? {
        queue.sync {
            if connection == nil {
                setupConnection()
            }
            return connection?.remoteObjectProxy as? TLAServiceProtocol
        }
    }

    /// Get service with error handler
    func service(errorHandler: @escaping (Error) -> Void) -> TLAServiceProtocol? {
        queue.sync {
            if connection == nil {
                setupConnection()
            }
            return connection?.remoteObjectProxyWithErrorHandler(errorHandler) as? TLAServiceProtocol
        }
    }

    private func setupConnection() {
        let connection = NSXPCConnection(serviceName: "com.tlastudio.TLAService")
        connection.remoteObjectInterface = NSXPCInterface(with: TLAServiceProtocol.self)

        // Register allowed classes for secure coding
        let interface = connection.remoteObjectInterface!
        let allowedClasses = NSSet(array: [
            SymbolInfo.self,
            DiagnosticInfo.self,
            ModelCheckOptionsInfo.self,
            ModelCheckProgressInfo.self,
            ProofCheckOptionsInfo.self,
            ProofCheckProgressInfo.self,
            ProofResultInfo.self,
            NSArray.self,
            NSString.self,
            NSNumber.self,
        ]) as! Set<AnyHashable>

        interface.setClasses(allowedClasses, for: #selector(TLAServiceProtocol.getSymbols(content:reply:)), argumentIndex: 0, ofReply: true)
        interface.setClasses(allowedClasses, for: #selector(TLAServiceProtocol.getDiagnostics(content:reply:)), argumentIndex: 0, ofReply: true)

        connection.invalidationHandler = { [weak self] in
            self?.queue.sync {
                self?.connection = nil
            }
        }

        connection.resume()
        self.connection = connection
    }

    func invalidate() {
        queue.sync {
            connection?.invalidate()
            connection = nil
        }
    }
}
