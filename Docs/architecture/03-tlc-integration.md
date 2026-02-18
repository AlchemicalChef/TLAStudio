# TLC Integration Architecture

## Overview

Phase 3 integrates TLC (Temporal Logic Checker) for model checking TLA+ specifications. TLC is compiled to native ARM64 using GraalVM for fast startup.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         TLA+ Studio                              │
│  ┌───────────────┐  ┌───────────────┐  ┌─────────────────────┐  │
│  │ Model Config  │  │ Progress View │  │ Error Trace Explorer│  │
│  │ Panel         │  │ (live stats)  │  │ (state navigation)  │  │
│  └───────────────┘  └───────────────┘  └─────────────────────┘  │
└────────────────────────────────┬────────────────────────────────┘
                                 │ XPC
┌────────────────────────────────▼────────────────────────────────┐
│                      TLAService (XPC)                            │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    TLCRunner                             │    │
│  │  - Spawn tlc-native process                              │    │
│  │  - Parse JSON output stream                              │    │
│  │  - Track progress, states, coverage                      │    │
│  │  - Handle errors, counterexamples                        │    │
│  └────────────────────────────┬────────────────────────────┘    │
└────────────────────────────────┼────────────────────────────────┘
                                 │ subprocess (stdio)
┌────────────────────────────────▼────────────────────────────────┐
│              tlc-native (GraalVM native-image)                   │
│  - 50-100ms startup (vs 2-3s JVM)                               │
│  - JSON output mode for machine parsing                          │
│  - Multi-threaded state exploration                              │
└─────────────────────────────────────────────────────────────────┘
```

## Model Configuration

### Data Model

```swift
struct ModelConfig: Codable, Identifiable {
    let id: UUID
    var name: String
    
    // Specification
    var specFile: URL
    var configFile: URL?
    
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
}

enum ConstantValue: Codable {
    case int(Int)
    case string(String)
    case bool(Bool)
    case set([ConstantValue])
    case modelValue(String)
    case symmetrySet(String)
}
```

### Config File Generation

```swift
func generateConfigFile(_ config: ModelConfig) -> String {
    var lines: [String] = []
    
    // Constants
    for (name, value) in config.constants {
        lines.append("CONSTANT \(name) = \(formatValue(value))")
    }
    
    // Invariants
    for inv in config.invariants {
        lines.append("INVARIANT \(inv)")
    }
    
    // Temporal properties
    for prop in config.temporalProperties {
        lines.append("PROPERTY \(prop)")
    }
    
    // Constraints
    if let constraint = config.stateConstraint {
        lines.append("CONSTRAINT \(constraint)")
    }
    
    // Symmetry
    for (setName, values) in config.symmetrySets {
        lines.append("SYMMETRY \(setName)")
    }
    
    return lines.joined(separator: "\n")
}
```

## TLC Runner

### XPC Service Protocol

```swift
@objc protocol TLCServiceProtocol {
    func startModelCheck(
        spec: URL,
        config: ModelConfig,
        progressHandler: @escaping (ModelCheckProgress) -> Void,
        reply: @escaping (ModelCheckResult?, Error?) -> Void
    )
    
    func stopModelCheck(id: UUID)
    
    func pauseModelCheck(id: UUID)
    
    func resumeModelCheck(id: UUID)
    
    func getCheckpointStatus(id: UUID, reply: @escaping (CheckpointInfo?) -> Void)
}
```

### Progress Data

```swift
struct ModelCheckProgress: Codable {
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
    
    enum Phase: String, Codable {
        case parsing
        case computing
        case checkingLiveness
        case done
        case error
    }
}

struct ActionCoverage: Codable {
    let actionName: String
    let count: UInt64
    let distinctStates: UInt64
}
```

### TLC Process Manager

```swift
actor TLCProcessManager {
    private var activeProcesses: [UUID: Process] = [:]
    private let tlcPath: URL
    
    func startModelCheck(
        spec: URL,
        config: ModelConfig,
        progress: @escaping (ModelCheckProgress) -> Void
    ) async throws -> ModelCheckResult {
        
        let sessionId = UUID()
        
        // Build command line
        var arguments = [
            "-tool",                    // Machine-readable output
            "-workers", "\(config.workers)",
            "-checkpoint", "\(Int(config.checkpointInterval))",
        ]
        
        if config.depthFirst {
            arguments += ["-dfid", "\(config.maxDepth ?? 100)"]
        }
        
        if !config.checkDeadlock {
            arguments += ["-deadlock"]
        }
        
        // Add config file
        let configFile = generateTempConfigFile(config)
        arguments += ["-config", configFile.path]
        
        // Add spec
        arguments += [spec.path]
        
        // Create process
        let process = Process()
        process.executableURL = tlcPath
        process.arguments = arguments
        process.currentDirectoryURL = spec.deletingLastPathComponent()
        
        // Set up output parsing
        let stdoutPipe = Pipe()
        let stderrPipe = Pipe()
        process.standardOutput = stdoutPipe
        process.standardError = stderrPipe
        
        activeProcesses[sessionId] = process
        
        // Parse output in real-time
        let parser = TLCOutputParser()
        stdoutPipe.fileHandleForReading.readabilityHandler = { handle in
            let data = handle.availableData
            if let update = parser.parse(data) {
                progress(update)
            }
        }
        
        // Run
        let startTime = Date()
        try process.run()
        process.waitUntilExit()
        
        activeProcesses.removeValue(forKey: sessionId)
        
        // Parse final result
        return parser.finalResult(
            exitCode: process.terminationStatus,
            duration: Date().timeIntervalSince(startTime)
        )
    }
    
    func stop(sessionId: UUID) {
        activeProcesses[sessionId]?.terminate()
    }
}
```

### TLC Output Parser

```swift
class TLCOutputParser {
    private var buffer = Data()
    private var states: UInt64 = 0
    private var distinct: UInt64 = 0
    private var coverage: [String: UInt64] = [:]
    private var errorTrace: ErrorTrace?
    
    func parse(_ data: Data) -> ModelCheckProgress? {
        buffer.append(data)
        
        // TLC tool mode outputs JSON lines
        while let newline = buffer.firstIndex(of: UInt8(ascii: "\n")) {
            let line = buffer[..<newline]
            buffer = buffer[buffer.index(after: newline)...]
            
            guard let json = try? JSONSerialization.jsonObject(with: line) as? [String: Any] else {
                continue
            }
            
            return parseJSON(json)
        }
        return nil
    }
    
    private func parseJSON(_ json: [String: Any]) -> ModelCheckProgress? {
        guard let type = json["type"] as? String else { return nil }
        
        switch type {
        case "progress":
            states = json["states"] as? UInt64 ?? states
            distinct = json["distinct"] as? UInt64 ?? distinct
            return ModelCheckProgress(
                sessionId: UUID(), // filled in by caller
                phase: .computing,
                statesFound: states,
                distinctStates: distinct,
                statesLeft: json["queue"] as? UInt64 ?? 0,
                duration: json["time"] as? TimeInterval ?? 0,
                statesPerSecond: json["sps"] as? Double ?? 0,
                currentAction: json["action"] as? String,
                coverage: parseCoverage(json["coverage"]),
                memoryUsed: json["memory"] as? UInt64 ?? 0
            )
            
        case "error":
            // Parse error trace
            errorTrace = parseErrorTrace(json)
            return nil
            
        case "coverage":
            coverage = json["actions"] as? [String: UInt64] ?? [:]
            return nil
            
        default:
            return nil
        }
    }
}
```

## Error Trace

### Data Model

```swift
struct ErrorTrace: Codable {
    let type: ErrorType
    let message: String
    let states: [TraceState]
    let loopStart: Int?  // For liveness violations
    
    enum ErrorType: String, Codable {
        case invariantViolation
        case deadlock
        case livenessViolation
        case assertionFailure
        case evaluationError
    }
}

struct TraceState: Codable, Identifiable {
    let id: Int
    let action: String?
    let variables: [String: StateValue]
    let location: SourceLocation?
}

enum StateValue: Codable {
    case int(Int)
    case string(String)
    case bool(Bool)
    case set([StateValue])
    case record([String: StateValue])
    case tuple([StateValue])
    case function([StateValue: StateValue])
}
```

### Error Trace View

```swift
struct ErrorTraceView: View {
    let trace: ErrorTrace
    @State private var selectedState: Int = 0
    @State private var diffMode: Bool = true
    
    var body: some View {
        HSplitView {
            // State list
            List(trace.states) { state in
                StateRow(
                    state: state,
                    isSelected: state.id == selectedState,
                    showDiff: diffMode && state.id > 0
                )
                .onTapGesture {
                    selectedState = state.id
                }
            }
            .frame(minWidth: 200)
            
            // State detail
            if let state = trace.states.first(where: { $0.id == selectedState }) {
                StateDetailView(
                    state: state,
                    previousState: selectedState > 0 
                        ? trace.states[selectedState - 1] 
                        : nil,
                    showDiff: diffMode
                )
            }
        }
        .toolbar {
            Toggle("Show Diff", isOn: $diffMode)
            Button("Jump to Source") {
                jumpToSource(trace.states[selectedState])
            }
        }
    }
}
```

## Coverage Analysis

```swift
struct CoverageView: View {
    let coverage: [ActionCoverage]
    let totalStates: UInt64
    
    var body: some View {
        Table(coverage) {
            TableColumn("Action") { action in
                Text(action.actionName)
                    .font(.system(.body, design: .monospaced))
            }
            TableColumn("Count") { action in
                Text("\(action.count)")
            }
            TableColumn("States") { action in
                Text("\(action.distinctStates)")
            }
            TableColumn("Coverage") { action in
                ProgressView(value: Double(action.distinctStates) / Double(totalStates))
            }
        }
    }
}
```

## Model Configuration UI

```swift
struct ModelConfigEditor: View {
    @Binding var config: ModelConfig
    
    var body: some View {
        Form {
            Section("Specification") {
                TextField("Name", text: $config.name)
                // File picker handled by document system
            }
            
            Section("Constants") {
                ForEach(Array(config.constants.keys), id: \.self) { key in
                    HStack {
                        Text(key)
                        Spacer()
                        ConstantValueEditor(value: binding(for: key))
                    }
                }
                Button("Add Constant") { /* ... */ }
            }
            
            Section("What to Check") {
                ForEach(config.invariants.indices, id: \.self) { i in
                    TextField("Invariant", text: $config.invariants[i])
                }
                Button("Add Invariant") {
                    config.invariants.append("")
                }
                
                ForEach(config.temporalProperties.indices, id: \.self) { i in
                    TextField("Property", text: $config.temporalProperties[i])
                }
                Button("Add Property") {
                    config.temporalProperties.append("")
                }
            }
            
            Section("Execution") {
                Stepper("Workers: \(config.workers)", value: $config.workers, in: 1...32)
                Toggle("Check Deadlock", isOn: $config.checkDeadlock)
                Toggle("Depth-First", isOn: $config.depthFirst)
            }
        }
    }
}
```

## GraalVM Build Process

See `Scripts/build-tlc-native.sh` for the build script.

### Required Configuration Files

1. `reflect-config.json` - Reflection metadata for TLC classes
2. `serialization-config.json` - Serialization for checkpoint/restore
3. `proxy-config.json` - Dynamic proxy classes

### Build Steps

```bash
# 1. Install GraalVM
brew install --cask graalvm-jdk

# 2. Install native-image
gu install native-image

# 3. Run tracing agent to gather configs
java -agentlib:native-image-agent=config-output-dir=config \
    -jar tla2tools.jar -workers 4 test.tla

# 4. Build native image
native-image --no-fallback \
    -H:ReflectionConfigurationFiles=config/reflect-config.json \
    -jar tla2tools.jar -o tlc-native

# 5. Verify
./tlc-native -h
```

## Implementation Checklist

- [ ] Create `ModelConfig.swift` data model
- [ ] Create `TLCServiceProtocol.swift` XPC protocol
- [ ] Implement `TLCProcessManager.swift`
- [ ] Implement `TLCOutputParser.swift`
- [ ] Create config file generator
- [ ] Build TLC native image
- [ ] Create `ModelConfigEditor.swift` UI
- [ ] Create `ModelCheckProgressView.swift`
- [ ] Create `ErrorTraceView.swift`
- [ ] Create `CoverageView.swift`
- [ ] Wire up XPC service
- [ ] Test with sample specifications
- [ ] Add checkpoint/restore support
