import AppKit
import UniformTypeIdentifiers

// MARK: - TLADocumentController

/// Custom document controller for TLA+ specific behaviors.
/// See Docs/architecture/01-document-management.md for specification.
final class TLADocumentController: NSDocumentController {

    // MARK: - Document Type Constants

    static let tlaTypeName = "TLA+ Specification"
    static let tlaUTI = "com.tlaplus.specification"
    static let cfgTypeName = "TLA+ Configuration"
    static let cfgUTI = "com.tlaplus.configuration"

    // MARK: - Initialization

    override init() {
        super.init()
    }

    required init?(coder: NSCoder) {
        super.init(coder: coder)
    }

    // MARK: - Document Type Registration

    override var documentClassNames: [String] {
        ["TLADocument"]
    }

    override var defaultType: String? {
        Self.tlaTypeName
    }

    override func documentClass(forType typeName: String) -> AnyClass? {
        TLADocument.self
    }

    override func typeForContents(of url: URL) throws -> String {
        let ext = url.pathExtension.lowercased()
        switch ext {
        case "tla":
            return Self.tlaTypeName
        case "cfg":
            return Self.cfgTypeName
        default:
            return Self.tlaTypeName
        }
    }

    override func displayName(forType typeName: String) -> String {
        switch typeName {
        case Self.tlaTypeName, Self.tlaUTI:
            return "TLA+ Specification"
        case Self.cfgTypeName, Self.cfgUTI:
            return "TLA+ Configuration"
        default:
            return typeName
        }
    }

    // MARK: - New Document

    override func newDocument(_ sender: Any?) {
        let document = TLADocument()
        document.makeWindowControllers()
        document.showWindows()
        addDocument(document)
    }

    override func makeUntitledDocument(ofType typeName: String) throws -> NSDocument {
        let document = TLADocument()
        return document
    }

    override func makeDocument(withContentsOf url: URL, ofType typeName: String) throws -> NSDocument {
        let document = TLADocument()
        try document.read(from: url, ofType: typeName)
        document.fileURL = url
        return document
    }

    /// Create new document from template
    func newDocument(from template: DocumentTemplate) {
        let document = TLADocument()
        document.content = template.content
        document.makeWindowControllers()
        document.showWindows()
        addDocument(document)
    }

    // MARK: - Open Document

    override func openDocument(_ sender: Any?) {
        let panel = NSOpenPanel()
        panel.allowedContentTypes = [
            UTType(filenameExtension: "tla") ?? .plainText,
            UTType(filenameExtension: "cfg") ?? .plainText
        ]
        panel.allowsMultipleSelection = true
        panel.canChooseDirectories = false

        panel.begin { [weak self] response in
            guard response == .OK else { return }
            for url in panel.urls {
                self?.openDocument(withContentsOf: url, display: true) { _, _, _ in }
            }
        }
    }

    /// Open specific file programmatically
    func openDocument(at url: URL) {
        openDocument(withContentsOf: url, display: true) { document, wasOpen, error in
            if let error = error {
                NSApp.presentError(error)
            }
        }
    }

    // MARK: - Recent Documents

    override func noteNewRecentDocumentURL(_ url: URL) {
        if url.pathExtension == "tla" || url.pathExtension == "cfg" {
            super.noteNewRecentDocumentURL(url)
        }
    }
}

// MARK: - Document Templates

/// Templates for creating new TLA+ documents
enum DocumentTemplate: String, CaseIterable {
    // Basic
    case empty
    case specification
    case plusCal
    // Patterns
    case mutualExclusion
    case producerConsumer
    case leaderElection
    // Advanced
    case refinement
    case stateMachine
    // Learning
    case annotatedTutorial
    case propertyChecking

    var displayName: String {
        switch self {
        case .empty: return "Empty Module"
        case .specification: return "Simple Specification"
        case .plusCal: return "PlusCal Algorithm"
        case .mutualExclusion: return "Mutual Exclusion"
        case .producerConsumer: return "Producer-Consumer"
        case .leaderElection: return "Leader Election"
        case .refinement: return "Refinement Mapping"
        case .stateMachine: return "State Machine"
        case .annotatedTutorial: return "Annotated Tutorial"
        case .propertyChecking: return "Property Checking"
        }
    }

    var category: String {
        switch self {
        case .empty, .specification, .plusCal: return "Basic"
        case .mutualExclusion, .producerConsumer, .leaderElection: return "Patterns"
        case .refinement, .stateMachine: return "Advanced"
        case .annotatedTutorial, .propertyChecking: return "Learning"
        }
    }

    var description: String {
        switch self {
        case .empty: return "Minimal TLA+ module boilerplate"
        case .specification: return "Spec with constants, variables, Init/Next"
        case .plusCal: return "PlusCal algorithm with translation markers"
        case .mutualExclusion: return "Two processes with critical section"
        case .producerConsumer: return "Bounded buffer with producer and consumer"
        case .leaderElection: return "Simple ring-based leader election"
        case .refinement: return "Refinement mapping between specs"
        case .stateMachine: return "Generic state machine pattern"
        case .annotatedTutorial: return "Heavily commented learning example"
        case .propertyChecking: return "Invariants and temporal properties"
        }
    }

    var icon: String {
        switch self {
        case .empty: return "doc"
        case .specification: return "doc.text"
        case .plusCal: return "arrow.triangle.2.circlepath"
        case .mutualExclusion: return "lock.shield"
        case .producerConsumer: return "arrow.left.arrow.right"
        case .leaderElection: return "crown"
        case .refinement: return "arrow.triangle.merge"
        case .stateMachine: return "gearshape.2"
        case .annotatedTutorial: return "book"
        case .propertyChecking: return "checkmark.seal"
        }
    }

    /// All categories in display order
    static var categories: [String] {
        ["Basic", "Patterns", "Advanced", "Learning"]
    }

    /// Templates grouped by category
    static var grouped: [(category: String, templates: [DocumentTemplate])] {
        categories.map { cat in
            (category: cat, templates: allCases.filter { $0.category == cat })
        }
    }

    var content: String {
        switch self {
        case .empty:
            return TLADocument.newDocumentTemplate()

        case .specification:
            return """
            -------------------------------- MODULE Spec --------------------------------
            \\* A TLA+ specification template

            EXTENDS Naturals, Sequences, FiniteSets

            CONSTANTS
                NumProcesses

            VARIABLES
                state

            vars == <<state>>

            TypeInvariant ==
                state \\in [1..NumProcesses -> {"idle", "running", "done"}]

            Init ==
                state = [p \\in 1..NumProcesses |-> "idle"]

            Step(p) ==
                /\\ state[p] = "idle"
                /\\ state' = [state EXCEPT ![p] = "running"]

            Complete(p) ==
                /\\ state[p] = "running"
                /\\ state' = [state EXCEPT ![p] = "done"]

            Next ==
                \\E p \\in 1..NumProcesses:
                    \\/ Step(p)
                    \\/ Complete(p)

            Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)

            ================================================================================
            """

        case .plusCal:
            return """
            -------------------------------- MODULE Algorithm --------------------------------
            EXTENDS Naturals, Sequences, TLC

            (*--algorithm Example
            variables x = 0;

            process Worker \\in 1..3
            begin
                Work:
                    x := x + 1;
            end process;

            end algorithm; *)

            \\* BEGIN TRANSLATION
            \\* END TRANSLATION

            ================================================================================
            """

        case .mutualExclusion:
            return """
            -------------------------------- MODULE MutualExclusion --------------------------------
            \\* Two processes competing for a critical section

            EXTENDS Naturals

            VARIABLES
                pc,       \\* program counter for each process
                turn      \\* whose turn it is

            vars == <<pc, turn>>

            Procs == {0, 1}

            TypeOK ==
                /\\ pc \\in [Procs -> {"idle", "waiting", "critical"}]
                /\\ turn \\in Procs

            Init ==
                /\\ pc = [p \\in Procs |-> "idle"]
                /\\ turn = 0

            Request(p) ==
                /\\ pc[p] = "idle"
                /\\ pc' = [pc EXCEPT ![p] = "waiting"]
                /\\ UNCHANGED turn

            Enter(p) ==
                /\\ pc[p] = "waiting"
                /\\ turn = p
                /\\ pc' = [pc EXCEPT ![p] = "critical"]
                /\\ UNCHANGED turn

            Exit(p) ==
                /\\ pc[p] = "critical"
                /\\ pc' = [pc EXCEPT ![p] = "idle"]
                /\\ turn' = 1 - p

            Next ==
                \\E p \\in Procs: Request(p) \\/ Enter(p) \\/ Exit(p)

            MutualExclusion ==
                ~(pc[0] = "critical" /\\ pc[1] = "critical")

            Spec == Init /\\ [][Next]_vars

            ================================================================================
            """

        case .producerConsumer:
            return """
            -------------------------------- MODULE ProducerConsumer --------------------------------
            \\* Bounded buffer with producer and consumer processes

            EXTENDS Naturals, Sequences

            CONSTANT BufCapacity, Data

            VARIABLES
                buffer,    \\* sequence of items in the buffer
                waitingP,  \\* producer waiting to put
                waitingC   \\* consumer waiting to get

            vars == <<buffer, waitingP, waitingC>>

            TypeOK ==
                /\\ buffer \\in Seq(Data)
                /\\ Len(buffer) <= BufCapacity
                /\\ waitingP \\in BOOLEAN
                /\\ waitingC \\in BOOLEAN

            Init ==
                /\\ buffer = <<>>
                /\\ waitingP = FALSE
                /\\ waitingC = FALSE

            Produce(d) ==
                /\\ Len(buffer) < BufCapacity
                /\\ buffer' = Append(buffer, d)
                /\\ waitingP' = FALSE
                /\\ UNCHANGED waitingC

            Consume ==
                /\\ Len(buffer) > 0
                /\\ buffer' = Tail(buffer)
                /\\ waitingC' = FALSE
                /\\ UNCHANGED waitingP

            ProducerWait ==
                /\\ Len(buffer) = BufCapacity
                /\\ waitingP' = TRUE
                /\\ UNCHANGED <<buffer, waitingC>>

            ConsumerWait ==
                /\\ Len(buffer) = 0
                /\\ waitingC' = TRUE
                /\\ UNCHANGED <<buffer, waitingP>>

            Next ==
                \\/ \\E d \\in Data: Produce(d)
                \\/ Consume
                \\/ ProducerWait
                \\/ ConsumerWait

            BufNotOverflow == Len(buffer) <= BufCapacity

            Spec == Init /\\ [][Next]_vars

            ================================================================================
            """

        case .leaderElection:
            return """
            -------------------------------- MODULE LeaderElection --------------------------------
            \\* Simple ring-based leader election (Chang-Roberts)

            EXTENDS Naturals, FiniteSets

            CONSTANT N   \\* Number of nodes

            ASSUME N > 0

            Nodes == 1..N

            VARIABLES
                inbox,    \\* inbox[n] = set of messages for node n
                leader,   \\* leader[n] = elected leader (0 if none)
                active    \\* active[n] = whether node is still participating

            vars == <<inbox, leader, active>>

            TypeOK ==
                /\\ inbox \\in [Nodes -> SUBSET Nodes]
                /\\ leader \\in [Nodes -> Nodes \\cup {0}]
                /\\ active \\in [Nodes -> BOOLEAN]

            Succ(n) == IF n = N THEN 1 ELSE n + 1

            Init ==
                /\\ inbox = [n \\in Nodes |-> {n}]
                /\\ leader = [n \\in Nodes |-> 0]
                /\\ active = [n \\in Nodes |-> TRUE]

            Send(n) ==
                /\\ active[n]
                /\\ inbox[n] /= {}
                /\\ LET msg == CHOOSE m \\in inbox[n]: \\A m2 \\in inbox[n]: m >= m2
                   IN /\\ IF msg > n
                         THEN /\\ inbox' = [inbox EXCEPT ![Succ(n)] = @ \\cup {msg}, ![n] = @ \\ {msg}]
                              /\\ UNCHANGED leader
                         ELSE IF msg = n
                              THEN /\\ leader' = [leader EXCEPT ![n] = n]
                                   /\\ inbox' = [inbox EXCEPT ![n] = @ \\ {msg}]
                              ELSE /\\ inbox' = [inbox EXCEPT ![n] = @ \\ {msg}]
                                   /\\ UNCHANGED leader
                      /\\ UNCHANGED active

            Next == \\E n \\in Nodes: Send(n)

            AtMostOneLeader ==
                \\A n1, n2 \\in Nodes:
                    (leader[n1] /= 0 /\\ leader[n2] /= 0) => leader[n1] = leader[n2]

            Spec == Init /\\ [][Next]_vars

            ================================================================================
            """

        case .refinement:
            return """
            -------------------------------- MODULE ImplSpec --------------------------------
            \\* Refinement mapping from implementation to abstract spec

            EXTENDS AbstractSpec

            VARIABLES
                implState

            \\* Refinement mapping
            StateMapping ==
                \\* Map implementation state to abstract state
                TRUE

            ImplInit ==
                /\\ implState = InitialValue
                /\\ StateMapping

            ImplNext ==
                /\\ implState' \\in NextStates(implState)
                /\\ StateMapping'

            ImplSpec == ImplInit /\\ [][ImplNext]_implState

            THEOREM ImplSpec => Spec

            ================================================================================
            """

        case .stateMachine:
            return """
            -------------------------------- MODULE StateMachine --------------------------------
            \\* Generic state machine pattern

            EXTENDS Naturals, Sequences

            CONSTANT States, Actions, InitState

            VARIABLES
                state,   \\* current state
                history  \\* sequence of past states (for debugging)

            vars == <<state, history>>

            TypeOK ==
                /\\ state \\in States
                /\\ history \\in Seq(States)

            Init ==
                /\\ state = InitState
                /\\ history = <<>>

            Transition(s, a, s2) ==
                /\\ state = s
                /\\ state' = s2
                /\\ history' = Append(history, state)

            Next ==
                \\E s \\in States, a \\in Actions, s2 \\in States:
                    Transition(s, a, s2)

            NoDeadlock == ENABLED Next

            Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)

            ================================================================================
            """

        case .annotatedTutorial:
            return """
            -------------------------------- MODULE Tutorial --------------------------------
            \\* === TLA+ Tutorial: A Simple Counter ===
            \\*
            \\* This module demonstrates the basic structure of a TLA+ specification.
            \\* TLA+ specs describe systems as state machines with:
            \\*   - An initial state (Init)
            \\*   - Allowed transitions (Next)
            \\*   - Properties to verify (invariants, temporal properties)

            EXTENDS Naturals  \\* Import natural number operators (+, -, <, etc.)

            CONSTANT Max      \\* A constant parameter (set in the model config)

            VARIABLE count    \\* A state variable that changes over time

            \\* --- Type Invariant ---
            \\* Defines what values 'count' can legally have.
            \\* TLC checks this holds in every reachable state.
            TypeOK == count \\in 0..Max

            \\* --- Initial State ---
            \\* The system starts with count = 0
            Init == count = 0

            \\* --- Increment Action ---
            \\* count can increase by 1 if below Max
            \\* The prime (') denotes the next-state value
            Increment ==
                /\\ count < Max         \\* precondition
                /\\ count' = count + 1  \\* effect

            \\* --- Reset Action ---
            \\* count can reset to 0 from any state
            Reset ==
                count' = 0

            \\* --- Next-State Relation ---
            \\* Either increment or reset can happen
            Next ==
                \\/ Increment
                \\/ Reset

            \\* --- Safety Property ---
            \\* count never exceeds Max
            Safety == count <= Max

            \\* --- Full Specification ---
            \\* Init state, then always Next transitions on the variable 'count'
            Spec == Init /\\ [][Next]_count

            ================================================================================
            """

        case .propertyChecking:
            return """
            -------------------------------- MODULE PropertyChecking --------------------------------
            \\* Demonstrates different kinds of properties TLC can check

            EXTENDS Naturals

            VARIABLES x, y, phase

            vars == <<x, y, phase>>

            TypeOK ==
                /\\ x \\in 0..10
                /\\ y \\in 0..10
                /\\ phase \\in {"init", "compute", "done"}

            \\* --- Invariants (safety properties checked in every state) ---
            Safety == x + y <= 20
            NonNegative == x >= 0 /\\ y >= 0

            Init ==
                /\\ x = 0
                /\\ y = 0
                /\\ phase = "init"

            StartCompute ==
                /\\ phase = "init"
                /\\ phase' = "compute"
                /\\ UNCHANGED <<x, y>>

            Compute ==
                /\\ phase = "compute"
                /\\ x + y < 10
                /\\ \\/ (x' = x + 1 /\\ UNCHANGED y)
                   \\/ (y' = y + 1 /\\ UNCHANGED x)
                /\\ UNCHANGED phase

            Finish ==
                /\\ phase = "compute"
                /\\ x + y >= 10
                /\\ phase' = "done"
                /\\ UNCHANGED <<x, y>>

            Next == StartCompute \\/ Compute \\/ Finish

            \\* --- Temporal Properties (checked over behaviors/traces) ---
            \\* Eventually the system reaches "done"
            Liveness == <>(phase = "done")

            \\* Phase always eventually changes
            NoStarvation == []<>(phase /= "compute")

            Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)

            ================================================================================
            """
        }
    }
}
