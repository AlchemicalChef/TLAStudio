//! TLA+ Core Library
//!
//! Provides parsing and language services for TLA+ Studio via UniFFI bindings.
//!
//! See Docs/architecture/02-language-intelligence.md for full specification.

use std::sync::LazyLock;
use parking_lot::Mutex;
use tree_sitter::{Parser, Tree, Query, QueryCursor, InputEdit};
use streaming_iterator::StreamingIterator;

// UniFFI setup
uniffi::setup_scaffolding!();

// MARK: - Error Types

#[derive(Debug, thiserror::Error, uniffi::Error)]
pub enum ParseError {
    #[error("Failed to parse: {message}")]
    ParseFailed { message: String },
    
    #[error("Invalid encoding")]
    InvalidEncoding,
    
    #[error("Internal error: {message}")]
    Internal { message: String },
}

// MARK: - Data Types

/// Position in a document (0-indexed)
#[derive(Debug, Clone, Copy, uniffi::Record)]
pub struct Position {
    pub line: u32,
    pub column: u32,
}

/// Range in a document
#[derive(Debug, Clone, Copy, uniffi::Record)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

/// Symbol kinds in TLA+
#[derive(Debug, Clone, Copy, uniffi::Enum)]
pub enum SymbolKind {
    Module,
    Operator,
    Variable,
    Constant,
    Theorem,
    Definition,
    Instance,
    Assumption,
}

/// A symbol in the document
#[derive(Debug, Clone, uniffi::Record)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub range: Range,
    pub selection_range: Option<Range>,
    pub children: Vec<Symbol>,
    /// Parameter names for operator definitions (empty for non-operators)
    pub parameters: Vec<String>,
}

/// Diagnostic severity
#[derive(Debug, Clone, Copy, uniffi::Enum)]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Information,
    Hint,
}

/// A diagnostic message
#[derive(Debug, Clone, uniffi::Record)]
pub struct Diagnostic {
    pub range: Range,
    pub severity: DiagnosticSeverity,
    pub message: String,
    pub code: Option<String>,
}

/// Syntax highlight token
#[derive(Debug, Clone, uniffi::Record)]
pub struct HighlightToken {
    pub range: Range,
    pub token_type: String,
    pub modifiers: Vec<String>,
}

/// Completion item kind
#[derive(Debug, Clone, Copy, uniffi::Enum)]
pub enum CompletionKind {
    Keyword,
    Operator,
    Variable,
    Constant,
    Module,
    Snippet,
    Function,
    Theorem,
    ProofTactic,
}

/// A completion suggestion
#[derive(Debug, Clone, uniffi::Record)]
pub struct CompletionItem {
    pub label: String,
    pub kind: CompletionKind,
    pub detail: Option<String>,
    pub insert_text: Option<String>,
}

/// Detailed completion item with full documentation and sorting
#[derive(Debug, Clone, uniffi::Record)]
pub struct DetailedCompletionItem {
    /// Display label
    pub label: String,
    /// Completion kind for icon selection
    pub kind: CompletionKind,
    /// Short detail text (type/module info)
    pub detail: Option<String>,
    /// Full documentation (markdown)
    pub documentation: Option<String>,
    /// Text to insert (may differ from label)
    pub insert_text: Option<String>,
    /// Filter text for fuzzy matching
    pub filter_text: Option<String>,
    /// Sort priority (lower = higher priority)
    pub sort_priority: u32,
    /// Signature for operators/functions
    pub signature: Option<String>,
}

/// Context where the cursor is located in the AST
#[derive(Debug, Clone, Copy, PartialEq, Eq, uniffi::Enum)]
pub enum CompletionContext {
    /// At top level of module (can define operators, theorems, etc.)
    TopLevel,
    /// After EXTENDS keyword (suggest module names)
    AfterExtends,
    /// After INSTANCE keyword (suggest module names)
    AfterInstance,
    /// Inside an expression (suggest variables, operators, constants)
    InExpression,
    /// Inside a PROOF block (suggest proof tactics)
    InProof,
    /// After \in or \subseteq (suggest set expressions)
    AfterSetOperator,
    /// Inside LET binding definition area
    InLetDef,
    /// After WITH in INSTANCE (suggest parameter mappings)
    AfterWith,
    /// Unknown context
    Unknown,
}

/// Signature help information for operator calls
#[derive(Debug, Clone, uniffi::Record)]
pub struct SignatureHelp {
    /// Available signatures (usually one)
    pub signatures: Vec<SignatureInfo>,
    /// Index of active signature
    pub active_signature: u32,
    /// Index of active parameter (for highlighting)
    pub active_parameter: u32,
}

/// Information about a single signature
#[derive(Debug, Clone, uniffi::Record)]
pub struct SignatureInfo {
    /// Full signature label (e.g., "Append(seq, elem)")
    pub label: String,
    /// Documentation for this signature
    pub documentation: Option<String>,
    /// Parameters
    pub parameters: Vec<ParameterInfo>,
}

/// Information about a single parameter
#[derive(Debug, Clone, uniffi::Record)]
pub struct ParameterInfo {
    /// Parameter name
    pub label: String,
    /// Parameter documentation
    pub documentation: Option<String>,
}

/// Edit information for incremental parsing
#[derive(Debug, Clone, uniffi::Record)]
pub struct EditInfo {
    pub start_byte: u32,
    pub old_end_byte: u32,
    pub new_end_byte: u32,
    pub start_position: Position,
    pub old_end_position: Position,
    pub new_end_position: Position,
}

/// Result of parsing a document
#[derive(uniffi::Object)]
pub struct ParseResult {
    tree: Mutex<Option<Tree>>,
    source: String,
    diagnostics: Vec<Diagnostic>,
}

#[uniffi::export]
impl ParseResult {
    /// Check if parsing succeeded
    pub fn is_valid(&self) -> bool {
        self.tree.lock().is_some()
    }

    /// Get parse diagnostics (errors, warnings)
    pub fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.clone()
    }
}

// MARK: - TLACore Interface

/// Cached keyword completions - computed once at first access
static KEYWORD_COMPLETIONS: LazyLock<Vec<CompletionItem>> = LazyLock::new(|| {
    let keywords = [
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
    ];

    keywords
        .iter()
        .map(|(kw, detail)| CompletionItem {
            label: kw.to_string(),
            kind: CompletionKind::Keyword,
            detail: Some(detail.to_string()),
            insert_text: None,
        })
        .collect()
});

/// Standard TLA+ modules with their exported symbols
static STANDARD_MODULES: LazyLock<Vec<ModuleSignature>> = LazyLock::new(|| {
    vec![
        ModuleSignature {
            name: "Naturals".to_string(),
            doc: "Natural numbers and arithmetic operators".to_string(),
            symbols: vec![
                SymbolSignature {
                    name: "Nat".to_string(),
                    kind: CompletionKind::Constant,
                    signature: None,
                    doc: "The set of natural numbers {0, 1, 2, ...}".to_string(),
                    parameters: vec![],
                    example: Some("n \\in Nat".to_string()),
                },
                SymbolSignature {
                    name: "+".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a + b".to_string()),
                    doc: "Addition of numbers".to_string(),
                    parameters: vec![],
                    example: Some("3 + 5 = 8".to_string()),
                },
                SymbolSignature {
                    name: "-".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a - b".to_string()),
                    doc: "Subtraction of numbers".to_string(),
                    parameters: vec![],
                    example: Some("10 - 4 = 6".to_string()),
                },
                SymbolSignature {
                    name: "*".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a * b".to_string()),
                    doc: "Multiplication of numbers".to_string(),
                    parameters: vec![],
                    example: Some("3 * 4 = 12".to_string()),
                },
                SymbolSignature {
                    name: "\\div".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a \\div b".to_string()),
                    doc: "Integer division".to_string(),
                    parameters: vec![],
                    example: Some("7 \\div 3 = 2".to_string()),
                },
                SymbolSignature {
                    name: "%".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a % b".to_string()),
                    doc: "Modulo (remainder)".to_string(),
                    parameters: vec![],
                    example: Some("7 % 3 = 1".to_string()),
                },
                SymbolSignature {
                    name: "^".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a ^ b".to_string()),
                    doc: "Exponentiation".to_string(),
                    parameters: vec![],
                    example: Some("2 ^ 10 = 1024".to_string()),
                },
                SymbolSignature {
                    name: "..".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a .. b".to_string()),
                    doc: "Integer range from a to b inclusive".to_string(),
                    parameters: vec![],
                    example: Some("1..5 = {1, 2, 3, 4, 5}".to_string()),
                },
            ],
        },
        ModuleSignature {
            name: "Integers".to_string(),
            doc: "Integers (extends Naturals with negative numbers)".to_string(),
            symbols: vec![
                SymbolSignature {
                    name: "Int".to_string(),
                    kind: CompletionKind::Constant,
                    signature: None,
                    doc: "The set of integers {..., -2, -1, 0, 1, 2, ...}".to_string(),
                    parameters: vec![],
                    example: Some("n \\in Int  \\* n can be -3, 0, 42, etc.".to_string()),
                },
            ],
        },
        ModuleSignature {
            name: "Reals".to_string(),
            doc: "Real numbers (extends Integers)".to_string(),
            symbols: vec![
                SymbolSignature {
                    name: "Real".to_string(),
                    kind: CompletionKind::Constant,
                    signature: None,
                    doc: "The set of real numbers".to_string(),
                    parameters: vec![],
                    example: Some("x \\in Real  \\* x can be 3.14, -2.5, etc.".to_string()),
                },
                SymbolSignature {
                    name: "Infinity".to_string(),
                    kind: CompletionKind::Constant,
                    signature: None,
                    doc: "Positive infinity".to_string(),
                    parameters: vec![],
                    example: Some("x < Infinity".to_string()),
                },
            ],
        },
        ModuleSignature {
            name: "Sequences".to_string(),
            doc: "Sequence (list) operations".to_string(),
            symbols: vec![
                SymbolSignature {
                    name: "Seq".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Seq(S)".to_string()),
                    doc: "The set of all finite sequences of elements from S".to_string(),
                    parameters: vec!["S".to_string()],
                    example: Some("seq \\in Seq(Nat)  \\* e.g., <<1, 2, 3>>".to_string()),
                },
                SymbolSignature {
                    name: "Len".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Len(seq)".to_string()),
                    doc: "Length of a sequence".to_string(),
                    parameters: vec!["seq".to_string()],
                    example: Some("Len(<<\"a\", \"b\", \"c\">>) = 3".to_string()),
                },
                SymbolSignature {
                    name: "Head".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Head(seq)".to_string()),
                    doc: "First element of a non-empty sequence".to_string(),
                    parameters: vec!["seq".to_string()],
                    example: Some("Head(<<1, 2, 3>>) = 1".to_string()),
                },
                SymbolSignature {
                    name: "Tail".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Tail(seq)".to_string()),
                    doc: "All but the first element of a non-empty sequence".to_string(),
                    parameters: vec!["seq".to_string()],
                    example: Some("Tail(<<1, 2, 3>>) = <<2, 3>>".to_string()),
                },
                SymbolSignature {
                    name: "Append".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Append(seq, elem)".to_string()),
                    doc: "Append element to the end of a sequence".to_string(),
                    parameters: vec!["seq".to_string(), "elem".to_string()],
                    example: Some("Append(<<1, 2>>, 3) = <<1, 2, 3>>".to_string()),
                },
                SymbolSignature {
                    name: "\\o".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("s1 \\o s2".to_string()),
                    doc: "Concatenation of two sequences".to_string(),
                    parameters: vec![],
                    example: Some("<<1, 2>> \\o <<3, 4>> = <<1, 2, 3, 4>>".to_string()),
                },
                SymbolSignature {
                    name: "SubSeq".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("SubSeq(seq, m, n)".to_string()),
                    doc: "Subsequence from index m to n (1-indexed, inclusive)".to_string(),
                    parameters: vec!["seq".to_string(), "m".to_string(), "n".to_string()],
                    example: Some("SubSeq(<<\"a\",\"b\",\"c\",\"d\">>, 2, 3) = <<\"b\",\"c\">>".to_string()),
                },
                SymbolSignature {
                    name: "SelectSeq".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("SelectSeq(seq, Test)".to_string()),
                    doc: "Filter sequence keeping elements where Test(_) is TRUE".to_string(),
                    parameters: vec!["seq".to_string(), "Test".to_string()],
                    example: Some("SelectSeq(<<1,2,3,4>>, LAMBDA x: x > 2) = <<3,4>>".to_string()),
                },
            ],
        },
        ModuleSignature {
            name: "FiniteSets".to_string(),
            doc: "Operations on finite sets".to_string(),
            symbols: vec![
                SymbolSignature {
                    name: "IsFiniteSet".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("IsFiniteSet(S)".to_string()),
                    doc: "TRUE iff S is a finite set".to_string(),
                    parameters: vec!["S".to_string()],
                    example: Some("IsFiniteSet({1, 2, 3}) = TRUE".to_string()),
                },
                SymbolSignature {
                    name: "Cardinality".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Cardinality(S)".to_string()),
                    doc: "Number of elements in finite set S".to_string(),
                    parameters: vec!["S".to_string()],
                    example: Some("Cardinality({\"a\", \"b\", \"c\"}) = 3".to_string()),
                },
            ],
        },
        ModuleSignature {
            name: "Bags".to_string(),
            doc: "Bag (multiset) operations".to_string(),
            symbols: vec![
                SymbolSignature {
                    name: "BagToSet".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("BagToSet(B)".to_string()),
                    doc: "Convert bag to set (removes duplicates)".to_string(),
                    parameters: vec!["B".to_string()],
                    example: Some("BagToSet((a :> 2) @@ (b :> 1)) = {a, b}".to_string()),
                },
                SymbolSignature {
                    name: "SetToBag".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("SetToBag(S)".to_string()),
                    doc: "Convert set to bag (each element count = 1)".to_string(),
                    parameters: vec!["S".to_string()],
                    example: Some("SetToBag({1, 2}) = (1 :> 1) @@ (2 :> 1)".to_string()),
                },
                SymbolSignature {
                    name: "BagCardinality".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("BagCardinality(B)".to_string()),
                    doc: "Total count of all elements in bag".to_string(),
                    parameters: vec!["B".to_string()],
                    example: Some("BagCardinality((a :> 2) @@ (b :> 3)) = 5".to_string()),
                },
                SymbolSignature {
                    name: "CopiesIn".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("CopiesIn(e, B)".to_string()),
                    doc: "Number of copies of e in bag B".to_string(),
                    parameters: vec!["e".to_string(), "B".to_string()],
                    example: Some("CopiesIn(a, (a :> 3) @@ (b :> 1)) = 3".to_string()),
                },
            ],
        },
        ModuleSignature {
            name: "TLC".to_string(),
            doc: "TLC model checker utilities".to_string(),
            symbols: vec![
                SymbolSignature {
                    name: "Print".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Print(out, val)".to_string()),
                    doc: "Print out and return val (for debugging)".to_string(),
                    parameters: vec!["out".to_string(), "val".to_string()],
                    example: Some("Print(\"x = \", x)  \\* prints \"x = \" then returns x".to_string()),
                },
                SymbolSignature {
                    name: "PrintT".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("PrintT(out)".to_string()),
                    doc: "Print out and return TRUE".to_string(),
                    parameters: vec!["out".to_string()],
                    example: Some("PrintT(<<\"state:\", x, y>>)  \\* print and return TRUE".to_string()),
                },
                SymbolSignature {
                    name: "Assert".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Assert(cond, out)".to_string()),
                    doc: "Assert condition, print out if false".to_string(),
                    parameters: vec!["cond".to_string(), "out".to_string()],
                    example: Some("Assert(x > 0, \"x must be positive\")".to_string()),
                },
                SymbolSignature {
                    name: "JavaTime".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("JavaTime".to_string()),
                    doc: "Current time in milliseconds since epoch".to_string(),
                    parameters: vec![],
                    example: Some("LET t == JavaTime IN ...".to_string()),
                },
                SymbolSignature {
                    name: "@@".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("f @@ g".to_string()),
                    doc: "Function merge: g overrides f where domains overlap".to_string(),
                    parameters: vec![],
                    example: Some("(\"a\" :> 1) @@ (\"b\" :> 2) = [x \\in {\"a\",\"b\"} |-> ...]".to_string()),
                },
                SymbolSignature {
                    name: ":>".to_string(),
                    kind: CompletionKind::Operator,
                    signature: Some("a :> b".to_string()),
                    doc: "Create function mapping a to b".to_string(),
                    parameters: vec![],
                    example: Some("\"key\" :> 42  \\* function: \"key\" -> 42".to_string()),
                },
                SymbolSignature {
                    name: "Permutations".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("Permutations(S)".to_string()),
                    doc: "Set of all permutations of set S".to_string(),
                    parameters: vec!["S".to_string()],
                    example: Some("Permutations({1,2}) = {{1,2}, {2,1}}".to_string()),
                },
                SymbolSignature {
                    name: "SortSeq".to_string(),
                    kind: CompletionKind::Function,
                    signature: Some("SortSeq(seq, Op)".to_string()),
                    doc: "Sort sequence using comparison operator Op".to_string(),
                    parameters: vec!["seq".to_string(), "Op".to_string()],
                    example: Some("SortSeq(<<3,1,2>>, LAMBDA a,b: a < b) = <<1,2,3>>".to_string()),
                },
            ],
        },
        ModuleSignature {
            name: "TLAPS".to_string(),
            doc: "TLA+ Proof System tactics and operators".to_string(),
            symbols: vec![],  // TLAPS provides proof tactics, not operator symbols
        },
    ]
});

/// Module signature information
#[derive(Debug, Clone)]
struct ModuleSignature {
    name: String,
    doc: String,
    symbols: Vec<SymbolSignature>,
}

/// Symbol signature information
#[derive(Debug, Clone)]
struct SymbolSignature {
    name: String,
    kind: CompletionKind,
    signature: Option<String>,
    doc: String,
    parameters: Vec<String>,
    example: Option<String>,
}

/// Standard module names for EXTENDS suggestions
static STANDARD_MODULE_NAMES: LazyLock<Vec<DetailedCompletionItem>> = LazyLock::new(|| {
    STANDARD_MODULES
        .iter()
        .map(|m| DetailedCompletionItem {
            label: m.name.clone(),
            kind: CompletionKind::Module,
            detail: Some("Standard module".to_string()),
            documentation: Some(m.doc.clone()),
            insert_text: None,
            filter_text: None,
            sort_priority: 10,
            signature: None,
        })
        .collect()
});

/// Proof tactics for PROOF block suggestions
static PROOF_TACTICS: LazyLock<Vec<DetailedCompletionItem>> = LazyLock::new(|| {
    let tactics = [
        ("BY", "Prove by using listed facts and definitions", "BY facts DEF defs"),
        ("OBVIOUS", "Step is trivially true", "OBVIOUS"),
        ("OMITTED", "Proof omitted (placeholder)", "OMITTED"),
        ("QED", "End of proof block", "QED"),
        ("HAVE", "Introduce an assumption", "HAVE expr"),
        ("TAKE", "Introduce witness for existential", "TAKE x \\in S"),
        ("WITNESS", "Provide witness for existential goal", "WITNESS expr"),
        ("PICK", "Choose from existential assumption", "PICK x \\in S : P(x)"),
        ("SUFFICES", "Change proof goal", "SUFFICES expr"),
        ("CASE", "Case split", "CASE expr"),
        ("USE", "Add facts to proof context", "USE facts DEF defs"),
        ("HIDE", "Remove facts from proof context", "HIDE DEF defs"),
        ("DEFINE", "Local definition in proof", "DEFINE x == expr"),
        ("DEF", "List of definitions to expand", "DEF Op1, Op2"),
        ("DEFS", "List of definitions to expand", "DEFS Op1, Op2"),
    ];

    tactics
        .iter()
        .map(|(name, doc, sig)| DetailedCompletionItem {
            label: name.to_string(),
            kind: CompletionKind::ProofTactic,
            detail: Some("Proof tactic".to_string()),
            documentation: Some(doc.to_string()),
            insert_text: None,
            filter_text: None,
            sort_priority: 5,
            signature: Some(sig.to_string()),
        })
        .collect()
});

/// Detailed keyword completions with documentation
static DETAILED_KEYWORD_COMPLETIONS: LazyLock<Vec<DetailedCompletionItem>> = LazyLock::new(|| {
    let keywords = [
        ("CONSTANT", "Declare module constants (parameters)", "CONSTANT const1, const2, ...", 1),
        ("CONSTANTS", "Declare module constants (parameters)", "CONSTANTS const1, const2, ...", 1),
        ("VARIABLE", "Declare state variables", "VARIABLE var1, var2, ...", 1),
        ("VARIABLES", "Declare state variables", "VARIABLES var1, var2, ...", 1),
        ("EXTENDS", "Import definitions from other modules", "EXTENDS Module1, Module2, ...", 0),
        ("INSTANCE", "Create parameterized module instance", "INSTANCE Module WITH param <- value, ...", 2),
        ("LOCAL", "Make definition local (not exported)", "LOCAL Op == ...", 2),
        ("THEOREM", "Declare a theorem to be proved", "THEOREM Name == expression", 3),
        ("LEMMA", "Declare a lemma (minor theorem)", "LEMMA Name == expression", 3),
        ("ASSUME", "State an assumption about constants", "ASSUME expression", 2),
        ("ASSUMPTION", "Declare a named assumption", "ASSUMPTION Name == expression", 2),
        ("AXIOM", "Declare an axiom", "AXIOM Name == expression", 3),
        ("PROOF", "Begin a proof block", "PROOF ...", 4),
        ("IF", "Conditional expression", "IF cond THEN expr1 ELSE expr2", 10),
        ("THEN", "Then branch of IF", "IF cond THEN expr1 ELSE expr2", 100),
        ("ELSE", "Else branch of IF", "IF cond THEN expr1 ELSE expr2", 100),
        ("CASE", "Multi-way conditional", "CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3", 10),
        ("OTHER", "Default case in CASE expression", "[] OTHER -> expr", 100),
        ("LET", "Local definitions", "LET x == expr1 IN expr2", 10),
        ("IN", "Body of LET expression", "LET x == e1 IN e2", 100),
        ("CHOOSE", "Hilbert's choice operator", "CHOOSE x \\in S : P(x)", 10),
        ("EXCEPT", "Function/record update", "[f EXCEPT ![a] = b]", 10),
        ("DOMAIN", "Domain of a function", "DOMAIN f", 10),
        ("SUBSET", "Power set (set of all subsets)", "SUBSET S", 10),
        ("UNION", "Generalized union", "UNION SetOfSets", 10),
        ("ENABLED", "Action enablement", "ENABLED Action", 15),
        ("UNCHANGED", "Variables unchanged", "UNCHANGED <<var1, var2>>", 15),
        ("TRUE", "Boolean true", "TRUE", 20),
        ("FALSE", "Boolean false", "FALSE", 20),
        ("BOOLEAN", "The set {TRUE, FALSE}", "BOOLEAN", 20),
    ];

    keywords
        .iter()
        .map(|(name, doc, sig, priority)| DetailedCompletionItem {
            label: name.to_string(),
            kind: CompletionKind::Keyword,
            detail: None,
            documentation: Some(doc.to_string()),
            insert_text: None,
            filter_text: None,
            sort_priority: *priority,
            signature: Some(sig.to_string()),
        })
        .collect()
});

/// TLA+ operators with documentation
static TLA_OPERATORS: LazyLock<Vec<DetailedCompletionItem>> = LazyLock::new(|| {
    let operators = [
        // Set operators
        ("\\in", "Set membership", "x \\in S", 5),
        ("\\notin", "Not a member of set", "x \\notin S", 5),
        ("\\subseteq", "Subset or equal", "A \\subseteq B", 5),
        ("\\subset", "Proper subset", "A \\subset B", 6),
        ("\\cup", "Set union", "A \\cup B", 5),
        ("\\cap", "Set intersection", "A \\cap B", 5),
        ("\\union", "Set union (alias)", "A \\union B", 6),
        ("\\intersect", "Set intersection (alias)", "A \\intersect B", 6),
        ("\\setminus", "Set difference", "A \\ B", 5),
        ("\\X", "Cartesian product", "A \\X B", 5),
        ("\\times", "Cartesian product (alias)", "A \\times B", 6),
        // Quantifiers
        ("\\E", "Existential quantifier", "\\E x \\in S : P(x)", 3),
        ("\\A", "Universal quantifier", "\\A x \\in S : P(x)", 3),
        ("\\EE", "Temporal existential", "\\EE x : F", 8),
        ("\\AA", "Temporal universal", "\\AA x : F", 8),
        // Logic
        ("\\lnot", "Logical negation", "\\lnot P", 5),
        ("\\neg", "Logical negation (alias)", "\\neg P", 6),
        ("\\lor", "Logical OR", "P \\lor Q", 5),
        ("\\land", "Logical AND", "P \\land Q", 5),
        ("\\/", "Logical OR (ASCII)", "P \\/ Q", 6),
        ("/\\", "Logical AND (ASCII)", "P /\\ Q", 6),
        ("=>", "Logical implication", "P => Q", 5),
        ("\\equiv", "Logical equivalence", "P \\equiv Q", 5),
        ("<=>", "Logical equivalence (ASCII)", "P <=> Q", 6),
        // Temporal
        ("[]", "Always (temporal)", "[]P", 10),
        ("<>", "Eventually (temporal)", "<>P", 10),
        ("~>", "Leads to (temporal)", "P ~> Q", 10),
        ("WF_", "Weak fairness", "WF_vars(Action)", 12),
        ("SF_", "Strong fairness", "SF_vars(Action)", 12),
        // Other
        ("'", "Prime (next state)", "x'", 8),
        ("LAMBDA", "Lambda expression", "LAMBDA x : expr", 10),
    ];

    operators
        .iter()
        .map(|(name, doc, sig, priority)| DetailedCompletionItem {
            label: name.to_string(),
            kind: CompletionKind::Operator,
            detail: Some("TLA+ operator".to_string()),
            documentation: Some(doc.to_string()),
            insert_text: None,
            filter_text: None,
            sort_priority: *priority,
            signature: Some(sig.to_string()),
        })
        .collect()
});

/// PlusCal keyword completions
static PLUSCAL_KEYWORDS: LazyLock<Vec<DetailedCompletionItem>> = LazyLock::new(|| {
    let keywords = [
        ("algorithm", "Begin PlusCal algorithm block", 1),
        ("variables", "Declare PlusCal variables", 2),
        ("variable", "Declare a PlusCal variable", 2),
        ("begin", "Begin algorithm body", 3),
        ("end", "End a block", 3),
        ("process", "Define a process", 4),
        ("fair process", "Define a fair process", 4),
        ("fair+", "Define a strongly fair process", 4),
        ("procedure", "Define a procedure", 5),
        ("macro", "Define a macro", 5),
        ("call", "Call a procedure", 6),
        ("return", "Return from procedure", 6),
        ("if", "PlusCal conditional", 10),
        ("then", "PlusCal then branch", 100),
        ("elsif", "PlusCal else-if branch", 10),
        ("else", "PlusCal else branch", 100),
        ("while", "PlusCal while loop", 10),
        ("do", "PlusCal loop body", 100),
        ("either", "Nondeterministic choice", 10),
        ("or", "Alternative in either block", 100),
        ("with", "Local variable binding", 10),
        ("await", "Wait for condition", 10),
        ("when", "Guard (alias for await)", 10),
        ("assert", "PlusCal assertion", 10),
        ("print", "PlusCal print statement", 10),
        ("skip", "No-op statement", 10),
        ("goto", "Jump to label", 10),
        ("define", "Define operators in PlusCal", 5),
    ];

    keywords
        .iter()
        .map(|(name, doc, priority)| DetailedCompletionItem {
            label: name.to_string(),
            kind: CompletionKind::Keyword,
            detail: Some("PlusCal".to_string()),
            documentation: Some(doc.to_string()),
            insert_text: None,
            filter_text: None,
            sort_priority: *priority,
            signature: None,
        })
        .collect()
});

/// Snippet completions for common TLA+ patterns
static SNIPPET_COMPLETIONS: LazyLock<Vec<DetailedCompletionItem>> = LazyLock::new(|| {
    vec![
        DetailedCompletionItem {
            label: "Init ==".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Init predicate".to_string()),
            documentation: Some("Initial state predicate template".to_string()),
            insert_text: Some("Init ==\n    /\\ $0".to_string()),
            filter_text: Some("Init".to_string()),
            sort_priority: 25,
            signature: None,
        },
        DetailedCompletionItem {
            label: "Next ==".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Next-state relation".to_string()),
            documentation: Some("Next-state relation template".to_string()),
            insert_text: Some("Next ==\n    \\/ $0".to_string()),
            filter_text: Some("Next".to_string()),
            sort_priority: 25,
            signature: None,
        },
        DetailedCompletionItem {
            label: "Spec == Init /\\ [][Next]_vars".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Specification formula".to_string()),
            documentation: Some("Standard specification combining Init, Next, and vars".to_string()),
            insert_text: Some("Spec == Init /\\ [][Next]_vars".to_string()),
            filter_text: Some("Spec".to_string()),
            sort_priority: 25,
            signature: None,
        },
        DetailedCompletionItem {
            label: "TypeInvariant ==".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Type invariant".to_string()),
            documentation: Some("Type invariant template".to_string()),
            insert_text: Some("TypeInvariant ==\n    /\\ $0".to_string()),
            filter_text: Some("TypeInvariant".to_string()),
            sort_priority: 25,
            signature: None,
        },
        DetailedCompletionItem {
            label: "IF ... THEN ... ELSE".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Conditional expression".to_string()),
            documentation: Some("IF-THEN-ELSE expression".to_string()),
            insert_text: Some("IF $0 THEN\n    TRUE\nELSE\n    FALSE".to_string()),
            filter_text: Some("IF".to_string()),
            sort_priority: 26,
            signature: None,
        },
        DetailedCompletionItem {
            label: "CHOOSE x \\in S : P(x)".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Choice operator".to_string()),
            documentation: Some("Pick an arbitrary element satisfying a predicate".to_string()),
            insert_text: Some("CHOOSE x \\in $0 : ".to_string()),
            filter_text: Some("CHOOSE".to_string()),
            sort_priority: 26,
            signature: None,
        },
        DetailedCompletionItem {
            label: "\\A x \\in S : P(x)".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Universal quantifier".to_string()),
            documentation: Some("For all elements in a set".to_string()),
            insert_text: Some("\\A x \\in $0 : ".to_string()),
            filter_text: Some("\\A".to_string()),
            sort_priority: 26,
            signature: None,
        },
        DetailedCompletionItem {
            label: "\\E x \\in S : P(x)".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Existential quantifier".to_string()),
            documentation: Some("There exists an element in a set".to_string()),
            insert_text: Some("\\E x \\in $0 : ".to_string()),
            filter_text: Some("\\E".to_string()),
            sort_priority: 26,
            signature: None,
        },
        DetailedCompletionItem {
            label: "[f EXCEPT ![a] = b]".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Function update".to_string()),
            documentation: Some("Update a function/record at a key".to_string()),
            insert_text: Some("[${1:f} EXCEPT ![${2:key}] = $0]".to_string()),
            filter_text: Some("EXCEPT".to_string()),
            sort_priority: 26,
            signature: None,
        },
        DetailedCompletionItem {
            label: "{x \\in S : P(x)}".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Set filter".to_string()),
            documentation: Some("Filter elements from a set by predicate".to_string()),
            insert_text: Some("{x \\in $0 : }".to_string()),
            filter_text: Some("{".to_string()),
            sort_priority: 26,
            signature: None,
        },
        DetailedCompletionItem {
            label: "[x \\in S |-> e]".to_string(),
            kind: CompletionKind::Snippet,
            detail: Some("Function constructor".to_string()),
            documentation: Some("Create a function mapping elements of S to expressions".to_string()),
            insert_text: Some("[x \\in $0 |-> ]".to_string()),
            filter_text: Some("[".to_string()),
            sort_priority: 26,
            signature: None,
        },
    ]
});

/// Main TLA+ language services interface
#[derive(uniffi::Object)]
pub struct TLACore {
    parser: Mutex<Parser>,
    highlight_query: Query,
    /// Pre-interned capture names for highlight queries (avoids repeated allocation)
    capture_names: Vec<String>,
    /// Reusable query cursor (avoids allocation per query)
    query_cursor: Mutex<QueryCursor>,
}

#[uniffi::export]
impl TLACore {
    /// Create a new TLACore instance
    #[uniffi::constructor]
    pub fn new() -> Result<Self, ParseError> {
        let mut parser = Parser::new();
        let language = tree_sitter_tlaplus::LANGUAGE;

        parser.set_language(&language.into()).map_err(|e| ParseError::Internal {
            message: format!("Failed to set language: {}", e),
        })?;

        // Load highlight queries
        let highlight_query = Query::new(&language.into(), tree_sitter_tlaplus::HIGHLIGHT_QUERY)
            .map_err(|e| ParseError::Internal {
                message: format!("Failed to load highlight query: {}", e),
            })?;

        // Pre-intern capture names to avoid repeated allocation during highlighting
        let capture_names: Vec<String> = highlight_query
            .capture_names()
            .iter()
            .map(|s| s.to_string())
            .collect();

        Ok(Self {
            parser: Mutex::new(parser),
            highlight_query,
            capture_names,
            query_cursor: Mutex::new(QueryCursor::new()),
        })
    }
    
    /// Parse a TLA+ document
    pub fn parse(&self, source: String) -> Result<ParseResult, ParseError> {
        let mut parser = self.parser.lock();

        let tree = parser.parse(&source, None);
        let diagnostics = if let Some(ref tree) = tree {
            self.extract_diagnostics(tree, &source)
        } else {
            vec![Diagnostic {
                range: Range {
                    start: Position { line: 0, column: 0 },
                    end: Position { line: 0, column: 0 },
                },
                severity: DiagnosticSeverity::Error,
                message: "Failed to parse document".to_string(),
                code: None,
            }]
        };

        Ok(ParseResult {
            tree: Mutex::new(tree),
            source,
            diagnostics,
        })
    }

    /// Parse a TLA+ document incrementally using previous parse result and edit information.
    /// This is significantly faster than full parsing for small edits in large documents.
    /// Note: The old_result remains valid and usable after this call.
    pub fn parse_incremental(
        &self,
        source: String,
        old_result: &ParseResult,
        edit: EditInfo,
    ) -> Result<ParseResult, ParseError> {
        // Clone the old tree (don't take it - that would invalidate old_result)
        // Release the lock before acquiring parser lock to prevent deadlock
        let old_tree = {
            let tree_guard = old_result.tree.lock();
            tree_guard.clone()
        };

        let mut parser = self.parser.lock();

        let tree = if let Some(mut old) = old_tree {
            // Apply the edit to the cloned tree for incremental parsing
            old.edit(&InputEdit {
                start_byte: edit.start_byte as usize,
                old_end_byte: edit.old_end_byte as usize,
                new_end_byte: edit.new_end_byte as usize,
                start_position: tree_sitter::Point {
                    row: edit.start_position.line as usize,
                    column: edit.start_position.column as usize,
                },
                old_end_position: tree_sitter::Point {
                    row: edit.old_end_position.line as usize,
                    column: edit.old_end_position.column as usize,
                },
                new_end_position: tree_sitter::Point {
                    row: edit.new_end_position.line as usize,
                    column: edit.new_end_position.column as usize,
                },
            });

            // Parse incrementally using the edited tree
            parser.parse(&source, Some(&old))
        } else {
            // No old tree available, fall back to full parse
            parser.parse(&source, None)
        };

        let diagnostics = if let Some(ref tree) = tree {
            self.extract_diagnostics(tree, &source)
        } else {
            vec![Diagnostic {
                range: Range {
                    start: Position { line: 0, column: 0 },
                    end: Position { line: 0, column: 0 },
                },
                severity: DiagnosticSeverity::Error,
                message: "Failed to parse document".to_string(),
                code: None,
            }]
        };

        Ok(ParseResult {
            tree: Mutex::new(tree),
            source,
            diagnostics,
        })
    }
    
    /// Get symbols from parse result
    pub fn get_symbols(&self, result: &ParseResult) -> Vec<Symbol> {
        let tree_guard = result.tree.lock();
        let Some(tree) = tree_guard.as_ref() else {
            return vec![];
        };

        self.extract_symbols(tree.root_node(), &result.source)
    }

    /// Get syntax highlights for a range.
    /// Uses a reusable QueryCursor and pre-interned capture names for performance.
    pub fn get_highlights(&self, result: &ParseResult, range: Range) -> Vec<HighlightToken> {
        let tree_guard = result.tree.lock();
        let Some(tree) = tree_guard.as_ref() else {
            return vec![];
        };

        // Reuse the query cursor to avoid allocation per call
        let mut cursor = self.query_cursor.lock();
        cursor.set_point_range(
            tree_sitter::Point {
                row: range.start.line as usize,
                column: range.start.column as usize,
            }
                ..tree_sitter::Point {
                    row: range.end.line as usize,
                    column: range.end.column as usize,
                },
        );

        let mut tokens = vec![];

        let mut matches =
            cursor.matches(&self.highlight_query, tree.root_node(), result.source.as_bytes());

        while let Some(match_) = matches.next() {
            for capture in match_.captures {
                let node = capture.node;
                // Use pre-interned capture names to avoid repeated allocation
                let Some(capture_name) = self.capture_names.get(capture.index as usize) else {
                    continue;
                };

                tokens.push(HighlightToken {
                    range: Range {
                        start: Position {
                            line: node.start_position().row as u32,
                            column: node.start_position().column as u32,
                        },
                        end: Position {
                            line: node.end_position().row as u32,
                            column: node.end_position().column as u32,
                        },
                    },
                    token_type: capture_name.clone(),
                    modifiers: vec![],
                });
            }
        }

        tokens
    }
    
    /// Get completions at a position.
    /// Uses cached keyword completions for performance.
    pub fn get_completions(&self, _result: &ParseResult, _position: Position) -> Vec<CompletionItem> {
        // TODO: Implement context-aware completions
        // For now, return TLA+ keywords (cached via LazyLock for zero allocation after first call)
        KEYWORD_COMPLETIONS.clone()
    }

    /// Analyze the context at a given position in the source code.
    /// Returns the completion context to determine what completions are appropriate.
    pub fn analyze_context(&self, result: &ParseResult, position: Position) -> CompletionContext {
        let source = &result.source;
        let point = tree_sitter::Point {
            row: position.line as usize,
            column: position.column as usize,
        };

        // Use source-based context analysis (more reliable than tree walking)
        self.determine_context_from_source(source, point)
    }

    /// Get detailed completions based on context at position.
    pub fn get_detailed_completions(
        &self,
        result: &ParseResult,
        position: Position,
    ) -> Vec<DetailedCompletionItem> {
        let context = self.analyze_context(result, position);
        let symbols = self.get_symbols(result);
        let extended_modules = self.get_extended_modules(result);
        let source = &result.source;
        let point = tree_sitter::Point {
            row: position.line as usize,
            column: position.column as usize,
        };

        let mut completions = Vec::new();

        match context {
            CompletionContext::AfterExtends | CompletionContext::AfterInstance => {
                // Only suggest module names
                completions.extend(STANDARD_MODULE_NAMES.clone());
            }

            CompletionContext::InProof => {
                // Suggest proof tactics, plus regular completions
                completions.extend(PROOF_TACTICS.clone());
                completions.extend(self.get_expression_completions_with_context(
                    &symbols, &extended_modules, Some(source), Some(point)));
            }

            CompletionContext::TopLevel => {
                // Suggest top-level keywords and operators
                completions.extend(DETAILED_KEYWORD_COMPLETIONS.iter()
                    .filter(|k| {
                        let label = k.label.as_str();
                        matches!(label,
                            "CONSTANT" | "CONSTANTS" | "VARIABLE" | "VARIABLES" |
                            "EXTENDS" | "INSTANCE" | "LOCAL" | "THEOREM" | "LEMMA" |
                            "ASSUME" | "ASSUMPTION" | "AXIOM"
                        )
                    })
                    .cloned());
                // Also add user-defined symbols for top-level references
                completions.extend(self.symbols_to_completions(&symbols, 20));
                // Add top-level snippets
                completions.extend(SNIPPET_COMPLETIONS.iter()
                    .filter(|s| {
                        let filter = s.filter_text.as_deref().unwrap_or(&s.label);
                        matches!(filter, "Init" | "Next" | "Spec" | "TypeInvariant")
                    })
                    .cloned());
            }

            CompletionContext::InExpression | CompletionContext::InLetDef | CompletionContext::Unknown => {
                // Suggest everything relevant for expressions
                completions.extend(self.get_expression_completions_with_context(
                    &symbols, &extended_modules, Some(source), Some(point)));
            }

            CompletionContext::AfterSetOperator => {
                // Prioritize set-related completions
                completions.extend(self.get_expression_completions_with_context(
                    &symbols, &extended_modules, Some(source), Some(point)));
            }

            CompletionContext::AfterWith => {
                // Suggest parameter names from the target module (not implemented yet)
                completions.extend(self.get_expression_completions_with_context(
                    &symbols, &extended_modules, Some(source), Some(point)));
            }
        }

        // Sort by priority then alphabetically
        completions.sort_by(|a, b| {
            a.sort_priority.cmp(&b.sort_priority)
                .then_with(|| a.label.cmp(&b.label))
        });

        // Limit completions to prevent DoS from malicious files with many symbols
        // Set high enough to support large specifications (1000+ symbols)
        const MAX_COMPLETIONS: usize = 2000;
        completions.truncate(MAX_COMPLETIONS);

        completions
    }

    /// Get signature help for an operator call at the given position.
    pub fn get_signature_help(
        &self,
        result: &ParseResult,
        position: Position,
    ) -> Option<SignatureHelp> {
        let source = &result.source;

        let point = tree_sitter::Point {
            row: position.line as usize,
            column: position.column as usize,
        };

        // Find the function call from source text
        let (operator_name, active_param) = self.find_enclosing_call_from_source(source, point)?;

        // Get user-defined symbols for signature lookup
        let user_symbols = self.get_symbols(result);

        // Look up the signature (checks stdlib then user-defined)
        let signature = self.find_signature(&operator_name, &user_symbols)?;

        Some(SignatureHelp {
            signatures: vec![signature],
            active_signature: 0,
            active_parameter: active_param,
        })
    }
}

// Private helper methods (not exported via FFI)
impl TLACore {
    fn extract_diagnostics(&self, tree: &Tree, _source: &str) -> Vec<Diagnostic> {
        let mut diagnostics = vec![];
        let mut cursor = tree.walk();
        
        // Find ERROR and MISSING nodes
        loop {
            let node = cursor.node();
            
            if node.is_error() || node.is_missing() {
                diagnostics.push(Diagnostic {
                    range: Range {
                        start: Position {
                            line: node.start_position().row as u32,
                            column: node.start_position().column as u32,
                        },
                        end: Position {
                            line: node.end_position().row as u32,
                            column: node.end_position().column as u32,
                        },
                    },
                    severity: DiagnosticSeverity::Error,
                    message: if node.is_missing() {
                        format!("Missing: {}", node.kind())
                    } else {
                        "Syntax error".to_string()
                    },
                    code: None,
                });
            }
            
            // Traverse tree
            if cursor.goto_first_child() {
                continue;
            }
            while !cursor.goto_next_sibling() {
                if !cursor.goto_parent() {
                    return diagnostics;
                }
            }
        }
    }
    
    fn extract_symbols(&self, node: tree_sitter::Node, source: &str) -> Vec<Symbol> {
        let mut symbols = vec![];
        let mut cursor = node.walk();
        
        for child in node.children(&mut cursor) {
            match child.kind() {
                "module" => {
                    if let Some(name_node) = child.child_by_field_name("name") {
                        let name = name_node.utf8_text(source.as_bytes()).unwrap_or("").to_string();
                        symbols.push(Symbol {
                            name,
                            kind: SymbolKind::Module,
                            range: self.node_range(&child),
                            selection_range: Some(self.node_range(&name_node)),
                            children: self.extract_symbols(child, source),
                            parameters: vec![],
                        });
                    }
                }
                "operator_definition" => {
                    if let Some(name_node) = child.child_by_field_name("name") {
                        let name = name_node.utf8_text(source.as_bytes()).unwrap_or("").to_string();
                        // Extract parameters from operator definition
                        let mut parameters = Vec::new();
                        let mut param_cursor = child.walk();
                        for param_node in child.children_by_field_name("parameter", &mut param_cursor) {
                            if !param_node.is_named() {
                                continue;
                            }
                            match param_node.kind() {
                                "identifier" => {
                                    if let Ok(text) = param_node.utf8_text(source.as_bytes()) {
                                        parameters.push(text.to_string());
                                    }
                                }
                                "operator_declaration" => {
                                    // Higher-order params like f(_,_)
                                    if let Some(op_name) = param_node.child_by_field_name("name") {
                                        if let Ok(text) = op_name.utf8_text(source.as_bytes()) {
                                            parameters.push(text.to_string());
                                        }
                                    }
                                }
                                _ => {
                                    if let Ok(text) = param_node.utf8_text(source.as_bytes()) {
                                        parameters.push(text.to_string());
                                    }
                                }
                            }
                        }
                        symbols.push(Symbol {
                            name,
                            kind: SymbolKind::Operator,
                            range: self.node_range(&child),
                            selection_range: Some(self.node_range(&name_node)),
                            children: vec![],
                            parameters,
                        });
                    }
                }
                "variable_declaration" => {
                    for var in child.children_by_field_name("name", &mut child.walk()) {
                        let name = var.utf8_text(source.as_bytes()).unwrap_or("").to_string();
                        symbols.push(Symbol {
                            name,
                            kind: SymbolKind::Variable,
                            range: self.node_range(&var),
                            selection_range: None,
                            children: vec![],
                            parameters: vec![],
                        });
                    }
                }
                "constant_declaration" => {
                    for constant in child.children_by_field_name("name", &mut child.walk()) {
                        let name = constant.utf8_text(source.as_bytes()).unwrap_or("").to_string();
                        symbols.push(Symbol {
                            name,
                            kind: SymbolKind::Constant,
                            range: self.node_range(&constant),
                            selection_range: None,
                            children: vec![],
                            parameters: vec![],
                        });
                    }
                }
                "theorem" => {
                    if let Some(name_node) = child.child_by_field_name("name") {
                        let name = name_node.utf8_text(source.as_bytes()).unwrap_or("").to_string();
                        symbols.push(Symbol {
                            name,
                            kind: SymbolKind::Theorem,
                            range: self.node_range(&child),
                            selection_range: Some(self.node_range(&name_node)),
                            children: vec![],
                            parameters: vec![],
                        });
                    }
                }
                _ => {
                    // Recurse into other nodes
                    symbols.extend(self.extract_symbols(child, source));
                }
            }
        }
        
        symbols
    }
    
    fn node_range(&self, node: &tree_sitter::Node) -> Range {
        Range {
            start: Position {
                line: node.start_position().row as u32,
                column: node.start_position().column as u32,
            },
            end: Position {
                line: node.end_position().row as u32,
                column: node.end_position().column as u32,
            },
        }
    }

    // MARK: - Context Analysis Helpers

    /// Safely slice a string by byte offset, handling UTF-8 boundaries
    fn safe_slice_to_byte<'a>(&self, s: &'a str, byte_offset: usize) -> &'a str {
        if byte_offset >= s.len() {
            s
        } else if s.is_char_boundary(byte_offset) {
            &s[..byte_offset]
        } else {
            // Find the previous valid char boundary
            (0..byte_offset)
                .rev()
                .find(|&i| s.is_char_boundary(i))
                .map(|i| &s[..i])
                .unwrap_or("")
        }
    }

    /// Determine the completion context from source text and cursor position
    fn determine_context_from_source(
        &self,
        source: &str,
        point: tree_sitter::Point,
    ) -> CompletionContext {
        // Get the current line and context
        let line = source.lines().nth(point.row).unwrap_or("");
        // Use safe slicing to handle UTF-8 boundaries correctly
        let prefix = self.safe_slice_to_byte(line, point.column);
        let trimmed_prefix = prefix.trim();

        // Check for EXTENDS context
        if trimmed_prefix.starts_with("EXTENDS") && !trimmed_prefix.contains(',') {
            return CompletionContext::AfterExtends;
        }
        if prefix.contains("EXTENDS") {
            // Check if we're still in the extends list
            let after_extends = prefix.split("EXTENDS").last().unwrap_or("");
            if !after_extends.contains("VARIABLE") && !after_extends.contains("CONSTANT")
               && !after_extends.contains("==") {
                return CompletionContext::AfterExtends;
            }
        }

        // Check for INSTANCE context
        if trimmed_prefix.starts_with("INSTANCE") || prefix.contains("INSTANCE ") {
            if prefix.contains(" WITH ") {
                return CompletionContext::AfterWith;
            }
            return CompletionContext::AfterInstance;
        }

        // Check for proof context - look at surrounding lines (limited to 200 lines for performance)
        let lines: Vec<&str> = source.lines().collect();
        let mut in_proof = false;
        let start_row = point.row.min(lines.len().saturating_sub(1));
        let min_row = start_row.saturating_sub(200); // Limit backward scan to 200 lines
        for i in (min_row..=start_row).rev() {
            let l = lines[i].trim();
            if l.starts_with("PROOF") || l == "PROOF" {
                in_proof = true;
                break;
            }
            if l.starts_with("QED") || l == "QED" || l.starts_with("THEOREM")
               || l.starts_with("LEMMA") || l.contains("====") {
                break;
            }
        }
        if in_proof {
            return CompletionContext::InProof;
        }

        // Check for set operators
        if self.is_after_set_operator(source, point) {
            return CompletionContext::AfterSetOperator;
        }

        // Check for LET context
        if prefix.contains("LET ") {
            let after_let = prefix.split("LET").last().unwrap_or("");
            if !after_let.contains(" IN ") && !after_let.contains(" IN\n") {
                return CompletionContext::InLetDef;
            }
        }

        // Check if we're at top level
        let trimmed = line.trim();
        if trimmed.is_empty() {
            // Check previous non-empty lines (limit to 50 lines to prevent DoS)
            const MAX_LOOKBACK: usize = 50;
            let min_row = point.row.saturating_sub(MAX_LOOKBACK);
            for i in (min_row..point.row).rev() {
                if i < lines.len() {
                    let prev = lines[i].trim();
                    if prev.is_empty() {
                        continue;
                    }
                    // If previous line ends with definition continuation, we're in expression
                    if prev.ends_with("/\\") || prev.ends_with("\\/") || prev.ends_with("THEN")
                       || prev.ends_with("ELSE") || prev.ends_with("->") || prev.ends_with(",") {
                        return CompletionContext::InExpression;
                    }
                    break;
                }
            }
            return CompletionContext::TopLevel;
        }

        // If line doesn't have == yet, could be top-level
        if !line.contains("==") && !prefix.contains("\\in") && !prefix.contains("\\E")
           && !prefix.contains("\\A") && !prefix.contains("IF ") {
            // Check if this looks like a new definition
            let words: Vec<&str> = trimmed.split_whitespace().collect();
            if words.len() <= 2 && words.first().map(|w| w.chars().next().unwrap_or(' ').is_uppercase()).unwrap_or(false) {
                // Looks like starting a keyword at top level
                return CompletionContext::TopLevel;
            }
        }

        CompletionContext::InExpression
    }

    /// Check if the cursor is right after a set operator (\in, \subseteq, etc.)
    fn is_after_set_operator(&self, source: &str, point: tree_sitter::Point) -> bool {
        let line = source.lines().nth(point.row).unwrap_or("");
        // Use safe slicing to handle UTF-8 boundaries
        let prefix = self.safe_slice_to_byte(line, point.column);

        // Check for common set operators
        prefix.ends_with("\\in ")
            || prefix.ends_with("\\subseteq ")
            || prefix.ends_with("\\subset ")
            || prefix.ends_with("\\supseteq ")
            || prefix.ends_with("\\supset ")
    }

    /// Get extended modules from parse result (using source text parsing)
    fn get_extended_modules(&self, result: &ParseResult) -> Vec<String> {
        let source = &result.source;
        let mut modules = Vec::new();

        // Parse EXTENDS declarations from source using regex-like approach
        for line in source.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with("EXTENDS") {
                // Parse module names after EXTENDS
                let after_extends = trimmed.strip_prefix("EXTENDS").unwrap_or("").trim();
                for module_name in after_extends.split(',') {
                    let name = module_name.trim();
                    if !name.is_empty() && name.chars().next().map(|c| c.is_alphabetic()).unwrap_or(false) {
                        modules.push(name.to_string());
                    }
                }
            }
        }

        modules
    }

    /// Check if cursor position is inside a PlusCal algorithm block
    fn is_in_pluscal(&self, source: &str, point: tree_sitter::Point) -> bool {
        let mut in_algo = false;
        for (i, line) in source.lines().enumerate() {
            if i > point.row {
                break;
            }
            let trimmed = line.trim();
            if trimmed.contains("--algorithm") || trimmed.contains("--fair algorithm") {
                in_algo = true;
            }
            // Use starts_with to avoid false matches inside comments/strings
            if in_algo && trimmed.starts_with("end algorithm") {
                in_algo = false;
            }
        }
        in_algo
    }

    /// Get completions suitable for expression context
    fn get_expression_completions_with_context(
        &self,
        symbols: &[Symbol],
        extended_modules: &[String],
        source: Option<&str>,
        point: Option<tree_sitter::Point>,
    ) -> Vec<DetailedCompletionItem> {
        let mut completions = Vec::new();

        // Add keywords relevant to expressions
        completions.extend(DETAILED_KEYWORD_COMPLETIONS.iter()
            .filter(|k| {
                let label = k.label.as_str();
                matches!(label,
                    "IF" | "THEN" | "ELSE" | "CASE" | "OTHER" |
                    "LET" | "IN" | "CHOOSE" | "EXCEPT" | "DOMAIN" |
                    "SUBSET" | "UNION" | "ENABLED" | "UNCHANGED" |
                    "TRUE" | "FALSE" | "BOOLEAN"
                )
            })
            .cloned());

        // Add TLA+ operators
        completions.extend(TLA_OPERATORS.clone());

        // Add symbols from extended modules
        for module_name in extended_modules {
            if let Some(module) = STANDARD_MODULES.iter().find(|m| m.name == *module_name) {
                for sym in &module.symbols {
                    // Build documentation with example if available
                    let documentation = match &sym.example {
                        Some(example) => format!("{}\n\nExample:\n  {}", sym.doc, example),
                        None => sym.doc.clone(),
                    };

                    completions.push(DetailedCompletionItem {
                        label: sym.name.clone(),
                        kind: sym.kind,
                        detail: Some(format!("from {}", module_name)),
                        documentation: Some(documentation),
                        insert_text: None,
                        filter_text: None,
                        sort_priority: 8,
                        signature: sym.signature.clone(),
                    });
                }
            }
        }

        // Add user-defined symbols
        completions.extend(self.symbols_to_completions(symbols, 15));

        // Add snippet completions
        completions.extend(SNIPPET_COMPLETIONS.clone());

        // Add PlusCal keywords if inside algorithm block
        if let (Some(src), Some(pt)) = (source, point) {
            if self.is_in_pluscal(src, pt) {
                completions.extend(PLUSCAL_KEYWORDS.clone());
            }
        }

        completions
    }

    /// Convert parsed symbols to completion items
    fn symbols_to_completions(&self, symbols: &[Symbol], base_priority: u32) -> Vec<DetailedCompletionItem> {
        let mut completions = Vec::new();

        for symbol in symbols {
            let (kind, priority_offset) = match symbol.kind {
                SymbolKind::Operator => (CompletionKind::Function, 0),
                SymbolKind::Variable => (CompletionKind::Variable, 1),
                SymbolKind::Constant => (CompletionKind::Constant, 2),
                SymbolKind::Theorem => (CompletionKind::Theorem, 5),
                SymbolKind::Module => (CompletionKind::Module, 10),
                SymbolKind::Definition => (CompletionKind::Function, 0),
                SymbolKind::Instance => (CompletionKind::Module, 10),
                SymbolKind::Assumption => (CompletionKind::Constant, 8),
            };

            let signature = if !symbol.parameters.is_empty() {
                let param_list = symbol.parameters.join(", ");
                Some(format!("{}({})", symbol.name, param_list))
            } else {
                None
            };

            completions.push(DetailedCompletionItem {
                label: symbol.name.clone(),
                kind,
                detail: Some(format!("{:?}", symbol.kind)),
                documentation: None,
                insert_text: None,
                filter_text: None,
                sort_priority: base_priority + priority_offset,
                signature,
            });

            // Recurse into children
            completions.extend(self.symbols_to_completions(&symbol.children, base_priority));
        }

        completions
    }

    /// Find the enclosing function call and active parameter index (using source text)
    fn find_enclosing_call_from_source(
        &self,
        source: &str,
        point: tree_sitter::Point,
    ) -> Option<(String, u32)> {
        let line = source.lines().nth(point.row)?;
        // Use safe_slice_to_byte to avoid panic on multi-byte UTF-8 characters
        let prefix = self.safe_slice_to_byte(line, point.column);

        // Look backwards for an identifier followed by (
        // Track parentheses depth to find the function name
        let mut paren_depth = 0;
        let chars: Vec<char> = prefix.chars().collect();

        for i in (0..chars.len()).rev() {
            match chars[i] {
                ')' => paren_depth += 1,
                '(' => {
                    if paren_depth > 0 {
                        paren_depth -= 1;
                    } else {
                        // Found the opening paren of our call
                        // Look for identifier before this paren
                        let mut name_end = i;
                        while name_end > 0 && chars[name_end - 1].is_whitespace() {
                            name_end -= 1;
                        }
                        let mut name_start = name_end;
                        while name_start > 0 && (chars[name_start - 1].is_alphanumeric() || chars[name_start - 1] == '_') {
                            name_start -= 1;
                        }

                        if name_start < name_end {
                            let name: String = chars[name_start..name_end].iter().collect();
                            // Count commas at depth 0 only (ignoring nested parens/brackets)
                            let mut comma_count: u32 = 0;
                            let mut depth: i32 = 0;
                            for ch in chars[i + 1..].iter() {
                                match ch {
                                    '(' | '[' | '{' => depth += 1,
                                    ')' | ']' | '}' => depth = depth.saturating_sub(1),
                                    ',' if depth == 0 => comma_count += 1,
                                    _ => {}
                                }
                            }
                            return Some((name, comma_count));
                        }
                        break;
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Find signature information for an operator/function
    fn find_signature(&self, name: &str, user_symbols: &[Symbol]) -> Option<SignatureInfo> {
        // Check standard library first
        for module in STANDARD_MODULES.iter() {
            for sym in &module.symbols {
                if sym.name == name && !sym.parameters.is_empty() {
                    // Build documentation with example if available
                    let documentation = match &sym.example {
                        Some(example) => format!("{}\n\nExample:\n  {}", sym.doc, example),
                        None => sym.doc.clone(),
                    };

                    return Some(SignatureInfo {
                        label: sym.signature.clone().unwrap_or_else(|| format!("{}(...)", name)),
                        documentation: Some(documentation),
                        parameters: sym.parameters.iter()
                            .map(|p| ParameterInfo {
                                label: p.clone(),
                                documentation: None,
                            })
                            .collect(),
                    });
                }
            }
        }

        // Check user-defined symbols
        self.find_user_signature(name, user_symbols)
    }

    /// Search user-defined symbols for signature info
    fn find_user_signature(&self, name: &str, symbols: &[Symbol]) -> Option<SignatureInfo> {
        for symbol in symbols {
            if symbol.name == name && !symbol.parameters.is_empty() {
                let param_list = symbol.parameters.join(", ");
                let label = format!("{}({})", name, param_list);
                return Some(SignatureInfo {
                    label,
                    documentation: Some("User-defined operator".to_string()),
                    parameters: symbol.parameters.iter()
                        .map(|p| ParameterInfo {
                            label: p.clone(),
                            documentation: None,
                        })
                        .collect(),
                });
            }
            // Recurse into children
            if let Some(found) = self.find_user_signature(name, &symbol.children) {
                return Some(found);
            }
        }
        None
    }
}

// Note: Default impl removed to prevent panic on construction failure.
// Use TLACore::new() which returns Result<Self, ParseError> instead.
