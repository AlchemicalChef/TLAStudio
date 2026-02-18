# Language Intelligence Architecture

## Overview

Phase 2 adds LSP-like features using tree-sitter for parsing and Rust for core logic, exposed to Swift via UniFFI.

## Features

| Feature | Description | Implementation |
|---------|-------------|----------------|
| Syntax Highlighting | Token-based coloring | tree-sitter queries |
| Diagnostics | Real-time error detection | tree-sitter ERROR nodes |
| Symbol Outline | Document structure | tree-sitter traversal |
| Go to Definition | Jump to declaration | Symbol index lookup |
| Hover | Documentation on hover | Symbol metadata |
| Completions | Context-aware suggestions | Scope analysis |
| Code Folding | Collapse blocks | tree-sitter node ranges |

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         Swift UI Layer                          │
│  SourceEditor │ SymbolOutline │ DiagnosticsPanel │ HoverPopup  │
└────────────────────────────────┬────────────────────────────────┘
                                 │ UniFFI
┌────────────────────────────────▼────────────────────────────────┐
│                      TLACore (Rust)                              │
│  ┌──────────────┐  ┌──────────────┐  ┌────────────────────────┐ │
│  │ TLAParser    │  │ SymbolIndex  │  │ CompletionProvider     │ │
│  │ (tree-sitter)│  │ (in-memory)  │  │ (context-aware)        │ │
│  └──────────────┘  └──────────────┘  └────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

## Tree-sitter Integration

### Grammar

Use existing grammar: `tree-sitter-tlaplus`

```toml
# Cargo.toml
[dependencies]
tree-sitter = "0.24"
tree-sitter-tlaplus = { git = "https://github.com/tlaplus-community/tree-sitter-tlaplus" }
```

### Incremental Parsing

```rust
impl TLAParser {
    pub fn parse_incremental(
        &mut self,
        source: &str,
        old_tree: Option<&Tree>,
        edit: Option<&InputEdit>,
    ) -> Tree {
        if let (Some(tree), Some(edit)) = (old_tree, edit) {
            let mut tree = tree.clone();
            tree.edit(edit);
            self.parser.parse(source, Some(&tree)).unwrap()
        } else {
            self.parser.parse(source, None).unwrap()
        }
    }
}
```

### Highlight Queries

```scheme
; Keywords
["CONSTANT" "CONSTANTS" "VARIABLE" "VARIABLES"] @keyword
["EXTENDS" "INSTANCE" "LOCAL"] @keyword.import
["THEOREM" "LEMMA" "PROPOSITION" "COROLLARY"] @keyword.theorem
["PROOF" "BY" "OBVIOUS" "OMITTED" "QED"] @keyword.proof

; Operators
["==" "=" "\\in" "\\notin" "\\subseteq"] @operator
["/\\" "\\/" "~" "=>"] @operator.logical
["[]" "<>" "~>"] @operator.temporal

; Identifiers
(identifier) @variable
(operator_definition name: (identifier) @function)
(constant_declaration name: (identifier) @constant)

; Literals
(string) @string
(number) @number

; Comments
(comment) @comment
(block_comment) @comment
```

## Symbol Index

### Data Structure

```rust
pub struct SymbolIndex {
    /// Module-level symbols
    modules: HashMap<String, ModuleSymbols>,
    
    /// Cross-reference index (name -> locations)
    references: HashMap<String, Vec<SourceLocation>>,
}

pub struct ModuleSymbols {
    pub name: String,
    pub path: PathBuf,
    pub operators: Vec<OperatorSymbol>,
    pub variables: Vec<VariableSymbol>,
    pub constants: Vec<ConstantSymbol>,
    pub theorems: Vec<TheoremSymbol>,
    pub instances: Vec<InstanceSymbol>,
}

pub struct OperatorSymbol {
    pub name: String,
    pub arity: usize,
    pub parameters: Vec<String>,
    pub location: SourceLocation,
    pub doc_comment: Option<String>,
    pub is_recursive: bool,
}
```

### Building the Index

```rust
impl SymbolIndex {
    pub fn index_module(&mut self, path: &Path, tree: &Tree, source: &str) {
        let mut cursor = tree.walk();
        
        // Extract module name
        // Extract EXTENDS
        // Extract operators, variables, constants
        // Extract theorems
        // Build cross-references
    }
    
    pub fn find_definition(&self, name: &str, from_module: &str) -> Option<&SourceLocation> {
        // 1. Check local module
        // 2. Check EXTENDS chain
        // 3. Check INSTANCE imports
    }
}
```

## Go to Definition

```rust
pub fn go_to_definition(
    &self,
    document: &str,
    position: Position,
) -> Option<SourceLocation> {
    // 1. Find node at position
    let node = self.node_at_position(position)?;
    
    // 2. Get identifier name
    let name = node.utf8_text(document.as_bytes()).ok()?;
    
    // 3. Determine context (is it a reference?)
    if !self.is_reference_context(&node) {
        return None;
    }
    
    // 4. Look up in symbol index
    self.symbol_index.find_definition(name, &self.current_module)
}
```

## Hover Documentation

```rust
pub fn hover(&self, document: &str, position: Position) -> Option<HoverInfo> {
    let node = self.node_at_position(position)?;
    let name = node.utf8_text(document.as_bytes()).ok()?;
    
    // Find symbol
    let symbol = self.symbol_index.find_symbol(name)?;
    
    Some(HoverInfo {
        content: format_symbol_docs(symbol),
        range: node_to_range(&node),
    })
}

fn format_symbol_docs(symbol: &Symbol) -> String {
    match symbol {
        Symbol::Operator(op) => {
            let params = op.parameters.join(", ");
            let mut doc = format!("```tla\n{}({}) == ...\n```", op.name, params);
            if let Some(comment) = &op.doc_comment {
                doc.push_str("\n\n");
                doc.push_str(comment);
            }
            doc
        }
        // ... other cases
    }
}
```

## Completions

### Context Detection

```rust
enum CompletionContext {
    TopLevel,           // Module body
    AfterExtends,       // After EXTENDS keyword
    AfterIn,            // After \in (expect set)
    Expression,         // General expression
    Proof,              // Inside PROOF block
    Action,             // After prime (')
}

fn detect_context(node: &Node, position: Position) -> CompletionContext {
    // Walk up tree to determine context
}
```

### Completion Sources

```rust
pub fn get_completions(&self, context: CompletionContext) -> Vec<CompletionItem> {
    match context {
        CompletionContext::TopLevel => {
            vec![
                keywords(),           // VARIABLE, CONSTANT, etc.
                local_operators(),    // Defined in this module
                extended_symbols(),   // From EXTENDS
            ].concat()
        }
        CompletionContext::AfterExtends => {
            available_modules()       // Naturals, Sequences, etc.
        }
        CompletionContext::Expression => {
            vec![
                local_symbols(),
                standard_operators(), // \in, \cup, etc.
                temporal_operators(), // [], <>, ~>
            ].concat()
        }
        // ...
    }
}
```

### Snippet Completions

```rust
fn snippet_completions() -> Vec<CompletionItem> {
    vec![
        CompletionItem {
            label: "VARIABLE".to_string(),
            insert_text: Some("VARIABLE ${1:name}".to_string()),
            kind: CompletionKind::Snippet,
        },
        CompletionItem {
            label: "operator".to_string(),
            insert_text: Some("${1:Name} == \n    ${2:expression}".to_string()),
            kind: CompletionKind::Snippet,
        },
        CompletionItem {
            label: "ifthenelse".to_string(),
            insert_text: Some("IF ${1:condition}\nTHEN ${2:then}\nELSE ${3:else}".to_string()),
            kind: CompletionKind::Snippet,
        },
    ]
}
```

## Code Folding

```rust
pub fn get_folding_ranges(&self, tree: &Tree) -> Vec<FoldingRange> {
    let mut ranges = vec![];
    
    // Query for foldable constructs
    let query = Query::new(language, r#"
        (module) @module
        (operator_definition) @operator
        (proof) @proof
        (block_comment) @comment
        (pluscal_algorithm) @pluscal
    "#)?;
    
    let mut cursor = QueryCursor::new();
    for match_ in cursor.matches(&query, tree.root_node(), source.as_bytes()) {
        let node = match_.captures[0].node;
        if node.end_position().row > node.start_position().row {
            ranges.push(FoldingRange {
                start_line: node.start_position().row,
                end_line: node.end_position().row,
                kind: match_.pattern_index.into(),
            });
        }
    }
    
    ranges
}
```

## Diagnostics

### Error Detection

```rust
pub fn get_diagnostics(&self, tree: &Tree, source: &str) -> Vec<Diagnostic> {
    let mut diagnostics = vec![];
    
    // 1. Syntax errors (ERROR nodes)
    collect_syntax_errors(tree, &mut diagnostics);
    
    // 2. Missing nodes
    collect_missing_nodes(tree, &mut diagnostics);
    
    // 3. Semantic warnings (optional)
    // - Unused variables
    // - Undefined references
    // - Shadowed names
    
    diagnostics
}

fn collect_syntax_errors(tree: &Tree, diagnostics: &mut Vec<Diagnostic>) {
    let mut cursor = tree.walk();
    loop {
        let node = cursor.node();
        if node.is_error() {
            diagnostics.push(Diagnostic {
                range: node_to_range(&node),
                severity: DiagnosticSeverity::Error,
                message: "Syntax error".to_string(),
                code: Some("E001".to_string()),
            });
        }
        // Traverse...
    }
}
```

## UniFFI Interface

```rust
// Already in lib.rs, extend with:

#[uniffi::export]
impl TLACore {
    /// Get completions at position
    pub fn get_completions(
        &self,
        result: &ParseResult,
        position: Position,
    ) -> Vec<CompletionItem>;
    
    /// Get hover info at position
    pub fn get_hover(
        &self,
        result: &ParseResult,
        position: Position,
    ) -> Option<HoverInfo>;
    
    /// Go to definition
    pub fn go_to_definition(
        &self,
        result: &ParseResult,
        position: Position,
    ) -> Option<SourceLocation>;
    
    /// Get folding ranges
    pub fn get_folding_ranges(
        &self,
        result: &ParseResult,
    ) -> Vec<FoldingRange>;
    
    /// Find all references
    pub fn find_references(
        &self,
        result: &ParseResult,
        position: Position,
    ) -> Vec<SourceLocation>;
}
```

## Implementation Checklist

- [ ] Integrate tree-sitter-tlaplus grammar
- [ ] Implement incremental parsing
- [ ] Create highlight queries
- [ ] Build SymbolIndex
- [ ] Implement go_to_definition
- [ ] Implement hover
- [ ] Implement completions with context detection
- [ ] Implement code folding
- [ ] Add semantic diagnostics
- [ ] Wire up UniFFI bindings
- [ ] Integrate with SourceEditor
- [ ] Add symbol outline panel
