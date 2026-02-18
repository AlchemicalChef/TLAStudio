# TLAPS Integration Architecture

## Overview

TLAPS (TLA+ Proof System) enables writing and mechanically checking proofs of TLA+ specifications. This document covers the architecture for integrating TLAPS into TLA+ Studio.

## TLAPS Components

| Component | Type | Purpose |
|-----------|------|---------|
| TLAPM | OCaml binary | Proof manager - parses proofs, generates obligations, dispatches to backends |
| Zenon | OCaml binary | Default prover - tableau-based first-order logic |
| Z3 | C++ binary | SMT solver - arithmetic, arrays, bitvectors |
| Isabelle | Scala/ML | Interactive theorem prover - most powerful |
| LS4 | OCaml binary | Temporal logic prover |
| SPASS | C binary | First-order prover |

## System Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              TLA+ Studio Editor                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │  Proof Annotations Layer                                            │    │
│  │  ✓ Proved (green) │ ✗ Failed (red) │ ⋯ Pending (yellow)            │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │  Proof Obligations Panel                                            │    │
│  │  - Hierarchical proof tree                                          │    │
│  │  - Filter: All / Failed / Pending                                   │    │
│  │  - Click to navigate                                                │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
└────────────────────────────────────────┬────────────────────────────────────┘
                                         │ XPC
┌────────────────────────────────────────▼────────────────────────────────────┐
│                           TLAPS Service (XPC)                                │
│  - Parse proof structure                                                     │
│  - Track obligation states                                                   │
│  - Manage fingerprint cache                                                  │
│  - Coordinate backends                                                       │
└────────────────────────────────────────┬────────────────────────────────────┘
                                         │ subprocess
┌────────────────────────────────────────▼────────────────────────────────────┐
│                              TLAPM (OCaml)                                   │
│  Command: tlapm --toolbox 0 --threads N spec.tla                            │
│  Output: JSON stream of obligations                                          │
└────────────────────────────────────────┬────────────────────────────────────┘
                                         │
    ┌─────────────┬─────────────┬────────┴────────┬─────────────┬─────────────┐
    ▼             ▼             ▼                 ▼             ▼             ▼
┌───────┐   ┌─────────┐   ┌─────────┐       ┌─────────┐   ┌─────────┐   ┌───────┐
│ Zenon │   │   Z3    │   │Isabelle │       │   LS4   │   │  SPASS  │   │ cvc5  │
│(auto) │   │  (smt)  │   │  (isa)  │       │(temporal│   │  (fol)  │   │ (smt) │
└───────┘   └─────────┘   └─────────┘       └─────────┘   └─────────┘   └───────┘
```

## Data Models

### ProofObligation

```swift
struct ProofObligation: Identifiable, Codable {
    let id: UUID
    let fingerprint: String           // TLAPM fingerprint for caching
    let location: SourceLocation      // File, line, column range
    let kind: ObligationKind
    var status: ProofStatus
    var backend: ProverBackend?
    var duration: TimeInterval?
    var errorMessage: String?
    var parent: UUID?
    var children: [UUID]
    var obligationText: String
}
```

### ObligationKind

```swift
enum ObligationKind: String, Codable {
    case theorem
    case lemma
    case corollary
    case proposition
    case step           // Numbered: <1>, <2>
    case qed
    case assertion
    case suffices
    case case_
    case pick
    case have
    case take
    case witness
}
```

### ProofStatus

```swift
enum ProofStatus: String, Codable {
    case unknown        // Not yet checked
    case pending        // Currently checking
    case proved         // Success
    case failed         // Prover returned failure
    case timeout        // Prover timed out
    case omitted        // OMITTED in source
    case trivial        // BY OBVIOUS
}
```

### ProverBackend

```swift
enum ProverBackend: String, Codable, CaseIterable {
    case auto           // Let TLAPM choose
    case zenon          // Default, good for set theory
    case z3             // SMT, good for arithmetic
    case isabelle       // Most powerful, slowest
    case cvc5           // Alternative SMT
    case spass          // First-order
    case ls4            // Temporal logic
    
    var defaultTimeout: TimeInterval {
        switch self {
        case .zenon: return 10
        case .z3, .cvc5: return 15
        case .isabelle: return 30
        case .spass: return 20
        case .ls4: return 10
        case .auto: return 15
        }
    }
}
```

## XPC Service Protocol

```swift
@objc protocol TLAPSServiceProtocol {
    // Check all proofs
    func checkAllProofs(
        spec: URL,
        options: ProofCheckOptions,
        progressHandler: @escaping (ProofProgress) -> Void,
        reply: @escaping (ProofCheckResult?, Error?) -> Void
    )
    
    // Check single step (incremental)
    func checkProofStep(
        spec: URL,
        location: SourceLocation,
        backend: ProverBackend,
        timeout: TimeInterval,
        reply: @escaping (ProofStepResult) -> Void
    )
    
    // Cancel checking
    func cancelProofCheck(id: UUID)
    
    // Parse structure without checking
    func parseProofStructure(
        spec: URL,
        reply: @escaping ([ProofObligation]) -> Void
    )
    
    // Cache operations
    func getCachedResults(
        for fingerprints: [String],
        reply: @escaping ([String: ProofStatus]) -> Void
    )
    
    func clearProofCache(
        for spec: URL?,
        reply: @escaping (Bool) -> Void
    )
}
```

## Building TLAPM for ARM64

```bash
#!/bin/bash
# Scripts/build-tlapm.sh

# Prerequisites
brew install opam

# Initialize opam
opam init --bare
opam switch create tlapm ocaml-base-compiler.4.14.1
eval $(opam env)

# Install dependencies
opam install dune ocamlfind camlzip

# Clone and build
git clone https://github.com/tlaplus/tlapm.git
cd tlapm
dune build

# Copy to bundle
cp _build/default/src/tlapm.exe ../Resources/Provers/tlapm
```

## Building Backend Provers

```bash
#!/bin/bash
# Scripts/build-provers.sh

PROVERS_DIR="Resources/Provers"

# Z3 - download pre-built
curl -LO https://github.com/Z3Prover/z3/releases/download/z3-4.15.0/z3-4.15.0-arm64-osx.zip
unzip z3-*.zip
cp z3-*/bin/z3 $PROVERS_DIR/

# Zenon - build from source
git clone https://github.com/zenon-prover/zenon
cd zenon && ./configure && make
cp zenon $PROVERS_DIR/
cd ..

# SPASS - build from source
wget http://www.spass-prover.org/download/sources/spass39.tgz
tar xzf spass39.tgz && cd spass39
make CFLAGS="-arch arm64"
cp SPASS $PROVERS_DIR/
cd ..
```

## Proof Cache

Proofs are cached by fingerprint to avoid re-checking unchanged obligations.

```
~/Library/Application Support/TLAStudio/ProofCache/
├── ab/
│   ├── ab12cd34...json
│   └── ab98ef76...json
├── cd/
│   └── cd45...json
└── index.json
```

Cache entry:
```json
{
  "fingerprint": "ab12cd34...",
  "status": "proved",
  "backend": "zenon",
  "timestamp": "2025-01-15T...",
  "duration": 0.234
}
```

## Editor Annotations

### Status Colors

| Status | Gutter Icon | Background |
|--------|-------------|------------|
| Proved | ✓ green | rgba(0,255,0,0.1) |
| Failed | ✗ red | rgba(255,0,0,0.15) |
| Pending | ⋯ yellow | rgba(255,255,0,0.1) |
| Timeout | ⏰ orange | rgba(255,165,0,0.1) |
| Omitted | ○ gray | transparent |
| Trivial | ✨ green | rgba(0,255,0,0.05) |

### Keyboard Shortcuts

| Shortcut | Action |
|----------|--------|
| ⇧⌘P | Check All Proofs |
| ⌘P | Check Current Step |
| ⌥⌘P | Check to Cursor |
| ⌘. | Stop Checking |
| ⌘' | Go to Next Failed |
| ⇧⌘' | Go to Previous Failed |

## Implementation Checklist

- [ ] Create `TLAPMRunner.swift` - process spawning and output parsing
- [ ] Create `ProofObligation.swift` - data models
- [ ] Create `ProofCache.swift` - fingerprint cache with disk persistence
- [ ] Create `TLAPSServiceProtocol.swift` - XPC protocol
- [ ] Create `ProofAnnotationManager.swift` - editor integration
- [ ] Create `ProofObligationsPanel.swift` - SwiftUI panel
- [ ] Add `Scripts/build-tlapm.sh`
- [ ] Add `Scripts/build-provers.sh`
- [ ] Test with simple proofs
- [ ] Test with Isabelle integration
- [ ] Test cache hit/miss scenarios

## Backend Selection Heuristics

```swift
func selectBackend(for obligation: ProofObligation) -> ProverBackend {
    let text = obligation.obligationText.lowercased()
    
    // Temporal logic → LS4
    if text.contains("[]") || text.contains("<>") || text.contains("~>") {
        return .ls4
    }
    
    // Heavy arithmetic → SMT
    if text.contains("\\in nat") || text.contains("\\in int") {
        return .z3
    }
    
    // Set theory → Zenon
    if text.contains("\\in") || text.contains("\\subseteq") {
        return .zenon
    }
    
    // Default
    return .auto
}
```

## Parallel Checking Strategy

1. Parse all obligations
2. Sort by estimated difficulty (simpler first)
3. Dispatch up to N parallel provers
4. First success cancels other attempts for same obligation
5. Cache successful proofs
6. Report progress in real-time
