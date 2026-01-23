# TLA+ Studio

<p align="center">
  <img src="TLAIcon.png" alt="TLA+ Studio Icon" width="128" height="128">
</p>

<p align="center">
  <strong>A native macOS IDE for TLA+ specifications</strong><br>
  Model checking, proof verification, and PlusCal translation with native Apple Silicon performance
</p>

---

## Features

### Editor
- **Syntax Highlighting** - Full TLA+ and PlusCal syntax support via tree-sitter
- **IntelliSense** - Code completion with documentation, signature help for operators
- **Go to Definition** - Jump to symbol definitions (Cmd+Click or F12)
- **Symbol Outline** - Navigate specs via sidebar symbol list
- **Code Folding** - Collapse modules, definitions, and proof blocks
- **Bracket Matching** - Automatic highlight of matching brackets
- **Multiple Themes** - Light and dark color schemes

### Model Checking (TLC)
- **Native TLC** - GraalVM-compiled TLC for fast startup (~100ms vs ~2s)
- **Model Configuration** - Visual editor for constants, invariants, properties
- **Live Progress** - Real-time state count, coverage, and queue depth
- **Error Traces** - Interactive trace explorer with state diff view
- **State Graph Visualization** - Graphviz-powered trace visualization
- **Large State Spaces** - Streaming trace storage for massive counterexamples
- **Checkpoints** - Save and resume long-running model checks

### Proof Verification (TLAPS)
- **Proof Obligations Panel** - Track obligation status (proved/failed/pending)
- **Inline Annotations** - Editor gutter shows proof status per line
- **Multiple Backends** - Z3, Zenon, Isabelle integration
- **Proof Progress** - Real-time progress during verification

### PlusCal
- **Translation** - Convert PlusCal algorithms to TLA+
- **Error Reporting** - Inline translation errors

---

## Screenshots

<p align="center">
  <img src="Screenshot 2026-01-17 at 11.21.03 AM.png" alt="TLA+ Studio Main Window" width="800">
</p>

---

## Requirements

### System Requirements
- **macOS 14.0+** (Sonoma or later)
- **Apple Silicon** (M1/M2/M3) or Intel Mac

### Prerequisites by Feature

| Feature | Required Tools | Installation |
|---------|---------------|--------------|
| **Editor** | None | Built-in |
| **Syntax Highlighting** | None | Built-in (tree-sitter) |
| **IntelliSense** | None | Built-in |
| **Model Checking (TLC)** | TLC Native Binary | See below |
| **Proof Verification** | TLAPM + backends | See below |
| **State Graph** | Graphviz | `brew install graphviz` |

### TLC Model Checker

TLA+ Studio uses a GraalVM native-image compiled TLC for fast startup. You need one of:

**Option A: Bundled Binary (Recommended)**
Place the native TLC binary in `Resources/`:
```
Resources/
├── tlc-native       # Standard GC version
└── tlc-native-fast  # Epsilon GC version (for small state spaces)
```

**Option B: Build from Source**
```bash
# Requires GraalVM with native-image
gu install native-image

# Build TLC native image
cd /path/to/tlaplus
./gradlew :tla2tools:nativeImage
cp tla2tools/build/native/nativeCompile/tlc ~/path/to/TLAStudio/Resources/tlc-native
```

**Option C: Custom Path**
Set a custom TLC path in **Preferences → Tools → TLC Path**

### TLAPM Proof System

For proof verification, you need TLAPM and its backend provers:

| Tool | Purpose | Installation |
|------|---------|--------------|
| **TLAPM** | Proof manager | Build from source or use bundled |
| **Z3** | SMT solver | `brew install z3` |
| **Zenon** | Theorem prover | Bundled with TLAPM |
| **Isabelle** | Proof assistant | Download via Preferences |

**Installing TLAPM (ARM64 macOS):**
```bash
# Install OCaml and dependencies
brew install opam
opam init
opam install dune

# Clone and build TLAPM
git clone https://github.com/tlaplus/tlapm.git
cd tlapm
dune build
dune install --prefix ~/.tlapm

# Set path in Preferences → Tools → TLAPM Path
```

**Installing Z3:**
```bash
brew install z3
# Or download from: https://github.com/Z3Prover/z3/releases
```

**Installing Isabelle (Optional):**
Isabelle can be downloaded directly from within TLA+ Studio:
1. Go to **Preferences → Tools**
2. Click **Download Isabelle**
3. Wait for download and extraction (~2GB)

### Graphviz (State Graph Visualization)

```bash
brew install graphviz
```

Or download from: https://graphviz.org/download/

### Quick Dependency Check

Run this to verify your setup:
```bash
# Check Graphviz
which dot && dot -V

# Check Z3
which z3 && z3 --version

# Check TLAPM (if installed)
which tlapm && tlapm --version
```

---

## Installation

### Download Release
Download the latest `.dmg` from [Releases](https://github.com/yourusername/TLAStudio/releases).

### Build from Source

#### Full Production Build (Recommended)

The production build script automatically installs all prerequisites and builds everything:

```bash
# Clone the repository
git clone https://github.com/yourusername/TLAStudio.git
cd TLAStudio

# Run full production build (installs prereqs, builds TLC, TLAPM, etc.)
./Scripts/build-production.sh

# Or with options:
./Scripts/build-production.sh --skip-prereqs  # Skip installing prerequisites
./Scripts/build-production.sh --dmg           # Also create DMG installer
./Scripts/build-production.sh --sign          # Code sign (requires Developer ID)
```

This will:
1. Install prerequisites (Homebrew, Rust, GraalVM, OCaml, Graphviz, Z3)
2. Build TLC native binary from source
3. Build TLAPM and proof backends
4. Build the Rust parser core
5. Build the Swift application
6. Create a complete `.app` bundle

#### Quick Development Build

If you already have prerequisites installed:

```bash
# Build Rust core
cd Sources/TLACore && cargo build --release && cd ../..

# Build and run
./Scripts/build-app.sh
open ".build/arm64-apple-macosx/debug/TLA+ Studio.app"
```

---

## Usage

### Creating a Specification

1. **File → New** (Cmd+N) to create a new TLA+ module
2. Write your specification with IntelliSense assistance
3. **File → Save** (Cmd+S) to save as `.tla` file

### Model Checking

1. Open a TLA+ specification
2. Click the **Model Check** tab in the sidebar
3. Configure constants and properties in the **Config** tab
4. Click **Run TLC** to start model checking
5. View results in **Results** tab, traces in **Trace** tab

### Proof Verification

1. Open a specification with TLAPS proofs
2. Click the **Proof** tab in the sidebar
3. Click **Check Proofs** to verify all obligations
4. View obligation status in the panel and editor gutter

### Keyboard Shortcuts

| Action | Shortcut |
|--------|----------|
| New Document | Cmd+N |
| Open | Cmd+O |
| Save | Cmd+S |
| Find | Cmd+F |
| Find & Replace | Cmd+Opt+F |
| Go to Definition | Cmd+Click or F12 |
| Trigger Completion | Ctrl+Space |
| Run TLC | Cmd+R |
| Stop TLC | Cmd+. |
| Fold All | Cmd+Opt+[ |
| Unfold All | Cmd+Opt+] |

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                TLA+ Studio (Swift/SwiftUI)                  │
│  Document Management │ Editor │ Model Check │ Proof UI     │
└──────────────────────────┬──────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────┐
│                 TLACore (Rust via UniFFI)                   │
│  tree-sitter Parser │ Symbols │ Completions │ Diagnostics  │
└──────────────────────────┬──────────────────────────────────┘
                           │ subprocess
┌──────────────────────────▼──────────────────────────────────┐
│                    Verification Tools                        │
│        TLC (Native) │ TLAPM │ Z3 │ Zenon │ Isabelle        │
└─────────────────────────────────────────────────────────────┘
```

### Key Components

| Component | Technology | Purpose |
|-----------|------------|---------|
| UI Layer | SwiftUI + AppKit | Native macOS interface |
| Document Model | NSDocument | File handling, auto-save |
| Parser | tree-sitter (Rust) | Incremental parsing, syntax |
| IntelliSense | Rust + Swift | Completions, signatures |
| Model Checker | TLC (GraalVM Native) | State space exploration |
| Proof Checker | TLAPM + backends | Formal verification |

---

## Development

### Project Structure

```
TLAStudio/
├── Sources/
│   ├── TLAStudioApp/          # Main Swift application
│   │   ├── App.swift          # Entry point
│   │   ├── Document/          # NSDocument, window controller
│   │   ├── Views/             # SwiftUI views, editor
│   │   ├── TLC/               # Model checking integration
│   │   └── Proof/             # TLAPS integration
│   │
│   ├── TLACore/               # Rust parser & analysis
│   │   └── src/lib.rs         # UniFFI exports
│   │
│   └── SourceEditor/          # Editor components
│
├── Scripts/
│   └── build-app.sh           # Build app bundle
│
├── Tests/
│   └── TLAStudioTests/        # Unit tests
│
└── Resources/                 # TLC binaries, icons
```

### Running Tests

```bash
# Run all tests
swift test

# Run specific test
swift test --filter TLAStudioTests.testDocumentCreation
```

### Building TLC Native

See `Docs/architecture/03-tlc-integration.md` for instructions on building TLC with GraalVM native-image.

---

## Contributing

Contributions are welcome! Please:

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'Add amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

---

## License

MIT License - see [LICENSE](LICENSE) for details.

---

## Acknowledgments

- [TLA+](https://lamport.azurewebsites.net/tla/tla.html) by Leslie Lamport
- [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus) grammar
- [TLC](https://github.com/tlaplus/tlaplus) model checker
- [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) proof system
