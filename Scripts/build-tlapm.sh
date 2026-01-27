#!/bin/bash
# Build TLAPM from source for ARM64 macOS

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
OUTPUT_DIR="$PROJECT_DIR/Sources/TLAStudioApp/Resources/Provers"

echo "=== Building TLAPM ==="

# Prerequisites check
if ! command -v opam &> /dev/null; then
    echo "Installing opam..."
    brew install opam
fi

# Initialize opam if needed
if [ ! -d "$HOME/.opam" ]; then
    opam init --bare --yes
fi

# Create switch for TLAPM
opam switch create tlapm ocaml-base-compiler.4.14.1 --yes 2>/dev/null || opam switch tlapm
eval $(opam env --switch=tlapm)

# Install dependencies
opam install dune ocamlfind camlzip --yes

# Clone TLAPM
TLAPM_DIR="$SCRIPT_DIR/tlapm"
if [ ! -d "$TLAPM_DIR" ]; then
    git clone https://github.com/tlaplus/tlapm.git "$TLAPM_DIR"
fi

cd "$TLAPM_DIR"
git pull

# Build
dune build

# Copy binary
mkdir -p "$OUTPUT_DIR"
cp _build/default/src/tlapm.exe "$OUTPUT_DIR/tlapm"
chmod +x "$OUTPUT_DIR/tlapm"

echo ""
echo "Built: $OUTPUT_DIR/tlapm"
ls -lh "$OUTPUT_DIR/tlapm"

# Test
echo ""
echo "Testing..."
"$OUTPUT_DIR/tlapm" --version && echo "✓ Success" || echo "✗ Failed"
