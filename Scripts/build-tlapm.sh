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

# Install the PTL translator too. TLAPM's default command for the LS4 backend is
# `ptl_to_trp -i $file | ls4`, so ls4 is useless without this companion binary —
# the pipe just feeds empty input to ls4 and every PTL obligation fails with
# `@!!reason:false`. Upstream dune ships it under two names
# (`translate/main.exe` and a `backends/bin/ptl_to_trp` symlink to the same thing);
# we keep both spellings in `bin/` so tlapm finds it regardless of which PATH
# directory it picks up first.
OUTPUT_BIN_DIR="$PROJECT_DIR/Sources/TLAStudioApp/Resources/bin"
if [ -f _build/default/translate/main.exe ]; then
    mkdir -p "$OUTPUT_BIN_DIR"
    cp _build/default/translate/main.exe "$OUTPUT_BIN_DIR/translate"
    cp _build/default/translate/main.exe "$OUTPUT_BIN_DIR/ptl_to_trp"
    chmod +x "$OUTPUT_BIN_DIR/translate" "$OUTPUT_BIN_DIR/ptl_to_trp"
    echo "Installed ptl_to_trp (PTL translator for ls4) into $OUTPUT_BIN_DIR"
else
    echo "Warning: _build/default/translate/main.exe not found; ls4/PTL backend will not work" >&2
fi

echo ""
echo "Built: $OUTPUT_DIR/tlapm"
ls -lh "$OUTPUT_DIR/tlapm"

# Test
echo ""
echo "Testing..."
"$OUTPUT_DIR/tlapm" --version && echo "✓ Success" || echo "✗ Failed"
