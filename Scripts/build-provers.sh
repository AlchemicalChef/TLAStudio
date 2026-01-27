#!/bin/bash
# Download and build backend provers for TLAPS
# Provers: Z3, CVC5, Zenon, Isabelle, SPASS

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
OUTPUT_DIR="$PROJECT_DIR/Sources/TLAStudioApp/Resources/Provers"
ARCH=$(uname -m)

echo "=== Building/Downloading Backend Provers ==="
echo "Architecture: $ARCH"

mkdir -p "$OUTPUT_DIR"
cd "$OUTPUT_DIR"

# Z3 - download pre-built
echo ""
echo "=== Z3 ==="
Z3_VERSION="4.13.4"
if [ "$ARCH" = "arm64" ]; then
    Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-arm64-osx-13.7.zip"
else
    Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-osx-13.7.zip"
fi

if [ ! -f "z3" ]; then
    echo "Downloading Z3 ${Z3_VERSION}..."
    curl -L -o z3.zip "$Z3_URL"
    unzip -o z3.zip
    cp z3-*/bin/z3 .
    rm -rf z3.zip z3-*/
    chmod +x z3
fi
echo "Z3: $(./z3 --version 2>&1 | head -1)"

# CVC5 - download pre-built
echo ""
echo "=== CVC5 ==="
CVC5_VERSION="1.2.0"
if [ "$ARCH" = "arm64" ]; then
    CVC5_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-macOS-arm64-static.zip"
else
    CVC5_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-macOS-x86_64-static.zip"
fi

if [ ! -f "cvc5" ]; then
    echo "Downloading CVC5 ${CVC5_VERSION}..."
    curl -L -o cvc5.zip "$CVC5_URL"
    unzip -o cvc5.zip
    mv cvc5-*/bin/cvc5 . 2>/dev/null || mv cvc5-*/cvc5 .
    rm -rf cvc5.zip cvc5-*/
    chmod +x cvc5
fi
echo "CVC5: $(./cvc5 --version 2>&1 | head -1)"

# Zenon - download pre-built from TLAPM releases or build from source
echo ""
echo "=== Zenon ==="
if [ ! -f "zenon" ]; then
    # Try to download pre-built zenon from TLAPM release assets
    ZENON_URL="https://github.com/tlaplus/tlapm/releases/download/202210041448/zenon-0.8.5-${ARCH}-darwin.tar.gz"

    if curl -fL -o zenon.tar.gz "$ZENON_URL" 2>/dev/null; then
        echo "Downloaded pre-built Zenon"
        tar -xzf zenon.tar.gz
        mv zenon-*/zenon . 2>/dev/null || mv zenon . 2>/dev/null || true
        rm -rf zenon.tar.gz zenon-*/
    else
        echo "Building Zenon from source..."
        # Build from source requires OCaml
        if ! command -v opam &> /dev/null; then
            echo "Installing opam for Zenon build..."
            brew install opam
        fi

        if [ ! -d "$HOME/.opam" ]; then
            opam init --bare --yes
        fi

        opam switch create zenon-build ocaml-base-compiler.4.14.1 --yes 2>/dev/null || opam switch zenon-build
        eval $(opam env --switch=zenon-build)

        ZENON_SRC="$SCRIPT_DIR/zenon-src"
        if [ ! -d "$ZENON_SRC" ]; then
            git clone https://github.com/zenon-prover/zenon.git "$ZENON_SRC"
        fi
        cd "$ZENON_SRC"
        ./configure --prefix="$OUTPUT_DIR"
        make
        cp zenon "$OUTPUT_DIR/"
        cd "$OUTPUT_DIR"
        rm -rf "$ZENON_SRC"
    fi
    chmod +x zenon
fi
echo "Zenon: $(./zenon -v 2>&1 | head -1 || echo 'installed')"

# Isabelle - download pre-built
echo ""
echo "=== Isabelle ==="
ISABELLE_VERSION="Isabelle2024"
if [ ! -d "isabelle" ]; then
    echo "Downloading Isabelle (this may take a while, ~1GB)..."

    if [ "$ARCH" = "arm64" ]; then
        ISABELLE_URL="https://isabelle.in.tum.de/website-${ISABELLE_VERSION}/dist/${ISABELLE_VERSION}_macos_arm64.tar.gz"
    else
        ISABELLE_URL="https://isabelle.in.tum.de/website-${ISABELLE_VERSION}/dist/${ISABELLE_VERSION}_macos.tar.gz"
    fi

    curl -L -o isabelle.tar.gz "$ISABELLE_URL"
    tar -xzf isabelle.tar.gz

    # Rename extracted directory
    mv ${ISABELLE_VERSION}* isabelle 2>/dev/null || mv Isabelle* isabelle 2>/dev/null || true
    rm -f isabelle.tar.gz

    # Create wrapper script that TLAPM expects
    cat > isabelle-wrapper << 'WRAPPER'
#!/bin/bash
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
exec "$SCRIPT_DIR/isabelle/bin/isabelle" "$@"
WRAPPER
    chmod +x isabelle-wrapper

    echo "Isabelle installed. Building required Isabelle/TLA+ heap..."
    # Note: TLAPM requires the TLA+ heap to be built, which happens on first use
fi

if [ -d "isabelle" ]; then
    echo "Isabelle: $(./isabelle/bin/isabelle version 2>&1 || echo 'installed')"
else
    echo "Isabelle: installation failed"
fi

# SPASS - download or build
echo ""
echo "=== SPASS ==="
if [ ! -f "SPASS" ]; then
    # Try pre-built first
    SPASS_URL="https://www.mpi-inf.mpg.de/fileadmin/inf/rg1/spass/SPASS-3.9-macOS.tar.gz"

    if curl -fL -o spass.tar.gz "$SPASS_URL" 2>/dev/null; then
        echo "Downloaded pre-built SPASS"
        tar -xzf spass.tar.gz
        # Find and copy the SPASS binary
        find . -name "SPASS" -type f -exec cp {} . \; 2>/dev/null || true
        rm -rf spass.tar.gz SPASS-*/
    else
        echo "Building SPASS from source..."
        SPASS_SRC="$SCRIPT_DIR/spass-src"

        # Download SPASS source
        curl -L -o spass-src.tgz "https://www.mpi-inf.mpg.de/fileadmin/inf/rg1/spass/spass39.tgz"
        mkdir -p "$SPASS_SRC"
        tar -xzf spass-src.tgz -C "$SPASS_SRC" --strip-components=1
        rm spass-src.tgz

        cd "$SPASS_SRC"
        make
        cp SPASS "$OUTPUT_DIR/"
        cd "$OUTPUT_DIR"
        rm -rf "$SPASS_SRC"
    fi

    if [ -f "SPASS" ]; then
        chmod +x SPASS
    fi
fi

if [ -f "SPASS" ]; then
    echo "SPASS: $(./SPASS 2>&1 | head -1 || echo 'installed')"
else
    echo "SPASS: not installed (optional)"
fi

# LS4 - temporal logic prover (optional, used by some TLAPM proofs)
echo ""
echo "=== LS4 (optional) ==="
if [ ! -f "ls4" ]; then
    # LS4 may need to be built from source
    echo "LS4: skipped (build from source if needed)"
fi

echo ""
echo "=== Summary ==="
echo "Provers directory: $OUTPUT_DIR"
echo ""
ls -lh "$OUTPUT_DIR" 2>/dev/null | grep -v "^total" | grep -v "^d" || true
echo ""

# List directories (like isabelle)
DIRS=$(find "$OUTPUT_DIR" -maxdepth 1 -type d ! -path "$OUTPUT_DIR" 2>/dev/null)
if [ -n "$DIRS" ]; then
    echo "Directories:"
    for dir in $DIRS; do
        echo "  $(basename "$dir")/ (~$(du -sh "$dir" 2>/dev/null | cut -f1))"
    done
fi

echo ""
echo "=== Prover Status ==="
[ -f "$OUTPUT_DIR/z3" ] && echo "  [x] Z3" || echo "  [ ] Z3"
[ -f "$OUTPUT_DIR/cvc5" ] && echo "  [x] CVC5" || echo "  [ ] CVC5"
[ -f "$OUTPUT_DIR/zenon" ] && echo "  [x] Zenon" || echo "  [ ] Zenon"
[ -d "$OUTPUT_DIR/isabelle" ] && echo "  [x] Isabelle" || echo "  [ ] Isabelle"
[ -f "$OUTPUT_DIR/SPASS" ] && echo "  [x] SPASS" || echo "  [ ] SPASS"
[ -f "$OUTPUT_DIR/ls4" ] && echo "  [x] LS4" || echo "  [ ] LS4 (optional)"
