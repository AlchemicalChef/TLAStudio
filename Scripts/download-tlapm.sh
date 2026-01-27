#!/bin/bash
# Download pre-built TLAPM binary for macOS ARM64
# This script downloads TLAPM from official releases instead of building from source

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
OUTPUT_BIN_DIR="$PROJECT_DIR/Sources/TLAStudioApp/Resources/bin"
OUTPUT_LIB_DIR="$PROJECT_DIR/Sources/TLAStudioApp/Resources/lib/tlapm"
ARCH=$(uname -m)

echo "=== Downloading TLAPM ==="
echo "Architecture: $ARCH"

# TLAPM version to download
TLAPM_VERSION="202210041448"

# Create output directories
mkdir -p "$OUTPUT_BIN_DIR"
mkdir -p "$OUTPUT_LIB_DIR"

# Download URL for macOS ARM64
# Note: TLAPM releases are from the tlaplus/tlapm repository
if [ "$ARCH" = "arm64" ]; then
    # ARM64 macOS - check for native build or use Rosetta-compatible x86_64
    TLAPM_URL="https://github.com/tlaplus/tlapm/releases/download/${TLAPM_VERSION}/tlapm-${TLAPM_VERSION}-arm64-darwin-gnu.tar.gz"
    TLAPM_FALLBACK_URL="https://github.com/tlaplus/tlapm/releases/download/${TLAPM_VERSION}/tlapm-${TLAPM_VERSION}-x86_64-darwin-gnu.tar.gz"
else
    TLAPM_URL="https://github.com/tlaplus/tlapm/releases/download/${TLAPM_VERSION}/tlapm-${TLAPM_VERSION}-x86_64-darwin-gnu.tar.gz"
    TLAPM_FALLBACK_URL=""
fi

# Download TLAPM
TEMP_DIR=$(mktemp -d)
cd "$TEMP_DIR"

echo "Downloading TLAPM..."
if ! curl -fL -o tlapm.tar.gz "$TLAPM_URL" 2>/dev/null; then
    if [ -n "$TLAPM_FALLBACK_URL" ]; then
        echo "ARM64 build not found, trying x86_64 (Rosetta)..."
        curl -fL -o tlapm.tar.gz "$TLAPM_FALLBACK_URL"
    else
        echo "Error: Failed to download TLAPM"
        exit 1
    fi
fi

echo "Extracting..."
tar -xzf tlapm.tar.gz

# Find the extracted directory
TLAPM_EXTRACTED=$(find . -maxdepth 1 -type d -name "tlapm-*" | head -1)
if [ -z "$TLAPM_EXTRACTED" ]; then
    TLAPM_EXTRACTED=$(find . -maxdepth 1 -type d ! -name "." | head -1)
fi

if [ -z "$TLAPM_EXTRACTED" ]; then
    echo "Error: Could not find extracted TLAPM directory"
    ls -la
    exit 1
fi

echo "Found TLAPM at: $TLAPM_EXTRACTED"

# Copy binary
if [ -f "$TLAPM_EXTRACTED/bin/tlapm" ]; then
    cp "$TLAPM_EXTRACTED/bin/tlapm" "$OUTPUT_BIN_DIR/tlapm"
elif [ -f "$TLAPM_EXTRACTED/tlapm" ]; then
    cp "$TLAPM_EXTRACTED/tlapm" "$OUTPUT_BIN_DIR/tlapm"
else
    echo "Error: Could not find tlapm binary"
    find "$TLAPM_EXTRACTED" -type f -name "tlapm*"
    exit 1
fi
chmod +x "$OUTPUT_BIN_DIR/tlapm"

# Copy standard library
if [ -d "$TLAPM_EXTRACTED/lib/tlapm" ]; then
    cp -R "$TLAPM_EXTRACTED/lib/tlapm/"* "$OUTPUT_LIB_DIR/"
elif [ -d "$TLAPM_EXTRACTED/lib/tlaps" ]; then
    cp -R "$TLAPM_EXTRACTED/lib/tlaps/"* "$OUTPUT_LIB_DIR/"
elif [ -d "$TLAPM_EXTRACTED/stdlib" ]; then
    mkdir -p "$OUTPUT_LIB_DIR/stdlib"
    cp -R "$TLAPM_EXTRACTED/stdlib/"* "$OUTPUT_LIB_DIR/stdlib/"
fi

# Cleanup
cd "$PROJECT_DIR"
rm -rf "$TEMP_DIR"

# Verify
echo ""
echo "=== Verification ==="
echo "TLAPM binary: $OUTPUT_BIN_DIR/tlapm"
ls -lh "$OUTPUT_BIN_DIR/tlapm"

echo ""
echo "TLAPM library: $OUTPUT_LIB_DIR"
ls -la "$OUTPUT_LIB_DIR" 2>/dev/null || echo "(empty)"

echo ""
echo "Testing TLAPM..."
if "$OUTPUT_BIN_DIR/tlapm" --version 2>/dev/null; then
    echo "TLAPM download successful!"
else
    echo "Warning: Could not verify TLAPM binary"
    echo "This may be due to missing dependencies or architecture mismatch"
    file "$OUTPUT_BIN_DIR/tlapm"
fi
