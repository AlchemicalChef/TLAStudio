#!/bin/bash
# Build TLACore Rust library and generate Swift bindings via UniFFI

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
RUST_DIR="$PROJECT_DIR/Sources/TLACore"
OUTPUT_DIR="$PROJECT_DIR/build/TLACore"
SWIFT_BINDINGS_DIR="$PROJECT_DIR/Sources/TLAStudioApp/TLACore"

echo "=== Building TLACore (Rust) ==="

# Check Rust toolchain
if ! command -v cargo &> /dev/null; then
    echo "Error: Rust not installed. Install via: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    exit 1
fi

# Ensure ARM64 target
rustup target add aarch64-apple-darwin 2>/dev/null || true

# Create output directories
mkdir -p "$OUTPUT_DIR/swift"
mkdir -p "$SWIFT_BINDINGS_DIR"

cd "$RUST_DIR"

# Build release
echo "Building release..."
cargo build --release --target aarch64-apple-darwin

# Generate Swift bindings
echo "Generating UniFFI bindings..."
cargo run --release --bin uniffi-bindgen generate \
    --library target/aarch64-apple-darwin/release/libtla_core.dylib \
    --language swift \
    --out-dir "$OUTPUT_DIR/swift"

# Create framework structure
FRAMEWORK_DIR="$OUTPUT_DIR/TLACore.framework"
rm -rf "$FRAMEWORK_DIR"
mkdir -p "$FRAMEWORK_DIR/Headers"
mkdir -p "$FRAMEWORK_DIR/Modules"

# Copy library
cp target/aarch64-apple-darwin/release/libtla_core.dylib "$FRAMEWORK_DIR/TLACore"

# Copy Swift bindings to framework
cp "$OUTPUT_DIR/swift/tla_core.swift" "$FRAMEWORK_DIR/"
cp "$OUTPUT_DIR/swift/tla_coreFFI.h" "$FRAMEWORK_DIR/Headers/"

# Also copy Swift bindings to app source for SwiftPM integration
cp "$OUTPUT_DIR/swift/tla_core.swift" "$SWIFT_BINDINGS_DIR/TLACoreBindings.swift"

# Create module map
cat > "$FRAMEWORK_DIR/Modules/module.modulemap" << 'EOF'
framework module TLACore {
    umbrella header "tla_coreFFI.h"
    export *
    module * { export * }
}
EOF

# Create Info.plist
cat > "$FRAMEWORK_DIR/Info.plist" << 'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>CFBundleIdentifier</key>
    <string>com.tlastudio.TLACore</string>
    <key>CFBundleName</key>
    <string>TLACore</string>
    <key>CFBundleVersion</key>
    <string>1.0.0</string>
    <key>CFBundleShortVersionString</key>
    <string>1.0.0</string>
    <key>CFBundlePackageType</key>
    <string>FMWK</string>
</dict>
</plist>
EOF

# Fix library install name
install_name_tool -id "@rpath/TLACore.framework/TLACore" "$FRAMEWORK_DIR/TLACore"

# Create symlink for easier access
ln -sf "$FRAMEWORK_DIR" "$PROJECT_DIR/TLACore.framework"

echo ""
echo "=== Build complete ==="
echo "Framework: $FRAMEWORK_DIR"
echo "Swift bindings copied to: $SWIFT_BINDINGS_DIR"
echo ""
echo "To use in Xcode:"
echo "1. Add TLACore.framework to 'Frameworks, Libraries, and Embedded Content'"
echo "2. Set 'Embed' to 'Embed & Sign'"
echo ""
echo "For SwiftPM, the bindings are already in Sources/TLAStudioApp/TLACore/"
