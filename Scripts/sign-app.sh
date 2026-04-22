#!/bin/bash
# Code sign TLA+ Studio app bundle for distribution
# Requires a valid Developer ID Application certificate

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Configuration - set these for your signing identity
# Find your identity with: security find-identity -v -p codesigning
IDENTITY="${SIGNING_IDENTITY:-Developer ID Application}"
APP_PATH="${1:-$PROJECT_DIR/.build/arm64-apple-macosx/release/TLA+ Studio.app}"

if [ ! -d "$APP_PATH" ]; then
    # Try debug build
    APP_PATH="$PROJECT_DIR/.build/arm64-apple-macosx/debug/TLA+ Studio.app"
fi

if [ ! -d "$APP_PATH" ]; then
    echo "Error: App bundle not found at: $APP_PATH"
    echo "Run build-app.sh first"
    exit 1
fi

echo "=== Code Signing TLA+ Studio ==="
echo "App: $APP_PATH"
echo "Identity: $IDENTITY"
echo ""

# Check if identity exists
if ! security find-identity -v -p codesigning | grep -q "$IDENTITY"; then
    echo "Warning: Signing identity '$IDENTITY' not found"
    echo "Available identities:"
    security find-identity -v -p codesigning
    echo ""
    echo "Set SIGNING_IDENTITY environment variable or pass identity as argument"
    echo "For ad-hoc signing (testing only), use: SIGNING_IDENTITY='-' $0"
    exit 1
fi

# Entitlements file for hardened runtime
ENTITLEMENTS="$SCRIPT_DIR/entitlements.plist"
if [ ! -f "$ENTITLEMENTS" ]; then
    echo "Creating entitlements file..."
    cat > "$ENTITLEMENTS" << 'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <!-- Allow JIT for TLC's GraalVM native image -->
    <key>com.apple.security.cs.allow-jit</key>
    <true/>
    <!-- Allow unsigned executable memory for TLC -->
    <key>com.apple.security.cs.allow-unsigned-executable-memory</key>
    <true/>
    <!-- Disable library validation to load bundled binaries -->
    <key>com.apple.security.cs.disable-library-validation</key>
    <true/>
    <!-- Allow DYLD environment variables for provers -->
    <key>com.apple.security.cs.allow-dyld-environment-variables</key>
    <true/>
</dict>
</plist>
PLIST
fi

echo "Signing embedded binaries (inside-out)..."

RESOURCE_ROOT="$APP_PATH/Contents/Resources"
BUNDLE_ROOT="$RESOURCE_ROOT/TLAStudio_TLAStudioApp.bundle"

for binary in \
    "$RESOURCE_ROOT/tlc-native" \
    "$RESOURCE_ROOT/tlc-native-fast" \
    "$RESOURCE_ROOT/bin/tlapm" \
    "$RESOURCE_ROOT/Provers/z3" \
    "$RESOURCE_ROOT/Provers/cvc5" \
    "$RESOURCE_ROOT/Provers/zenon" \
    "$RESOURCE_ROOT/Provers/SPASS" \
    "$RESOURCE_ROOT/Provers/ls4" \
    "$RESOURCE_ROOT/Provers/isabelle-wrapper" \
    "$BUNDLE_ROOT/tlc-native" \
    "$BUNDLE_ROOT/tlc-native-fast" \
    "$BUNDLE_ROOT/bin/tlapm" \
    "$BUNDLE_ROOT/Provers/z3" \
    "$BUNDLE_ROOT/Provers/cvc5" \
    "$BUNDLE_ROOT/Provers/zenon" \
    "$BUNDLE_ROOT/Provers/SPASS" \
    "$BUNDLE_ROOT/Provers/ls4" \
    "$BUNDLE_ROOT/Provers/isabelle-wrapper" \
    "$BUNDLE_ROOT/lib/tlapm/backends/bin/zenon" \
    "$BUNDLE_ROOT/lib/tlapm/backends/bin/ls4"; do
    if [ -f "$binary" ]; then
        echo "  Signing $(basename "$binary")..."
        codesign --force --options runtime --timestamp \
            --sign "$IDENTITY" "$binary"
    fi
done

for isabelle_dir in \
    "$RESOURCE_ROOT/Provers/isabelle" \
    "$BUNDLE_ROOT/Provers/isabelle"; do
    if [ -d "$isabelle_dir" ]; then
        echo "  Signing Isabelle binaries in $isabelle_dir..."
        find "$isabelle_dir/bin" -type f -perm +111 2>/dev/null | while read binary; do
            codesign --force --options runtime --timestamp \
                --sign "$IDENTITY" "$binary" 2>/dev/null || true
        done
        find "$isabelle_dir/contrib" -type f -perm +111 2>/dev/null | while read binary; do
            codesign --force --options runtime --timestamp \
                --sign "$IDENTITY" "$binary" 2>/dev/null || true
        done
    fi
done

# Sign frameworks if any
if [ -d "$APP_PATH/Contents/Frameworks" ]; then
    echo "Signing frameworks..."
    find "$APP_PATH/Contents/Frameworks" -name "*.framework" -type d | while read framework; do
        codesign --force --options runtime --timestamp \
            --sign "$IDENTITY" "$framework"
    done
    find "$APP_PATH/Contents/Frameworks" -name "*.dylib" -type f | while read dylib; do
        codesign --force --options runtime --timestamp \
            --sign "$IDENTITY" "$dylib"
    done
fi

# Sign the main app bundle
echo "Signing main app bundle..."
codesign --force --options runtime --timestamp \
    --entitlements "$ENTITLEMENTS" \
    --sign "$IDENTITY" "$APP_PATH"

echo ""
echo "=== Verification ==="

# Verify signature
echo "Verifying code signature..."
codesign --verify --deep --strict --verbose=2 "$APP_PATH"

# Check Gatekeeper assessment
echo ""
echo "Checking Gatekeeper assessment..."
spctl --assess --type exec --verbose "$APP_PATH" 2>&1 || {
    echo "Note: Gatekeeper assessment may fail until app is notarized"
}

echo ""
echo "Code signing complete!"
echo "Next step: Run notarize-app.sh to submit for Apple notarization"
