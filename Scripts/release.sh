#!/bin/bash
# Master release build script for TLA+ Studio
# Creates a complete, signed, notarized DMG installer

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Configuration
VERSION="${VERSION:-1.0.0}"
BUILD_CONFIG="${BUILD_CONFIG:-release}"
SKIP_NOTARIZE="${SKIP_NOTARIZE:-false}"
SKIP_PROVERS="${SKIP_PROVERS:-false}"

echo "=============================================="
echo "  TLA+ Studio Release Build"
echo "  Version: $VERSION"
echo "  Config: $BUILD_CONFIG"
echo "=============================================="
echo ""

cd "$PROJECT_DIR"

# Step 1: Download/Build dependencies
echo "=== Step 1: Dependencies ==="

if [ "$SKIP_PROVERS" != "true" ]; then
    # Download TLAPM
    if [ ! -f "Sources/TLAStudioApp/Resources/bin/tlapm" ]; then
        echo "Downloading TLAPM..."
        "$SCRIPT_DIR/download-tlapm.sh"
    else
        echo "TLAPM already present, skipping download"
    fi

    # Build/download provers
    if [ ! -f "Sources/TLAStudioApp/Resources/Provers/z3" ]; then
        echo "Building provers..."
        "$SCRIPT_DIR/build-provers.sh"
    else
        echo "Provers already present, skipping build"
    fi
else
    echo "Skipping prover download (SKIP_PROVERS=true)"
fi

# Step 2: Build Rust core
echo ""
echo "=== Step 2: Build Rust Core ==="
"$SCRIPT_DIR/build-rust-core.sh"

# Step 3: Build Swift application
echo ""
echo "=== Step 3: Build Swift Application ==="
if [ "$BUILD_CONFIG" = "release" ]; then
    swift build -c release
else
    swift build
fi

# Step 4: Create app bundle
echo ""
echo "=== Step 4: Create App Bundle ==="

# Modify build-app.sh to use release config
if [ "$BUILD_CONFIG" = "release" ]; then
    # Create release version of build-app.sh behavior
    BUILD_DIR="$PROJECT_DIR/.build/arm64-apple-macosx/release"
else
    BUILD_DIR="$PROJECT_DIR/.build/arm64-apple-macosx/debug"
fi

APP_NAME="TLA+ Studio"
APP_DIR="$BUILD_DIR/$APP_NAME.app"

# Run build-app.sh (it handles both debug and release)
"$SCRIPT_DIR/build-app.sh"

# For release builds, copy from debug to release if needed
if [ "$BUILD_CONFIG" = "release" ] && [ ! -d "$APP_DIR" ]; then
    DEBUG_APP="$PROJECT_DIR/.build/arm64-apple-macosx/debug/$APP_NAME.app"
    if [ -d "$DEBUG_APP" ]; then
        mkdir -p "$BUILD_DIR"
        cp -R "$DEBUG_APP" "$APP_DIR"
    fi
fi

# Update version in Info.plist
if [ -f "$APP_DIR/Contents/Info.plist" ]; then
    /usr/libexec/PlistBuddy -c "Set :CFBundleShortVersionString $VERSION" "$APP_DIR/Contents/Info.plist"
    /usr/libexec/PlistBuddy -c "Set :CFBundleVersion $VERSION" "$APP_DIR/Contents/Info.plist"
fi

echo "App bundle created: $APP_DIR"

# Step 5: Code sign
echo ""
echo "=== Step 5: Code Sign ==="
if [ -n "$SIGNING_IDENTITY" ] || security find-identity -v -p codesigning | grep -q "Developer ID"; then
    "$SCRIPT_DIR/sign-app.sh" "$APP_DIR"
else
    echo "Warning: No signing identity found, skipping code signing"
    echo "Set SIGNING_IDENTITY environment variable for signed builds"
fi

# Step 6: Notarize
echo ""
echo "=== Step 6: Notarize ==="
if [ "$SKIP_NOTARIZE" = "true" ]; then
    echo "Skipping notarization (SKIP_NOTARIZE=true)"
elif [ -n "$NOTARIZE_PROFILE" ] || xcrun notarytool history --keychain-profile "notarytool-profile" &>/dev/null; then
    "$SCRIPT_DIR/notarize-app.sh" "$APP_DIR"
else
    echo "Warning: No notarization profile found, skipping notarization"
    echo "Set NOTARIZE_PROFILE environment variable or create 'notarytool-profile'"
fi

# Step 7: Create DMG
echo ""
echo "=== Step 7: Create DMG ==="
VERSION="$VERSION" "$SCRIPT_DIR/create-dmg.sh" "$APP_DIR"

# Summary
echo ""
echo "=============================================="
echo "  Release Build Complete!"
echo "=============================================="
echo ""
echo "Artifacts:"
echo "  App:  $APP_DIR"
echo "  DMG:  $PROJECT_DIR/.build/TLA+Studio-${VERSION}.dmg"
echo ""

# Calculate sizes
echo "Bundle sizes:"
if [ -f "$APP_DIR/Contents/Resources/tlc-native" ]; then
    echo "  TLC:      $(du -h "$APP_DIR/Contents/Resources/tlc-native" | cut -f1)"
fi
if [ -d "$APP_DIR/Contents/Resources/bin" ]; then
    echo "  TLAPM:    $(du -sh "$APP_DIR/Contents/Resources/bin" | cut -f1)"
fi
if [ -d "$APP_DIR/Contents/Resources/Provers" ]; then
    echo "  Provers:  $(du -sh "$APP_DIR/Contents/Resources/Provers" | cut -f1)"
fi
echo "  Total:    $(du -sh "$APP_DIR" | cut -f1)"
echo ""

DMG_PATH="$PROJECT_DIR/.build/TLA+Studio-${VERSION}.dmg"
if [ -f "$DMG_PATH" ]; then
    echo "DMG size: $(du -h "$DMG_PATH" | cut -f1)"
    echo ""
    echo "To test the installer:"
    echo "  open \"$DMG_PATH\""
fi
