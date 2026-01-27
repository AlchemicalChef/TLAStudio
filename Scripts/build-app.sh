#!/bin/bash
# Build TLA+ Studio as a proper macOS .app bundle

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Support release or debug builds
BUILD_CONFIG="${BUILD_CONFIG:-debug}"
if [ "$1" = "release" ] || [ "$1" = "-c" ] && [ "$2" = "release" ]; then
    BUILD_CONFIG="release"
fi

BUILD_DIR="$PROJECT_DIR/.build/arm64-apple-macosx/$BUILD_CONFIG"
APP_NAME="TLA+ Studio"
APP_DIR="$BUILD_DIR/$APP_NAME.app"

echo "Building TLA+ Studio ($BUILD_CONFIG)..."

# Build with Swift Package Manager
cd "$PROJECT_DIR"
if [ "$BUILD_CONFIG" = "release" ]; then
    swift build -c release
else
    swift build
fi

# Create app bundle structure
echo "Creating app bundle..."
rm -rf "$APP_DIR"
mkdir -p "$APP_DIR/Contents/MacOS"
mkdir -p "$APP_DIR/Contents/Resources"

# Copy executable
cp "$BUILD_DIR/TLAStudio" "$APP_DIR/Contents/MacOS/TLAStudio"

# Copy icon
cp "$PROJECT_DIR/Sources/TLAStudioApp/Resources/AppIcon.icns" "$APP_DIR/Contents/Resources/AppIcon.icns"

# Copy resource bundle (contains all resources: TLC, TLAPM, provers via SPM)
cp -R "$BUILD_DIR/TLAStudio_TLAStudioApp.bundle" "$APP_DIR/Contents/Resources/"

# Set executable permissions on binaries in the resource bundle
echo "Setting executable permissions..."
BUNDLE_DIR="$APP_DIR/Contents/Resources/TLAStudio_TLAStudioApp.bundle"

# TLC binaries
if [ -f "$BUNDLE_DIR/tlc-native" ]; then
    chmod +x "$BUNDLE_DIR/tlc-native"
fi
if [ -f "$BUNDLE_DIR/tlc-native-fast" ]; then
    chmod +x "$BUNDLE_DIR/tlc-native-fast"
fi

# TLAPM binary
if [ -d "$BUNDLE_DIR/bin" ]; then
    chmod +x "$BUNDLE_DIR/bin/"* 2>/dev/null || true
fi

# Backend provers
if [ -d "$BUNDLE_DIR/Provers" ]; then
    for binary in z3 cvc5 zenon SPASS ls4 tlapm isabelle-wrapper; do
        if [ -f "$BUNDLE_DIR/Provers/$binary" ]; then
            chmod +x "$BUNDLE_DIR/Provers/$binary"
        fi
    done
fi

# Zenon in lib/tlapm/backends/bin
if [ -d "$BUNDLE_DIR/lib/tlapm/backends/bin" ]; then
    chmod +x "$BUNDLE_DIR/lib/tlapm/backends/bin/"* 2>/dev/null || true
fi

# Create PkgInfo
echo -n "APPL????" > "$APP_DIR/Contents/PkgInfo"

# Create Info.plist
cat > "$APP_DIR/Contents/Info.plist" << 'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>CFBundleIdentifier</key>
    <string>com.tlastudio.app</string>
    <key>CFBundleName</key>
    <string>TLA+ Studio</string>
    <key>CFBundleDisplayName</key>
    <string>TLA+ Studio</string>
    <key>CFBundleExecutable</key>
    <string>TLAStudio</string>
    <key>CFBundleVersion</key>
    <string>1</string>
    <key>CFBundleShortVersionString</key>
    <string>1.0.0</string>
    <key>CFBundlePackageType</key>
    <string>APPL</string>
    <key>LSMinimumSystemVersion</key>
    <string>14.0</string>
    <key>LSApplicationCategoryType</key>
    <string>public.app-category.developer-tools</string>
    <key>CFBundleIconFile</key>
    <string>AppIcon</string>
    <key>CFBundleIconName</key>
    <string>AppIcon</string>
    <key>NSHighResolutionCapable</key>
    <true/>
    <key>NSPrincipalClass</key>
    <string>NSApplication</string>
    <key>CFBundleDocumentTypes</key>
    <array>
        <dict>
            <key>CFBundleTypeName</key>
            <string>TLA+ Specification</string>
            <key>CFBundleTypeRole</key>
            <string>Editor</string>
            <key>LSHandlerRank</key>
            <string>Owner</string>
            <key>LSItemContentTypes</key>
            <array>
                <string>com.tlaplus.specification</string>
            </array>
            <key>NSDocumentClass</key>
            <string>TLAStudioApp.TLADocument</string>
        </dict>
    </array>
    <key>UTImportedTypeDeclarations</key>
    <array>
        <dict>
            <key>UTTypeIdentifier</key>
            <string>com.tlaplus.specification</string>
            <key>UTTypeDescription</key>
            <string>TLA+ Specification</string>
            <key>UTTypeConformsTo</key>
            <array>
                <string>public.plain-text</string>
                <string>public.source-code</string>
            </array>
            <key>UTTypeTagSpecification</key>
            <dict>
                <key>public.filename-extension</key>
                <array>
                    <string>tla</string>
                </array>
            </dict>
        </dict>
    </array>
    <key>NSHumanReadableCopyright</key>
    <string>Copyright © 2025. All rights reserved.</string>
</dict>
</plist>
PLIST

echo "Build complete: $APP_DIR"
echo ""
echo "To run: open \"$APP_DIR\""
