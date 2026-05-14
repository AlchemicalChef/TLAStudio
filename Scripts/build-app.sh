#!/bin/bash
# Build TLA+ Studio as a proper macOS .app bundle

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Support release or debug builds
BUILD_CONFIG="${BUILD_CONFIG:-debug}"
if [ "$1" = "release" ] || { [ "$1" = "-c" ] && [ "$2" = "release" ]; }; then
    BUILD_CONFIG="release"
fi

APP_NAME="TLA+ Studio"

copy_tlacore_dylib() {
    local app_dir="$1"
    local executable_path="$app_dir/Contents/MacOS/TLAStudio"
    local frameworks_dir="$app_dir/Contents/Frameworks"
    local bundled_dylib="$frameworks_dir/libtla_core.dylib"
    local linked_dylib
    local dylib_source=""

    linked_dylib="$(otool -L "$executable_path" | awk '/libtla_core\.dylib/{print $1; exit}')"

    if [ -n "$linked_dylib" ] && [ -f "$linked_dylib" ]; then
        dylib_source="$linked_dylib"
    else
        for candidate in \
            "$PROJECT_DIR/Sources/TLACore/target/$BUILD_CONFIG/libtla_core.dylib" \
            "$PROJECT_DIR/Sources/TLACore/target/$BUILD_CONFIG/deps/libtla_core.dylib" \
            "$PROJECT_DIR/Sources/TLACore/target/aarch64-apple-darwin/$BUILD_CONFIG/libtla_core.dylib" \
            "$PROJECT_DIR/Sources/TLACore/target/aarch64-apple-darwin/$BUILD_CONFIG/deps/libtla_core.dylib" \
            "$PROJECT_DIR/Sources/TLACore/target/release/libtla_core.dylib" \
            "$PROJECT_DIR/Sources/TLACore/target/release/deps/libtla_core.dylib"
        do
            if [ -f "$candidate" ]; then
                dylib_source="$candidate"
                break
            fi
        done
    fi

    if [ -z "$dylib_source" ]; then
        echo "Warning: libtla_core.dylib not found; app bundle will not be self-contained" >&2
        return
    fi

    mkdir -p "$frameworks_dir"
    cp "$dylib_source" "$bundled_dylib"
    chmod +x "$bundled_dylib"

    install_name_tool -id "@rpath/libtla_core.dylib" "$bundled_dylib"
    if [ -n "$linked_dylib" ]; then
        install_name_tool -change "$linked_dylib" "@executable_path/../Frameworks/libtla_core.dylib" "$executable_path"
    fi
}

# Re-sign the app after install_name_tool modifies the binary. install_name_tool
# invalidates the ad-hoc signature Swift attaches at build time, so macOS refuses
# to launch the bundle with `SIGKILL (Code Signature Invalid)` without this step.
# Uses ad-hoc signing (`-`) for local debug builds; real signing for distribution
# lives in Scripts/sign-app.sh.
resign_adhoc() {
    local app_dir="$1"
    echo "Ad-hoc re-signing bundle (dylib first, then app)..."
    if [ -f "$app_dir/Contents/Frameworks/libtla_core.dylib" ]; then
        codesign --force --sign - "$app_dir/Contents/Frameworks/libtla_core.dylib"
    fi
    codesign --force --deep --sign - "$app_dir"
}

echo "Building TLA+ Studio ($BUILD_CONFIG)..."

# Build with Swift Package Manager
cd "$PROJECT_DIR"
if [ "$BUILD_CONFIG" = "release" ]; then
    swift build -c release
    BUILD_DIR="$(swift build -c release --show-bin-path)"
else
    swift build
    BUILD_DIR="$(swift build --show-bin-path)"
fi

APP_DIR="$BUILD_DIR/$APP_NAME.app"

# Create app bundle structure
echo "Creating app bundle..."
rm -rf "$APP_DIR"
mkdir -p "$APP_DIR/Contents/MacOS"
mkdir -p "$APP_DIR/Contents/Resources"
mkdir -p "$APP_DIR/Contents/Frameworks"

# Copy executable
cp "$BUILD_DIR/TLAStudio" "$APP_DIR/Contents/MacOS/TLAStudio"
copy_tlacore_dylib "$APP_DIR"

# Copy icon
cp "$PROJECT_DIR/Sources/TLAStudioApp/Resources/AppIcon.icns" "$APP_DIR/Contents/Resources/AppIcon.icns"

# Copy resource bundle (contains all resources: TLC, TLAPM, provers via SPM)
cp -R "$BUILD_DIR/TLAStudio_TLAStudioApp.bundle" "$APP_DIR/Contents/Resources/"

# Copy resources that are not in the SwiftPM target tree but are required at runtime
if [ -f "$PROJECT_DIR/Scripts/tla2tools.jar" ]; then
    cp "$PROJECT_DIR/Scripts/tla2tools.jar" "$APP_DIR/Contents/Resources/tla2tools.jar"
fi
if [ -d "$PROJECT_DIR/Resources/StandardModules" ]; then
    cp -R "$PROJECT_DIR/Resources/StandardModules" "$APP_DIR/Contents/Resources/"
fi

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
        <dict>
            <key>CFBundleTypeName</key>
            <string>TLA+ Configuration</string>
            <key>CFBundleTypeRole</key>
            <string>Editor</string>
            <key>LSHandlerRank</key>
            <string>Alternate</string>
            <key>LSItemContentTypes</key>
            <array>
                <string>com.tlaplus.configuration</string>
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
        <dict>
            <key>UTTypeIdentifier</key>
            <string>com.tlaplus.configuration</string>
            <key>UTTypeDescription</key>
            <string>TLA+ Configuration</string>
            <key>UTTypeConformsTo</key>
            <array>
                <string>public.plain-text</string>
                <string>public.source-code</string>
            </array>
            <key>UTTypeTagSpecification</key>
            <dict>
                <key>public.filename-extension</key>
                <array>
                    <string>cfg</string>
                </array>
            </dict>
        </dict>
    </array>
    <key>NSHumanReadableCopyright</key>
    <string>Copyright © 2025. All rights reserved.</string>
</dict>
</plist>
PLIST

resign_adhoc "$APP_DIR"

echo "Build complete: $APP_DIR"
echo ""
echo "To run: open \"$APP_DIR\""
