#!/bin/bash
# Create a proper .app bundle for TLAStudio

set -e

BUILD_DIR=".build/arm64-apple-macosx/debug"
APP_NAME="TLAStudio"
BUNDLE_DIR="$BUILD_DIR/$APP_NAME.app"
TLACORE_DIR="Sources/TLACore"

echo "Creating app bundle at $BUNDLE_DIR..."

# Create bundle structure
mkdir -p "$BUNDLE_DIR/Contents/MacOS"
mkdir -p "$BUNDLE_DIR/Contents/Resources"
mkdir -p "$BUNDLE_DIR/Contents/Frameworks"

# Copy executable
cp "$BUILD_DIR/$APP_NAME" "$BUNDLE_DIR/Contents/MacOS/$APP_NAME"

# Copy TLACore library if it exists
if [ -f "$TLACORE_DIR/target/release/libtla_core.dylib" ]; then
    echo "Copying TLACore library..."
    cp "$TLACORE_DIR/target/release/libtla_core.dylib" "$BUNDLE_DIR/Contents/Frameworks/"

    # Get the current install name of the dylib (it's an absolute path)
    DYLIB_ID=$(otool -D "$TLACORE_DIR/target/release/libtla_core.dylib" | tail -1)
    echo "Original dylib install name: $DYLIB_ID"

    # Update dylib's own install name
    install_name_tool -id @rpath/libtla_core.dylib "$BUNDLE_DIR/Contents/Frameworks/libtla_core.dylib" 2>/dev/null || true

    # Update dylib path in executable using the original path
    install_name_tool -change "$DYLIB_ID" @executable_path/../Frameworks/libtla_core.dylib "$BUNDLE_DIR/Contents/MacOS/$APP_NAME" 2>/dev/null || true

    echo "Updated dylib paths for bundle portability"
fi

# Copy Info.plist and process variables
sed -e "s/\$(PRODUCT_BUNDLE_IDENTIFIER)/com.tlaplus.studio/g" \
    -e "s/\$(EXECUTABLE_NAME)/$APP_NAME/g" \
    -e "s/\$(PRODUCT_MODULE_NAME)/TLAStudioApp/g" \
    Resources/Info.plist > "$BUNDLE_DIR/Contents/Info.plist"

# Create PkgInfo
echo -n "APPL????" > "$BUNDLE_DIR/Contents/PkgInfo"

echo "App bundle created: $BUNDLE_DIR"
echo ""
echo "To run: open $BUNDLE_DIR"
