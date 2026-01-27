#!/bin/bash
# Create DMG installer for TLA+ Studio with drag-to-install UI

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Configuration
APP_NAME="TLA+ Studio"
VERSION="${VERSION:-1.0.0}"
DMG_NAME="TLA+Studio-${VERSION}"
VOL_NAME="TLA+ Studio ${VERSION}"

APP_PATH="${1:-$PROJECT_DIR/.build/arm64-apple-macosx/release/TLA+ Studio.app}"
OUTPUT_DIR="$PROJECT_DIR/.build"

if [ ! -d "$APP_PATH" ]; then
    APP_PATH="$PROJECT_DIR/.build/arm64-apple-macosx/debug/TLA+ Studio.app"
fi

if [ ! -d "$APP_PATH" ]; then
    echo "Error: App bundle not found"
    exit 1
fi

echo "=== Creating DMG Installer ==="
echo "App: $APP_PATH"
echo "Version: $VERSION"
echo ""

# Create temporary directory for DMG contents
DMG_TEMP="$OUTPUT_DIR/dmg-temp"
rm -rf "$DMG_TEMP"
mkdir -p "$DMG_TEMP"

# Copy app to temp directory
echo "Copying app bundle..."
cp -R "$APP_PATH" "$DMG_TEMP/"

# Create Applications symlink for drag-to-install
ln -s /Applications "$DMG_TEMP/Applications"

# Create a background image for the DMG (optional)
BACKGROUND_DIR="$DMG_TEMP/.background"
mkdir -p "$BACKGROUND_DIR"

# Create a simple background with instructions
# Using a placeholder - you can replace with a custom image
cat > "$BACKGROUND_DIR/README.txt" << 'EOF'
Drag TLA+ Studio to Applications to install.
EOF

# Create the DMG
DMG_PATH="$OUTPUT_DIR/${DMG_NAME}.dmg"
TEMP_DMG="$OUTPUT_DIR/${DMG_NAME}-temp.dmg"

# Remove existing DMG
rm -f "$DMG_PATH" "$TEMP_DMG"

echo "Creating DMG..."

# Calculate required size (add 50MB buffer)
APP_SIZE=$(du -sm "$DMG_TEMP" | cut -f1)
DMG_SIZE=$((APP_SIZE + 50))

# Create temporary DMG (read-write)
hdiutil create -srcfolder "$DMG_TEMP" \
    -volname "$VOL_NAME" \
    -fs HFS+ \
    -fsargs "-c c=64,a=16,e=16" \
    -format UDRW \
    -size ${DMG_SIZE}m \
    "$TEMP_DMG"

# Mount the temporary DMG
echo "Configuring DMG appearance..."
MOUNT_DIR=$(hdiutil attach -readwrite -noverify "$TEMP_DMG" | grep "/Volumes/" | sed 's/.*\/Volumes/\/Volumes/')

if [ -z "$MOUNT_DIR" ]; then
    echo "Error: Failed to mount DMG"
    exit 1
fi

# Configure DMG window appearance using AppleScript
osascript << APPLESCRIPT
tell application "Finder"
    tell disk "$VOL_NAME"
        open
        set current view of container window to icon view
        set toolbar visible of container window to false
        set statusbar visible of container window to false
        set bounds of container window to {400, 100, 900, 450}
        set viewOptions to the icon view options of container window
        set arrangement of viewOptions to not arranged
        set icon size of viewOptions to 100

        -- Position the app and Applications folder
        set position of item "$APP_NAME.app" of container window to {125, 170}
        set position of item "Applications" of container window to {375, 170}

        close
        open
        update without registering applications
        delay 2
    end tell
end tell
APPLESCRIPT

# Sync and unmount
sync
hdiutil detach "$MOUNT_DIR" -quiet

# Convert to compressed read-only DMG
echo "Compressing DMG..."
hdiutil convert "$TEMP_DMG" \
    -format UDZO \
    -imagekey zlib-level=9 \
    -o "$DMG_PATH"

# Remove temporary files
rm -f "$TEMP_DMG"
rm -rf "$DMG_TEMP"

echo ""
echo "=== DMG Created ==="
echo "Output: $DMG_PATH"
echo "Size: $(du -h "$DMG_PATH" | cut -f1)"

# Sign the DMG if signing identity is available
IDENTITY="${SIGNING_IDENTITY:-Developer ID Application}"
if security find-identity -v -p codesigning | grep -q "$IDENTITY"; then
    echo ""
    echo "Signing DMG..."
    codesign --force --sign "$IDENTITY" "$DMG_PATH"
    echo "DMG signed successfully"
fi

echo ""
echo "=== Verification ==="

# Verify DMG
echo "Verifying DMG..."
hdiutil verify "$DMG_PATH"

# Show contents
echo ""
echo "DMG contents:"
hdiutil attach "$DMG_PATH" -nobrowse -quiet
ls -la "/Volumes/$VOL_NAME/" 2>/dev/null || true
hdiutil detach "/Volumes/$VOL_NAME" -quiet 2>/dev/null || true

echo ""
echo "DMG creation complete!"
echo ""
echo "To test: open \"$DMG_PATH\""
