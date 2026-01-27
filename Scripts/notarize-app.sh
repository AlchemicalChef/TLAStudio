#!/bin/bash
# Submit TLA+ Studio to Apple for notarization
# Requires: Apple Developer account, app-specific password stored in keychain

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Configuration
BUNDLE_ID="com.tlastudio.app"
APP_PATH="${1:-$PROJECT_DIR/.build/arm64-apple-macosx/release/TLA+ Studio.app}"

# Keychain profile name (created with: xcrun notarytool store-credentials)
KEYCHAIN_PROFILE="${NOTARIZE_PROFILE:-notarytool-profile}"

if [ ! -d "$APP_PATH" ]; then
    APP_PATH="$PROJECT_DIR/.build/arm64-apple-macosx/debug/TLA+ Studio.app"
fi

if [ ! -d "$APP_PATH" ]; then
    echo "Error: App bundle not found"
    exit 1
fi

echo "=== Notarizing TLA+ Studio ==="
echo "App: $APP_PATH"
echo "Bundle ID: $BUNDLE_ID"
echo ""

# Check if keychain profile exists
if ! xcrun notarytool history --keychain-profile "$KEYCHAIN_PROFILE" &>/dev/null; then
    echo "Error: Keychain profile '$KEYCHAIN_PROFILE' not found"
    echo ""
    echo "Create a profile with:"
    echo "  xcrun notarytool store-credentials \"$KEYCHAIN_PROFILE\" \\"
    echo "    --apple-id \"your@email.com\" \\"
    echo "    --team-id \"YOUR_TEAM_ID\" \\"
    echo "    --password \"app-specific-password\""
    echo ""
    echo "Or set NOTARIZE_PROFILE environment variable to use a different profile"
    exit 1
fi

# Create ZIP for notarization (required format)
ZIP_PATH="$PROJECT_DIR/.build/TLAStudio-notarize.zip"
echo "Creating ZIP archive..."
ditto -c -k --keepParent "$APP_PATH" "$ZIP_PATH"
echo "Created: $ZIP_PATH ($(du -h "$ZIP_PATH" | cut -f1))"

# Submit for notarization
echo ""
echo "Submitting for notarization..."
echo "This may take several minutes..."

SUBMISSION_OUTPUT=$(xcrun notarytool submit "$ZIP_PATH" \
    --keychain-profile "$KEYCHAIN_PROFILE" \
    --wait \
    2>&1)

echo "$SUBMISSION_OUTPUT"

# Extract submission ID
SUBMISSION_ID=$(echo "$SUBMISSION_OUTPUT" | grep -o 'id: [a-f0-9-]*' | head -1 | cut -d' ' -f2)

# Check result
if echo "$SUBMISSION_OUTPUT" | grep -q "status: Accepted"; then
    echo ""
    echo "Notarization successful!"
    echo ""

    # Staple the ticket to the app
    echo "Stapling notarization ticket..."
    xcrun stapler staple "$APP_PATH"

    echo ""
    echo "Verifying stapled ticket..."
    xcrun stapler validate "$APP_PATH"

    # Clean up ZIP
    rm -f "$ZIP_PATH"

    echo ""
    echo "Notarization complete!"
    echo "The app is now ready for distribution."
    echo ""
    echo "Next step: Run create-dmg.sh to create the installer"
else
    echo ""
    echo "Notarization failed or is still in progress"

    if [ -n "$SUBMISSION_ID" ]; then
        echo ""
        echo "Getting detailed log..."
        xcrun notarytool log "$SUBMISSION_ID" \
            --keychain-profile "$KEYCHAIN_PROFILE" \
            "$PROJECT_DIR/.build/notarization-log.json"
        echo "Log saved to: $PROJECT_DIR/.build/notarization-log.json"

        # Show summary of issues
        if [ -f "$PROJECT_DIR/.build/notarization-log.json" ]; then
            echo ""
            echo "Issues found:"
            cat "$PROJECT_DIR/.build/notarization-log.json" | python3 -c "
import json, sys
data = json.load(sys.stdin)
if 'issues' in data:
    for issue in data['issues']:
        print(f\"  - {issue.get('severity', 'unknown')}: {issue.get('message', 'No message')}\")
        if 'path' in issue:
            print(f\"    Path: {issue['path']}\")
" 2>/dev/null || cat "$PROJECT_DIR/.build/notarization-log.json"
        fi
    fi

    exit 1
fi
