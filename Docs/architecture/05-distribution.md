# Distribution Architecture

## Overview

TLA+ Studio is distributed directly (not via App Store) using Developer ID signing and notarization. This avoids App Store sandbox restrictions while maintaining security.

## Bundle Structure

```
TLAStudio.app/
├── Contents/
│   ├── Info.plist
│   ├── MacOS/
│   │   └── TLAStudio              # Main executable
│   ├── XPCServices/
│   │   └── TLAService.xpc/        # XPC service bundle
│   │       └── Contents/
│   │           ├── Info.plist
│   │           └── MacOS/TLAService
│   ├── Frameworks/
│   │   └── TLACore.framework/     # Rust core via UniFFI
│   │       ├── TLACore
│   │       ├── Headers/
│   │       └── Resources/
│   └── Resources/
│       ├── Assets.xcassets        # Icons
│       ├── Provers/               # Verification tools
│       │   ├── tlc-native         # GraalVM AOT compiled
│       │   ├── tlapm              # TLAPS proof manager
│       │   ├── z3                 # SMT solver
│       │   ├── zenon              # Tableau prover
│       │   ├── spass              # First-order prover
│       │   └── ls4                # Temporal logic prover
│       ├── StandardModules/       # TLA+ standard library
│       │   ├── Naturals.tla
│       │   ├── Integers.tla
│       │   ├── Sequences.tla
│       │   ├── FiniteSets.tla
│       │   ├── Bags.tla
│       │   ├── TLC.tla
│       │   └── TLAPS.tla
│       ├── SampleSpecs/           # Example specifications
│       └── TreeSitter/
│           └── libtree-sitter-tlaplus.dylib
```

## Code Signing

### Identity Setup

```bash
# List available signing identities
security find-identity -v -p codesigning

# Expected output:
# "Developer ID Application: Your Name (TEAMID)"
```

### Signing Order (Inside-Out)

Sign components from innermost to outermost:

```bash
#!/bin/bash
# Scripts/codesign-bundle.sh

set -e

IDENTITY="Developer ID Application: Your Name (TEAMID)"
APP="TLAStudio.app"
ENTITLEMENTS="Resources/TLAStudio.entitlements"
XPC_ENTITLEMENTS="Resources/TLAService.entitlements"

echo "=== Signing TLA+ Studio ==="

# 1. Sign provers (no entitlements, just runtime)
echo "Signing provers..."
for prover in tlc-native tlapm z3 zenon spass ls4; do
    codesign --force --options runtime --timestamp \
        --sign "$IDENTITY" \
        "$APP/Contents/Resources/Provers/$prover"
done

# 2. Sign tree-sitter library
echo "Signing tree-sitter..."
codesign --force --options runtime --timestamp \
    --sign "$IDENTITY" \
    "$APP/Contents/Resources/TreeSitter/libtree-sitter-tlaplus.dylib"

# 3. Sign framework
echo "Signing TLACore framework..."
codesign --force --options runtime --timestamp \
    --sign "$IDENTITY" \
    "$APP/Contents/Frameworks/TLACore.framework"

# 4. Sign XPC service
echo "Signing XPC service..."
codesign --force --options runtime --timestamp \
    --entitlements "$XPC_ENTITLEMENTS" \
    --sign "$IDENTITY" \
    "$APP/Contents/XPCServices/TLAService.xpc"

# 5. Sign main app (last)
echo "Signing main app..."
codesign --force --options runtime --timestamp \
    --entitlements "$ENTITLEMENTS" \
    --sign "$IDENTITY" \
    "$APP"

# 6. Verify
echo "Verifying signature..."
codesign --verify --deep --strict "$APP"
spctl --assess --type execute "$APP"

echo "=== Signing complete ==="
```

### XPC Service Entitlements

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" 
    "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>com.apple.security.app-sandbox</key>
    <true/>
    
    <!-- Access to spawn subprocesses (for TLC, TLAPM) -->
    <key>com.apple.security.temporary-exception.sbpl</key>
    <array>
        <string>(allow process-exec)</string>
    </array>
    
    <!-- File access for specs -->
    <key>com.apple.security.files.user-selected.read-write</key>
    <true/>
</dict>
</plist>
```

## Notarization

```bash
#!/bin/bash
# Scripts/notarize.sh

APP="TLAStudio.app"
ZIP="TLAStudio.zip"
APPLE_ID="your@email.com"
TEAM_ID="YOURTEAMID"
APP_PASSWORD="@keychain:AC_PASSWORD"  # App-specific password

# 1. Create zip for upload
echo "Creating archive..."
ditto -c -k --keepParent "$APP" "$ZIP"

# 2. Submit for notarization
echo "Submitting for notarization..."
xcrun notarytool submit "$ZIP" \
    --apple-id "$APPLE_ID" \
    --team-id "$TEAM_ID" \
    --password "$APP_PASSWORD" \
    --wait

# 3. Staple the ticket
echo "Stapling notarization ticket..."
xcrun stapler staple "$APP"

# 4. Verify
echo "Verifying notarization..."
spctl --assess --verbose "$APP"
xcrun stapler validate "$APP"

# 5. Clean up
rm "$ZIP"

echo "=== Notarization complete ==="
```

## DMG Creation

```bash
#!/bin/bash
# Scripts/create-dmg.sh

APP="TLAStudio.app"
DMG="TLAStudio-1.0.0.dmg"
VOLUME_NAME="TLA+ Studio"

# 1. Create temporary directory
TEMP_DIR=$(mktemp -d)
cp -R "$APP" "$TEMP_DIR/"

# 2. Create symlink to Applications
ln -s /Applications "$TEMP_DIR/Applications"

# 3. Create DMG
hdiutil create -volname "$VOLUME_NAME" \
    -srcfolder "$TEMP_DIR" \
    -ov -format UDZO \
    "$DMG"

# 4. Sign the DMG
codesign --force --sign "Developer ID Application: Your Name (TEAMID)" "$DMG"

# 5. Notarize the DMG
xcrun notarytool submit "$DMG" \
    --apple-id "$APPLE_ID" \
    --team-id "$TEAM_ID" \
    --password "$APP_PASSWORD" \
    --wait

xcrun stapler staple "$DMG"

# 6. Clean up
rm -rf "$TEMP_DIR"

echo "Created: $DMG"
```

## Auto-Updates (Sparkle)

### Setup

1. Add Sparkle dependency:
```swift
// Package.swift
dependencies: [
    .package(url: "https://github.com/sparkle-project/Sparkle", from: "2.0.0"),
]
```

2. Configure Info.plist:
```xml
<key>SUFeedURL</key>
<string>https://yourdomain.com/appcast.xml</string>
<key>SUPublicEDKey</key>
<string>YOUR_ED25519_PUBLIC_KEY</string>
```

3. Generate keys:
```bash
./bin/generate_keys
# Save private key securely
# Add public key to Info.plist
```

### Appcast File

```xml
<?xml version="1.0" encoding="utf-8"?>
<rss version="2.0" xmlns:sparkle="http://www.andymatuschak.org/xml-namespaces/sparkle">
    <channel>
        <title>TLA+ Studio Updates</title>
        <link>https://yourdomain.com/appcast.xml</link>
        <item>
            <title>Version 1.0.1</title>
            <sparkle:releaseNotesLink>
                https://yourdomain.com/releases/1.0.1.html
            </sparkle:releaseNotesLink>
            <pubDate>Mon, 15 Jan 2025 12:00:00 +0000</pubDate>
            <enclosure url="https://yourdomain.com/releases/TLAStudio-1.0.1.dmg"
                       sparkle:version="1.0.1"
                       sparkle:shortVersionString="1.0.1"
                       length="50000000"
                       type="application/octet-stream"
                       sparkle:edSignature="BASE64_SIGNATURE"/>
            <sparkle:minimumSystemVersion>14.0</sparkle:minimumSystemVersion>
        </item>
    </channel>
</rss>
```

### Sign Updates

```bash
# Sign the DMG with your EdDSA private key
./bin/sign_update TLAStudio-1.0.1.dmg
# Outputs: sparkle:edSignature="..."
```

## Release Checklist

- [ ] Update version in Info.plist
- [ ] Update CHANGELOG.md
- [ ] Build release configuration
- [ ] Run all tests
- [ ] Build Rust core (release)
- [ ] Build TLC native image
- [ ] Assemble app bundle
- [ ] Code sign (inside-out)
- [ ] Notarize app
- [ ] Create DMG
- [ ] Notarize DMG
- [ ] Sign update for Sparkle
- [ ] Update appcast.xml
- [ ] Upload to distribution server
- [ ] Tag release in git
- [ ] Create GitHub release

## Gatekeeper Testing

```bash
# Clear cache to test fresh install
sudo spctl --reset-default

# Test app
spctl --assess --type execute TLAStudio.app

# Test DMG
spctl --assess --type open TLAStudio-1.0.0.dmg

# Expected: "accepted"
```

## Troubleshooting

### "App is damaged"
```bash
# Check signature
codesign -vvv --deep --strict TLAStudio.app

# Check notarization
spctl --assess --verbose TLAStudio.app
xcrun stapler validate TLAStudio.app
```

### Signature invalid after modification
- Any modification invalidates signatures
- Re-sign entire bundle after changes
- Sign inside-out

### XPC service not found
- Verify bundle ID in XPC Info.plist
- Check LaunchServices registration
- Verify signing of XPC bundle
