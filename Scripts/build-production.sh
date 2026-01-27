#!/bin/bash
#
# TLA+ Studio Production Build Script
# ====================================
# Builds a complete, self-contained TLA+ Studio.app with all dependencies
#
# Usage:
#   ./Scripts/build-production.sh [options]
#
# Options:
#   --skip-prereqs     Skip prerequisite installation
#   --skip-tlc         Skip TLC native build (use existing)
#   --skip-tlapm       Skip TLAPM build (use existing)
#   --sign             Code sign the app (requires Developer ID)
#   --notarize         Notarize the app (requires Apple credentials)
#   --dmg              Create DMG installer
#   --help             Show this help message
#

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Script configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
BUILD_DIR="$PROJECT_DIR/.build/arm64-apple-macosx/release"
DEPS_DIR="$PROJECT_DIR/.deps"
APP_NAME="TLA+ Studio"
APP_DIR="$BUILD_DIR/$APP_NAME.app"
VERSION="1.0.0"

# Parse arguments
SKIP_PREREQS=false
SKIP_TLC=false
SKIP_TLAPM=false
DO_SIGN=false
DO_NOTARIZE=false
CREATE_DMG=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --skip-prereqs) SKIP_PREREQS=true; shift ;;
        --skip-tlc) SKIP_TLC=true; shift ;;
        --skip-tlapm) SKIP_TLAPM=true; shift ;;
        --sign) DO_SIGN=true; shift ;;
        --notarize) DO_NOTARIZE=true; shift ;;
        --dmg) CREATE_DMG=true; shift ;;
        --help)
            head -20 "$0" | tail -15
            exit 0
            ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

# Helper functions
log_step() {
    echo -e "\n${BLUE}==>${NC} ${GREEN}$1${NC}"
}

log_info() {
    echo -e "    ${YELLOW}→${NC} $1"
}

log_error() {
    echo -e "    ${RED}✗${NC} $1"
}

log_success() {
    echo -e "    ${GREEN}✓${NC} $1"
}

check_command() {
    if command -v "$1" &> /dev/null; then
        return 0
    else
        return 1
    fi
}

# ============================================================================
# STEP 1: Check and Install Prerequisites
# ============================================================================

install_prerequisites() {
    log_step "Checking prerequisites..."

    # Check macOS version
    MACOS_VERSION=$(sw_vers -productVersion)
    log_info "macOS version: $MACOS_VERSION"

    # Check Xcode Command Line Tools
    if ! xcode-select -p &> /dev/null; then
        log_info "Installing Xcode Command Line Tools..."
        xcode-select --install
        echo "Please complete Xcode CLI installation and re-run this script."
        exit 1
    fi
    log_success "Xcode Command Line Tools installed"

    # Check/Install Homebrew
    if ! check_command brew; then
        log_info "Installing Homebrew..."
        /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
        eval "$(/opt/homebrew/bin/brew shellenv)"
    fi
    log_success "Homebrew installed"

    # Check/Install Rust
    if ! check_command rustc; then
        log_info "Installing Rust toolchain..."
        curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
        source "$HOME/.cargo/env"
    fi
    log_success "Rust installed ($(rustc --version | cut -d' ' -f2))"

    # Add ARM64 target if needed
    if ! rustup target list --installed | grep -q "aarch64-apple-darwin"; then
        log_info "Adding aarch64-apple-darwin target..."
        rustup target add aarch64-apple-darwin
    fi
    log_success "Rust ARM64 target configured"

    # Install Graphviz
    if ! check_command dot; then
        log_info "Installing Graphviz..."
        brew install graphviz
    fi
    log_success "Graphviz installed ($(dot -V 2>&1 | head -1))"

    # Install Z3
    if ! check_command z3; then
        log_info "Installing Z3..."
        brew install z3
    fi
    log_success "Z3 installed ($(z3 --version | head -1))"

    # Install Java (needed for TLC build)
    if ! check_command java; then
        log_info "Installing Java (for TLC build)..."
        brew install openjdk@17
        sudo ln -sfn /opt/homebrew/opt/openjdk@17/libexec/openjdk.jdk /Library/Java/JavaVirtualMachines/openjdk-17.jdk
    fi
    log_success "Java installed ($(java -version 2>&1 | head -1))"

    # Install GraalVM (for TLC native-image)
    if ! check_command native-image; then
        log_info "Installing GraalVM..."
        brew install --cask graalvm-jdk
        export GRAALVM_HOME="/Library/Java/JavaVirtualMachines/graalvm-jdk-21/Contents/Home"
        export PATH="$GRAALVM_HOME/bin:$PATH"

        # Install native-image component
        if check_command gu; then
            gu install native-image
        fi
    fi
    log_success "GraalVM native-image available"

    # Install OCaml and OPAM (for TLAPM)
    if ! check_command opam; then
        log_info "Installing OCaml/OPAM..."
        brew install opam
        opam init -y --disable-sandboxing
        eval $(opam env)
    fi
    log_success "OCaml/OPAM installed"
}

# ============================================================================
# STEP 2: Build TLC Native Binary
# ============================================================================

build_tlc_native() {
    log_step "Building TLC Native Binary..."

    # Check if TLC native binary already exists
    if [ -f "$PROJECT_DIR/Resources/tlc-native" ]; then
        log_success "TLC native binary already exists in Resources/"
        mkdir -p "$PROJECT_DIR/Sources/TLAStudioApp/Resources"
        cp "$PROJECT_DIR/Resources/tlc-native" "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native"
        chmod +x "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native"

        # Also copy fast version if it exists
        if [ -f "$PROJECT_DIR/Resources/tlc-native-fast" ]; then
            cp "$PROJECT_DIR/Resources/tlc-native-fast" "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native-fast"
            chmod +x "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native-fast"
            log_success "TLC fast binary copied"
        fi
        return
    fi

    # Check Sources/TLAStudioApp/Resources as well
    if [ -f "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native" ]; then
        log_success "TLC native binary already exists"
        return
    fi

    mkdir -p "$DEPS_DIR"
    TLC_DIR="$DEPS_DIR/tlaplus"

    # Clone TLA+ repository if not present
    if [ ! -d "$TLC_DIR" ]; then
        log_info "Cloning TLA+ repository..."
        git clone --depth 1 https://github.com/tlaplus/tlaplus.git "$TLC_DIR"
    fi

    # Set GraalVM environment - detect installed version
    GRAALVM_DIR=$(ls -d /Library/Java/JavaVirtualMachines/graalvm-*.jdk 2>/dev/null | head -1)
    if [ -n "$GRAALVM_DIR" ]; then
        export GRAALVM_HOME="$GRAALVM_DIR/Contents/Home"
    else
        export GRAALVM_HOME="${GRAALVM_HOME:-/Library/Java/JavaVirtualMachines/graalvm-jdk-21/Contents/Home}"
    fi
    export JAVA_HOME="$GRAALVM_HOME"
    export PATH="$GRAALVM_HOME/bin:$PATH"

    cd "$TLC_DIR"

    # Build TLC native image
    log_info "Building TLC with GraalVM native-image (this may take 5-10 minutes)..."

    # Check for Gradle wrapper or use Maven
    if [ -f "./gradlew" ]; then
        ./gradlew :tla2tools:nativeCompile -x test || {
            log_error "TLC native build failed. Falling back to JAR..."
            ./gradlew :tla2tools:shadowJar -x test

            # Copy JAR as fallback
            mkdir -p "$PROJECT_DIR/Sources/TLAStudioApp/Resources"
            cp tla2tools/build/libs/tla2tools-*-SNAPSHOT.jar "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tla2tools.jar" 2>/dev/null
            log_info "Using TLC JAR (slower startup)"
            cd "$PROJECT_DIR"
            return
        }

        # Copy native binary
        mkdir -p "$PROJECT_DIR/Sources/TLAStudioApp/Resources"
        cp tla2tools/build/native/nativeCompile/tlc "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native"
        chmod +x "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native"

        log_success "TLC native binary built"

        # Build fast version (Epsilon GC) for small state spaces
        log_info "Building TLC fast version (Epsilon GC)..."
        ./gradlew :tla2tools:nativeCompile -Pfast -x test 2>/dev/null && {
            cp tla2tools/build/native/nativeCompile/tlc "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native-fast"
            chmod +x "$PROJECT_DIR/Sources/TLAStudioApp/Resources/tlc-native-fast"
            log_success "TLC fast binary built"
        } || log_info "Fast build skipped (optional)"
    else
        log_info "Gradle wrapper not found, skipping TLC native build"
        log_info "You can manually place tlc-native in Resources/ or Sources/TLAStudioApp/Resources/"
    fi

    cd "$PROJECT_DIR"
}

# ============================================================================
# STEP 3: Build TLAPM and Backends
# ============================================================================

build_tlapm() {
    log_step "Building TLAPM Proof System..."

    mkdir -p "$DEPS_DIR"
    TLAPM_DIR="$DEPS_DIR/tlapm"

    # Initialize OPAM if needed
    eval $(opam env 2>/dev/null) || true

    # Install TLAPM dependencies
    log_info "Installing OCaml dependencies..."
    opam install -y dune sexplib

    # Clone TLAPM if not present
    if [ ! -d "$TLAPM_DIR" ]; then
        log_info "Cloning TLAPM repository..."
        git clone --depth 1 https://github.com/tlaplus/tlapm.git "$TLAPM_DIR"
    fi

    cd "$TLAPM_DIR"

    # Build TLAPM
    log_info "Building TLAPM..."
    eval $(opam env)
    dune build

    # Install to project resources
    RESOURCES_DIR="$PROJECT_DIR/Sources/TLAStudioApp/Resources"
    mkdir -p "$RESOURCES_DIR/bin"
    mkdir -p "$RESOURCES_DIR/lib/tlapm"

    # Copy TLAPM binary
    cp _build/default/src/tlapm.exe "$RESOURCES_DIR/bin/tlapm"
    chmod +x "$RESOURCES_DIR/bin/tlapm"

    # Copy standard library
    cp -R library/* "$RESOURCES_DIR/lib/tlapm/" 2>/dev/null || true

    log_success "TLAPM built"

    # Build/copy Zenon
    log_info "Setting up Zenon..."
    if [ -d "zenon" ]; then
        cd zenon
        ./configure && make
        cp zenon "$RESOURCES_DIR/bin/"
        chmod +x "$RESOURCES_DIR/bin/zenon"
        cd ..
        log_success "Zenon built"
    elif check_command zenon; then
        cp "$(which zenon)" "$RESOURCES_DIR/bin/"
        log_success "Zenon copied from system"
    else
        log_info "Zenon not available (some proofs may fail)"
    fi

    # Copy Z3
    log_info "Setting up Z3..."
    if check_command z3; then
        cp "$(which z3)" "$RESOURCES_DIR/bin/"
        chmod +x "$RESOURCES_DIR/bin/z3"
        log_success "Z3 copied"
    fi

    cd "$PROJECT_DIR"
}

# ============================================================================
# STEP 4: Build Rust Core
# ============================================================================

build_rust_core() {
    log_step "Building Rust Core (TLACore)..."

    cd "$PROJECT_DIR/Sources/TLACore"

    # Build release version
    log_info "Compiling TLACore..."
    cargo build --release --target aarch64-apple-darwin

    log_success "TLACore built"

    cd "$PROJECT_DIR"
}

# ============================================================================
# STEP 5: Build Swift Application
# ============================================================================

build_swift_app() {
    log_step "Building Swift Application..."

    cd "$PROJECT_DIR"

    # Build release version
    log_info "Compiling TLA+ Studio..."
    swift build -c release

    log_success "Swift app built"
}

# ============================================================================
# STEP 6: Create App Bundle
# ============================================================================

create_app_bundle() {
    log_step "Creating App Bundle..."

    # Remove old bundle
    rm -rf "$APP_DIR"

    # Create structure
    mkdir -p "$APP_DIR/Contents/MacOS"
    mkdir -p "$APP_DIR/Contents/Resources"

    # Copy executable
    cp "$BUILD_DIR/TLAStudio" "$APP_DIR/Contents/MacOS/TLAStudio"

    # Copy icon
    if [ -f "$PROJECT_DIR/Sources/TLAStudioApp/Resources/AppIcon.icns" ]; then
        cp "$PROJECT_DIR/Sources/TLAStudioApp/Resources/AppIcon.icns" "$APP_DIR/Contents/Resources/"
    fi

    # Copy resource bundle
    if [ -d "$BUILD_DIR/TLAStudio_TLAStudioApp.bundle" ]; then
        cp -R "$BUILD_DIR/TLAStudio_TLAStudioApp.bundle" "$APP_DIR/Contents/Resources/"
    fi

    # Set executable permissions
    log_info "Setting permissions..."
    find "$APP_DIR" -name "tlc-native*" -exec chmod +x {} \;
    find "$APP_DIR" -name "tlapm" -exec chmod +x {} \;
    find "$APP_DIR" -name "z3" -exec chmod +x {} \;
    find "$APP_DIR" -name "zenon" -exec chmod +x {} \;

    # Create PkgInfo
    echo -n "APPL????" > "$APP_DIR/Contents/PkgInfo"

    # Create Info.plist
    cat > "$APP_DIR/Contents/Info.plist" << PLIST
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
    <string>$VERSION</string>
    <key>CFBundleShortVersionString</key>
    <string>$VERSION</string>
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

    log_success "App bundle created"
}

# ============================================================================
# STEP 7: Code Signing (Optional)
# ============================================================================

sign_app() {
    log_step "Code Signing..."

    # Find Developer ID
    IDENTITY=$(security find-identity -v -p codesigning | grep "Developer ID Application" | head -1 | sed 's/.*"\(.*\)".*/\1/')

    if [ -z "$IDENTITY" ]; then
        log_error "No Developer ID found. Skipping code signing."
        return
    fi

    log_info "Signing with: $IDENTITY"

    # Sign all executables
    find "$APP_DIR" -type f -perm +111 -exec codesign --force --options runtime --sign "$IDENTITY" {} \;

    # Sign the app bundle
    codesign --force --options runtime --sign "$IDENTITY" "$APP_DIR"

    # Verify
    codesign --verify --deep --strict "$APP_DIR" && log_success "Code signing verified" || log_error "Code signing verification failed"
}

# ============================================================================
# STEP 8: Notarization (Optional)
# ============================================================================

notarize_app() {
    log_step "Notarizing..."

    # Create ZIP for notarization
    NOTARIZE_ZIP="$BUILD_DIR/TLAStudio-notarize.zip"
    ditto -c -k --keepParent "$APP_DIR" "$NOTARIZE_ZIP"

    log_info "Submitting for notarization..."
    xcrun notarytool submit "$NOTARIZE_ZIP" --keychain-profile "AC_PASSWORD" --wait

    # Staple ticket
    xcrun stapler staple "$APP_DIR"

    rm -f "$NOTARIZE_ZIP"
    log_success "Notarization complete"
}

# ============================================================================
# STEP 9: Create DMG (Optional)
# ============================================================================

create_dmg() {
    log_step "Creating DMG Installer..."

    DMG_DIR="$BUILD_DIR/dmg"
    DMG_PATH="$BUILD_DIR/TLA+Studio-$VERSION.dmg"

    rm -rf "$DMG_DIR"
    mkdir -p "$DMG_DIR"

    # Copy app
    cp -R "$APP_DIR" "$DMG_DIR/"

    # Create symlink to Applications
    ln -s /Applications "$DMG_DIR/Applications"

    # Create DMG
    hdiutil create -volname "TLA+ Studio" -srcfolder "$DMG_DIR" -ov -format UDZO "$DMG_PATH"

    rm -rf "$DMG_DIR"

    log_success "DMG created: $DMG_PATH"
}

# ============================================================================
# Main Build Process
# ============================================================================

main() {
    echo ""
    echo -e "${GREEN}╔════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║          TLA+ Studio Production Build                      ║${NC}"
    echo -e "${GREEN}║          Version: $VERSION                                    ║${NC}"
    echo -e "${GREEN}╚════════════════════════════════════════════════════════════╝${NC}"
    echo ""

    START_TIME=$(date +%s)

    # Step 1: Prerequisites
    if [ "$SKIP_PREREQS" = false ]; then
        install_prerequisites
    else
        log_step "Skipping prerequisite installation"
    fi

    # Step 2: Build TLC
    if [ "$SKIP_TLC" = false ]; then
        build_tlc_native
    else
        log_step "Skipping TLC build"
    fi

    # Step 3: Build TLAPM
    if [ "$SKIP_TLAPM" = false ]; then
        build_tlapm
    else
        log_step "Skipping TLAPM build"
    fi

    # Step 4: Build Rust Core
    build_rust_core

    # Step 5: Build Swift App
    build_swift_app

    # Step 6: Create App Bundle
    create_app_bundle

    # Step 7: Code Signing
    if [ "$DO_SIGN" = true ]; then
        sign_app
    fi

    # Step 8: Notarization
    if [ "$DO_NOTARIZE" = true ]; then
        notarize_app
    fi

    # Step 9: Create DMG
    if [ "$CREATE_DMG" = true ]; then
        create_dmg
    fi

    # Done!
    END_TIME=$(date +%s)
    DURATION=$((END_TIME - START_TIME))

    echo ""
    echo -e "${GREEN}╔════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║                    Build Complete!                         ║${NC}"
    echo -e "${GREEN}╚════════════════════════════════════════════════════════════╝${NC}"
    echo ""
    echo -e "  ${BLUE}App:${NC}      $APP_DIR"
    echo -e "  ${BLUE}Duration:${NC} ${DURATION}s"
    echo ""
    echo -e "  To run:  ${YELLOW}open \"$APP_DIR\"${NC}"
    echo ""
}

# Run main
main
