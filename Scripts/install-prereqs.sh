#!/bin/bash
#
# TLA+ Studio Prerequisites Installer
# ====================================
# Installs all dependencies needed to build and run TLA+ Studio
#
# Usage:
#   ./Scripts/install-prereqs.sh
#

set -e

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_step() { echo -e "\n${BLUE}==>${NC} ${GREEN}$1${NC}"; }
log_info() { echo -e "    ${YELLOW}→${NC} $1"; }
log_success() { echo -e "    ${GREEN}✓${NC} $1"; }

check_command() { command -v "$1" &> /dev/null; }

echo ""
echo -e "${GREEN}TLA+ Studio Prerequisites Installer${NC}"
echo "===================================="
echo ""

# Xcode Command Line Tools
log_step "Xcode Command Line Tools"
if xcode-select -p &> /dev/null; then
    log_success "Already installed"
else
    log_info "Installing..."
    xcode-select --install
    echo "Please complete installation and re-run this script."
    exit 1
fi

# Homebrew
log_step "Homebrew"
if check_command brew; then
    log_success "Already installed"
else
    log_info "Installing..."
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    eval "$(/opt/homebrew/bin/brew shellenv)"
fi

# Rust
log_step "Rust Toolchain"
if check_command rustc; then
    log_success "Already installed ($(rustc --version | cut -d' ' -f2))"
else
    log_info "Installing..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source "$HOME/.cargo/env"
fi

# ARM64 target
if ! rustup target list --installed | grep -q "aarch64-apple-darwin"; then
    log_info "Adding ARM64 target..."
    rustup target add aarch64-apple-darwin
fi

# Graphviz
log_step "Graphviz (for state graph visualization)"
if check_command dot; then
    log_success "Already installed"
else
    log_info "Installing..."
    brew install graphviz
fi

# Z3
log_step "Z3 (SMT solver for proofs)"
if check_command z3; then
    log_success "Already installed"
else
    log_info "Installing..."
    brew install z3
fi

# Java
log_step "Java (for TLC build)"
if check_command java; then
    log_success "Already installed"
else
    log_info "Installing OpenJDK 17..."
    brew install openjdk@17
    sudo ln -sfn /opt/homebrew/opt/openjdk@17/libexec/openjdk.jdk /Library/Java/JavaVirtualMachines/openjdk-17.jdk 2>/dev/null || true
fi

# GraalVM (optional, for TLC native build)
log_step "GraalVM (optional, for TLC native build)"
if check_command native-image; then
    log_success "Already installed"
else
    log_info "Installing..."
    brew install --cask graalvm-jdk 2>/dev/null || log_info "Skipped (optional)"
fi

# OCaml/OPAM (for TLAPM build)
log_step "OCaml/OPAM (for TLAPM build)"
if check_command opam; then
    log_success "Already installed"
else
    log_info "Installing..."
    brew install opam
    opam init -y --disable-sandboxing
fi

echo ""
echo -e "${GREEN}All prerequisites installed!${NC}"
echo ""
echo "Versions:"
echo "  - Rust:     $(rustc --version 2>/dev/null | cut -d' ' -f2 || echo 'not found')"
echo "  - Graphviz: $(dot -V 2>&1 | head -1 || echo 'not found')"
echo "  - Z3:       $(z3 --version 2>/dev/null | head -1 || echo 'not found')"
echo "  - Java:     $(java -version 2>&1 | head -1 || echo 'not found')"
echo "  - OPAM:     $(opam --version 2>/dev/null || echo 'not found')"
echo ""
echo "Next steps:"
echo "  1. Build the app:  ./Scripts/build-production.sh --skip-prereqs"
echo "  2. Or quick build: ./Scripts/build-app.sh"
echo ""
