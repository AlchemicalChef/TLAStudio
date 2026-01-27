#!/bin/bash
# Build TLC as GraalVM native images for Apple Silicon
# Produces two binaries:
#   - tlc-native-fast: Epsilon GC, best for small/medium specs (no GC overhead)
#   - tlc-native: SerialGC with PGO, best for large specs

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
OUTPUT_DIR="$PROJECT_DIR/Sources/TLAStudioApp/Resources"

# Use GraalVM 25 (system install) or fall back to GraalVM 21
if [ -d "/Library/Java/JavaVirtualMachines/graalvm-25.jdk/Contents/Home" ]; then
    export GRAALVM_HOME="/Library/Java/JavaVirtualMachines/graalvm-25.jdk/Contents/Home"
elif [ -d "$HOME/.graalvm/graalvm-jdk-21.0.9+7.1/Contents/Home" ]; then
    export GRAALVM_HOME="$HOME/.graalvm/graalvm-jdk-21.0.9+7.1/Contents/Home"
else
    echo "Error: GraalVM not found"
    echo "Install GraalVM: brew install --cask graalvm/tap/graalvm-jdk@25"
    exit 1
fi

export PATH="$GRAALVM_HOME/bin:$PATH"
export JAVA_HOME="$GRAALVM_HOME"

echo "=== Building TLC Native Images ==="
echo "GraalVM: $GRAALVM_HOME"

# Verify GraalVM
if ! command -v native-image &> /dev/null; then
    echo "Error: native-image not found in PATH"
    exit 1
fi

native-image --version

# Download TLA+ tools if needed
TLA_TOOLS_JAR="$SCRIPT_DIR/tla2tools.jar"
if [ ! -f "$TLA_TOOLS_JAR" ]; then
    echo "Downloading TLA+ tools..."
    curl -L -o "$TLA_TOOLS_JAR" \
        "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
fi

mkdir -p "$OUTPUT_DIR"

# Common native-image options
COMMON_OPTS=(
    --no-fallback
    -H:+UnlockExperimentalVMOptions
    -H:ReflectionConfigurationFiles="$SCRIPT_DIR/reflect-config.json"
    -H:DynamicProxyConfigurationFiles="$SCRIPT_DIR/proxy-config.json"
    -H:ConfigurationFileDirectories="$SCRIPT_DIR"
    "-H:IncludeResources=.*\.properties"
    "-H:IncludeResources=.*\.tla"
    "-H:IncludeResources=.*\.class"
    -H:IncludeResourceBundles=tlc2.output.messages
    --enable-url-protocols=https
    -O3
    -march=native
    -jar "$TLA_TOOLS_JAR"
)

# =============================================================================
# Build 1: Epsilon GC (fast, for small/medium specs)
# =============================================================================
echo ""
echo "=== Building tlc-native-fast (Epsilon GC) ==="
echo "Best for: Quick checks, small/medium specs (<1M states)"
echo ""

native-image \
    --gc=epsilon \
    "${COMMON_OPTS[@]}" \
    -o "$OUTPUT_DIR/tlc-native-fast"

echo ""
echo "Built: $OUTPUT_DIR/tlc-native-fast"
ls -lh "$OUTPUT_DIR/tlc-native-fast"

# =============================================================================
# Build 2: SerialGC with PGO (for large specs)
# =============================================================================
echo ""
echo "=== Building tlc-native (SerialGC + PGO) ==="
echo "Best for: Large specs, intensive model checking"
echo ""

# Check if we have existing PGO profile
PGO_PROFILE="$SCRIPT_DIR/tlc-pgo.iprof"

if [ -f "$PGO_PROFILE" ]; then
    echo "Using existing PGO profile: $PGO_PROFILE"
    native-image \
        --pgo="$PGO_PROFILE" \
        "${COMMON_OPTS[@]}" \
        -o "$OUTPUT_DIR/tlc-native"
else
    echo "No PGO profile found. Building instrumented binary first..."

    # Build instrumented binary (without -O3, as required by PGO)
    INSTRUMENT_OPTS=(
        --no-fallback
        --pgo-instrument
        -H:+UnlockExperimentalVMOptions
        -H:ReflectionConfigurationFiles="$SCRIPT_DIR/reflect-config.json"
        -H:DynamicProxyConfigurationFiles="$SCRIPT_DIR/proxy-config.json"
        -H:ConfigurationFileDirectories="$SCRIPT_DIR"
        "-H:IncludeResources=.*\.properties"
        "-H:IncludeResources=.*\.tla"
        "-H:IncludeResources=.*\.class"
        -H:IncludeResourceBundles=tlc2.output.messages
        --enable-url-protocols=https
        -march=native
        -jar "$TLA_TOOLS_JAR"
    )

    native-image \
        "${INSTRUMENT_OPTS[@]}" \
        -o "$OUTPUT_DIR/tlc-native-instrumented"

    echo ""
    echo "Collecting profile data (running sample workload)..."

    # Create a sample spec for profiling
    PROFILE_SPEC=$(mktemp -d)/ProfileSpec.tla
    cat > "$PROFILE_SPEC" << 'EOF'
---- MODULE ProfileSpec ----
EXTENDS Naturals, FiniteSets
CONSTANT N
Nodes == 0..(N-1)
VARIABLES state, token
vars == <<state, token>>
Init == state = [n \in Nodes |-> "idle"] /\ token = 0
PickUp(n) == /\ state[n] = "idle" /\ state' = [state EXCEPT ![n] = "waiting"] /\ UNCHANGED token
Enter(n) == /\ state[n] = "waiting" /\ token = n /\ state' = [state EXCEPT ![n] = "critical"] /\ UNCHANGED token
Exit(n) == /\ state[n] = "critical" /\ state' = [state EXCEPT ![n] = "idle"] /\ token' = (n + 1) % N
Next == \E n \in Nodes: PickUp(n) \/ Enter(n) \/ Exit(n)
TypeOK == /\ \A n \in Nodes: state[n] \in {"idle", "waiting", "critical"} /\ token \in Nodes
Mutex == Cardinality({n \in Nodes: state[n] = "critical"}) <= 1
====
EOF

    PROFILE_CFG=$(mktemp)
    echo -e "CONSTANT N = 12\nINIT Init\nNEXT Next\nINVARIANT TypeOK\nINVARIANT Mutex" > "$PROFILE_CFG"

    # Run instrumented binary to collect profile
    cd "$(dirname "$PROFILE_SPEC")"
    "$OUTPUT_DIR/tlc-native-instrumented" -workers 8 "$(basename "$PROFILE_SPEC")" -config "$PROFILE_CFG" || true

    # Move profile to scripts directory
    if [ -f "default.iprof" ]; then
        mv default.iprof "$PGO_PROFILE"
        echo "Profile saved to: $PGO_PROFILE"
    else
        echo "Warning: No profile generated, building without PGO"
    fi

    # Clean up
    rm -rf "$(dirname "$PROFILE_SPEC")" "$PROFILE_CFG"
    rm -f "$OUTPUT_DIR/tlc-native-instrumented"

    # Build final binary with PGO (if profile exists)
    if [ -f "$PGO_PROFILE" ]; then
        native-image \
            --pgo="$PGO_PROFILE" \
            "${COMMON_OPTS[@]}" \
            -o "$OUTPUT_DIR/tlc-native"
    else
        native-image \
            "${COMMON_OPTS[@]}" \
            -o "$OUTPUT_DIR/tlc-native"
    fi
fi

echo ""
echo "Built: $OUTPUT_DIR/tlc-native"
ls -lh "$OUTPUT_DIR/tlc-native"

# =============================================================================
# Summary
# =============================================================================
echo ""
echo "=== Build Complete ==="
echo ""
echo "Binaries created:"
ls -lh "$OUTPUT_DIR"/tlc-native*
echo ""
echo "Usage:"
echo "  tlc-native-fast  - Epsilon GC, 0% GC overhead, OOMs on very large specs"
echo "  tlc-native       - SerialGC+PGO, handles any size, ~40% GC overhead"
echo ""
echo "TLCProcessManager will auto-select based on estimated state space."
