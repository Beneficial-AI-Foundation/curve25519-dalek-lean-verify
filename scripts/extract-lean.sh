#!/bin/bash

# Extract Lean Script
# Uses Charon to generate LLBC, then Aeneas to produce Lean files

set -e  # Exit on any error

echo "=== Extracting Lean Files from Rust Code ==="
echo

# Configuration
# The main crate we're extracting
CRATE_DIR="curve25519-dalek"
CRATE_NAME="curve25519_dalek"  # Underscored version for LLBC file
CHARON_BIN="./aeneas/charon/bin/charon"
AENEAS_BIN="./aeneas/bin/aeneas"
OUTPUT_DIR="Curve25519Dalek"
FUNCTIONS_FILE="extract-functions.txt"
TWEAKS_FILE="aeneas-tweaks.txt"

# RUSTFLAGS are configured in .cargo/config.toml:
# - curve25519_dalek_backend="serial" (pure Rust implementation without SIMD)
# - curve25519_dalek_bits="64" (64-bit arithmetic)
# - verify (enable functions tagged with #[cfg(verify)])

LLBC_FILE="${CRATE_NAME}.llbc"

# Load functions to extract from file
# Lines starting with # are comments, empty lines are ignored
load_functions() {
    if [ ! -f "$FUNCTIONS_FILE" ]; then
        echo "Error: Functions file not found: $FUNCTIONS_FILE"
        exit 1
    fi

    START_FROM=()
    while IFS= read -r line || [ -n "$line" ]; do
        # Skip empty lines and comments
        if [[ -z "$line" || "$line" =~ ^[[:space:]]*# ]]; then
            continue
        fi
        # Trim whitespace and add to array
        line=$(echo "$line" | xargs)
        if [ -n "$line" ]; then
            START_FROM+=("$line")
        fi
    done < "$FUNCTIONS_FILE"

    if [ ${#START_FROM[@]} -eq 0 ]; then
        echo "Error: No functions found in $FUNCTIONS_FILE"
        exit 1
    fi
}

# Check if required tools exist
check_tools() {
    echo "Checking required tools..."
    
    if [ ! -f "$CHARON_BIN" ]; then
        echo "Error: Charon not found at $CHARON_BIN"
        echo "Run the setup script first: ./scripts/setup-aeneas.sh"
        exit 1
    fi
    
    if [ ! -f "$AENEAS_BIN" ]; then
        echo "Error: Aeneas not found at $AENEAS_BIN"
        echo "Run the setup script first: ./scripts/setup-aeneas.sh"
        exit 1
    fi
    
    echo "✓ Tools found"
    echo
}

# Generate LLBC file using Charon
generate_llbc() {
    echo "Step 1: Generating LLBC file with Charon..."
    echo "Using configuration from .cargo/config.toml (serial backend, 64-bit, verify cfg)"
    echo

    # Create .logs directory if it doesn't exist
    mkdir -p .logs

    # Remove existing LLBC file if it exists
    if [ -f "$LLBC_FILE" ]; then
        echo "Removing existing $LLBC_FILE"
        rm "$LLBC_FILE"
    fi

    # Run Charon to generate LLBC
    # For workspaces, we need to specify which package to extract
    # Charon passes through cargo arguments after the preset

    # Build the --start-from arguments
    START_FROM_ARGS=()
    for item in "${START_FROM[@]}"; do
        START_FROM_ARGS+=(--start-from "$item")
    done

    echo "Running: $CHARON_BIN cargo --preset=aeneas ${START_FROM_ARGS[*]} -- -p $CRATE_DIR"
    echo "Extracting ${#START_FROM[@]} item(s) and their dependencies"
    echo "Logging output to .logs/charon.log"
    "$CHARON_BIN" cargo --preset=aeneas "${START_FROM_ARGS[@]}" -- -p "$CRATE_DIR" 2>&1 | tee .logs/charon.log

    if [ ! -f "$LLBC_FILE" ]; then
        echo "Error: Failed to generate $LLBC_FILE"
        exit 1
    fi
    
    echo "✓ LLBC file generated: $LLBC_FILE"
    echo
}

# Generate Lean files using Aeneas
generate_lean() {
    echo "Step 2: Generating Lean files with Aeneas..."

    # Create output directory if it doesn't exist
    mkdir -p "$OUTPUT_DIR"

    # Run Aeneas to generate Lean files
    echo "Running: $AENEAS_BIN -backend lean -split-files -dest $OUTPUT_DIR $LLBC_FILE"
    echo "Logging output to .logs/aeneas.log"
    "$AENEAS_BIN" -backend lean -split-files -dest "$OUTPUT_DIR" "$LLBC_FILE" 2>&1 | tee .logs/aeneas.log

    echo "✓ Lean files generated in $OUTPUT_DIR"
    echo
}

# Apply tweaks to generated Lean files
apply_tweaks() {
    local input_file="$1"
    local tweaks_file="$2"

    if [ ! -f "$tweaks_file" ]; then
        echo "No tweaks file found at $tweaks_file, skipping tweaks"
        return
    fi

    echo "Applying tweaks from $tweaks_file to $input_file..."

    local content=$(cat "$input_file")
    local find_text=""
    local replace_text=""
    local in_find=false
    local in_replace=false

    while IFS= read -r line; do
        if [[ "$line" == "===FIND===" ]]; then
            in_find=true
            in_replace=false
            find_text=""
        elif [[ "$line" == "===REPLACE===" ]]; then
            in_find=false
            in_replace=true
            replace_text=""
        elif [[ "$line" == "" ]] && [[ "$in_replace" == true ]]; then
            # End of a substitution block - apply it (replaces ALL occurrences)
            content="${content//"$find_text"/"$replace_text"}"
            in_replace=false
            find_text=""
            replace_text=""
        elif [[ "$in_find" == true ]]; then
            find_text="${find_text}${find_text:+$'\n'}${line}"
        elif [[ "$in_replace" == true ]]; then
            replace_text="${replace_text}${replace_text:+$'\n'}${line}"
        fi
    done < "$tweaks_file"

    # Apply last substitution if file doesn't end with blank line
    if [[ "$in_replace" == true ]] && [[ -n "$find_text" ]]; then
        content="${content//"$find_text"/"$replace_text"}"
    fi

    echo "$content" > "$input_file"
    echo "✓ Tweaks applied to $input_file"
}

# Update lean-toolchain to match Aeneas
sync_toolchain() {
    echo "Step 3: Synchronizing Lean toolchain..."
    
    if [ -f "./scripts/update-lean-toolchain.sh" ]; then
        ./scripts/update-lean-toolchain.sh
    else
        echo "⚠ Toolchain sync script not found, skipping"
    fi
    
    echo
}

# Main execution
main() {
    echo "Working directory: $(pwd)"
    echo "Extracting Lean files for crate: $CRATE_DIR (output: ${CRATE_NAME}.llbc)"
    echo

    load_functions
    echo "Loaded ${#START_FROM[@]} function(s) from $FUNCTIONS_FILE"
    echo

    check_tools
    generate_llbc
    generate_lean

    # Apply tweaks to Funs.lean if tweaks file exists
    apply_tweaks "$OUTPUT_DIR/Funs.lean" "$TWEAKS_FILE"

    sync_toolchain

    echo "=== Extraction Complete! ==="
    echo
    echo "Generated files:"
    echo "- LLBC file: $LLBC_FILE"
    echo "- Lean files: $OUTPUT_DIR/"
}

# Run the main function
main "$@"