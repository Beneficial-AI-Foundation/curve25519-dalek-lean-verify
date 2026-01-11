#!/bin/bash

# Extract Lean Script
# Uses Charon to generate LLBC, then Aeneas to produce Lean files

set -e  # Exit on any error

HERE=$(cd `dirname $0`; pwd)
ROOT=$HERE/..

echo "=== Extracting Lean Files from Rust Code ==="
echo

# Configuration
# The main crate we're extracting
CRATE_DIR="curve25519-dalek"
CRATE_NAME="curve25519_dalek"  # Underscored version for LLBC file
CHARON_BIN="$ROOT/aeneas/charon/bin/charon"
AENEAS_BIN="$ROOT/aeneas/bin/aeneas"
OUTPUT_DIR="$ROOT/Curve25519Dalek"
FUNCTIONS_FILE="$ROOT/extract-functions.txt"
TWEAKS_FILE="$ROOT/aeneas-tweaks.txt"

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
        echo "Run the setup script first: $HERE/setup-aeneas.sh"
        exit 1
    fi
    
    if [ ! -f "$AENEAS_BIN" ]; then
        echo "Error: Aeneas not found at $AENEAS_BIN"
        echo "Run the setup script first: $HERE/setup-aeneas.sh"
        exit 1
    fi
    
    echo "✓ Tools found"
    echo
}

# Generate LLBC file using Charon
generate_llbc() {
    echo "Step 1: Generating LLBC file with Charon..."
    echo "Using configuration from $ROOT/.cargo/config.toml (serial backend, 64-bit, verify cfg)"
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

    # Items that Charon/Aeneas cannot fully handle:
    # --exclude: completely remove (for items we don't need)
    # --opaque: keep signature but no body (for items that crash but may be referenced)
    EXCLUDE_ARGS=(
        --exclude 'curve25519_dalek::backend::serial::curve_models::{impl core::fmt::Debug for _}'
        --exclude 'curve25519_dalek::scalar::{impl core::fmt::Debug for _}'
        # bits_le: uses iterator .map() which pulls in mutually recursive traits
        # NOTE: Montgomery scalar multiplication was rewritten to avoid this, so bits_le is now unused
        --exclude 'curve25519_dalek::scalar::Scalar::bits_le'
        # batch_invert: pulls in Vec/slice iterator machinery
        --exclude 'curve25519_dalek::scalar::Scalar::batch_invert'
        # Product/Sum impls: pull in mutually recursive iterator traits
        --exclude 'curve25519_dalek::scalar::{impl core::iter::Product<_> for _}'
        --exclude 'curve25519_dalek::scalar::{impl core::iter::Sum<_> for _}'
        # Hash traits: not needed for cryptographic verification, causes Aeneas syntax issues
        --exclude 'core::hash::Hash'
        --exclude 'core::hash::Hasher'
        --exclude 'core::array::{impl core::hash::Hash for _}'
        --exclude 'core::hash::impls::{impl core::hash::Hash for _}'
        --exclude 'curve25519_dalek::scalar::{impl core::hash::Hash for _}'
    )
    OPAQUE_ARGS=(
        # non_adjacent_form/as_radix_2w: dynamic array indexing causes Aeneas internal error
        --opaque 'curve25519_dalek::scalar::Scalar::non_adjacent_form'
        --opaque 'curve25519_dalek::scalar::Scalar::as_radix_2w'
    )

    echo "Running: $CHARON_BIN cargo --preset=aeneas ${START_FROM_ARGS[*]} ${EXCLUDE_ARGS[*]} ${OPAQUE_ARGS[*]} -- -p $CRATE_DIR"
    echo "Extracting ${#START_FROM[@]} item(s) and their dependencies"
    echo "Logging output to $ROOT/.logs/charon.log"
    "$CHARON_BIN" cargo --preset=aeneas "${START_FROM_ARGS[@]}" "${EXCLUDE_ARGS[@]}" "${OPAQUE_ARGS[@]}" -- -p "$CRATE_DIR" 2>&1 | tee $ROOT/.logs/charon.log

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
    echo "Logging output to $ROOT/.logs/aeneas.log"
    "$AENEAS_BIN" -backend lean -split-files -dest "$OUTPUT_DIR" "$LLBC_FILE" 2>&1 | tee $ROOT/.logs/aeneas.log

    echo "✓ Lean files generated in $OUTPUT_DIR"
    echo
}

# Quote a string to be used as a sed regex.
# This is used to properly escape any 'raw' search strings in the
# tweaks file by turning the input into a proper (but inefficient)
# regular expression.
quoteRe() { sed -e 's/[^^]/[&]/g; s/\^/\\^/g; $!a\'$'\n''\\n' <<< "$1" | tr -d '\n'; }

# Quote a string to be used as the target for replacement with sed.
# This properly escapes sed's supported shortcuts for referencing the
# string / match groups.
quoteSubst() {
  IFS= read -d '' -r < <(sed -e ':a' -e '$!{N;ba' -e '}' -e 's/[&/\]/\\&/g; s/\n/\\&/g' <<<"$1") || true
  printf %s "${REPLY%$'\n'}"
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

    # Validate that tweaks file ends with at least two blank lines
    # (needed so the last substitution block is processed correctly)
    # Note: We append 'x' to prevent command substitution from stripping trailing newlines
    local ending=$(tail -c 2 "$tweaks_file"; echo x)
    ending=${ending%x}
    if [[ "$ending" != $'\n\n' ]]; then
        echo "⚠ Warning: $tweaks_file does not end with at least two blank lines!"
        echo "  The last substitution may not be processed correctly."
        echo "  Please ensure there are at least two blank lines at the end of the file."
    fi

    local content=$(cat "$input_file")
    local find_text=""
    local replace_text=""
    local in_find=false
    local in_replace=false
    local use_regex=false

    while IFS= read -r line; do
        if [[ "$line" == "===FIND===" ]]; then
            in_find=true
            in_replace=false
            use_regex=false
            find_text=""
        elif [[ "$line" == "===FIND_REGEX===" ]]; then
            in_find=true
            in_replace=false
            use_regex=true
            find_text=""
        elif [[ "$line" == "===REPLACE===" ]]; then
            in_find=false
            in_replace=true
            replace_text=""
        elif [[ "$line" == "" ]] && [[ "$in_replace" == true ]]; then
            # End of a substitution block - apply it
            if [[ "$use_regex" == false ]]; then
                find_text=$(quoteRe "$find_text")
            fi
            content=$(sed -e ':a' -e '$!{N;ba' -e '}' -e "s/$find_text/$(quoteSubst "$replace_text")/g" <<< "$content")
            in_replace=false
            find_text=""
            replace_text=""
            use_regex=false
        elif [[ "$in_find" == true ]]; then
            find_text="${find_text}${find_text:+$'\n'}${line}"
        elif [[ "$in_replace" == true ]]; then
            replace_text="${replace_text}${replace_text:+$'\n'}${line}"
        fi
    done < "$tweaks_file"

    echo "$content" > "$input_file"
    echo "✓ Tweaks applied to $input_file"
}

# Update lean-toolchain to match Aeneas
sync_toolchain() {
    echo "Step 3: Synchronizing Lean toolchain..."
    
    if [ -f "$HERE/update-lean-toolchain.sh" ]; then
        $HERE/update-lean-toolchain.sh
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

    # Apply tweaks to generated Lean files if tweaks file exists
    if [ -f "$TWEAKS_FILE" ]; then
        apply_tweaks "$OUTPUT_DIR/Funs.lean" "$TWEAKS_FILE"
        apply_tweaks "$OUTPUT_DIR/Types.lean" "$TWEAKS_FILE"
    fi

    sync_toolchain

    echo "=== Extraction Complete! ==="
    echo
    echo "Generated files:"
    echo "- LLBC file: $LLBC_FILE"
    echo "- Lean files: $OUTPUT_DIR/"
}

# Run the main function
main "$@"
