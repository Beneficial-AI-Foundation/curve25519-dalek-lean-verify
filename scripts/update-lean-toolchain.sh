#!/bin/bash

# Update Lean Toolchain Script
# Checks and synchronizes lean-toolchain files between project root and aeneas/backends/lean/

set -e  # Exit on any error

HOME=$(cd `dirname $0`; pwd)
ROOT=$HOME/..

echo "=== Lean Toolchain Update Script ==="
echo

VERIFY_TOOLCHAIN="$ROOT/lean-toolchain"
AENEAS_TOOLCHAIN="$ROOT/aeneas/backends/lean/lean-toolchain"

# Check if both files exist
if [ ! -f "$VERIFY_TOOLCHAIN" ]; then
    echo "Error: $VERIFY_TOOLCHAIN is missing"
    echo "This file should contain the Lean version specification for your verification project."
    exit 1
fi

if [ ! -f "$AENEAS_TOOLCHAIN" ]; then
    echo "Error: $AENEAS_TOOLCHAIN is missing"
    echo "This file should exist after running the Aeneas setup script."
    echo "Try running: $HERE/setup-aeneas.sh"
    exit 1
fi

# Read the contents of both files
VERIFY_VERSION=$(cat "$VERIFY_TOOLCHAIN" | tr -d '\n\r')
AENEAS_VERSION=$(cat "$AENEAS_TOOLCHAIN" | tr -d '\n\r')

echo "Current Lean versions:"
echo "  $VERIFY_TOOLCHAIN: $VERIFY_VERSION"
echo "  $AENEAS_TOOLCHAIN: $AENEAS_VERSION"
echo

# Compare versions
if [ "$VERIFY_VERSION" = "$AENEAS_VERSION" ]; then
    echo "✓ Both files contain the same Lean version ($VERIFY_VERSION)"
    echo "No update needed."
else
    echo "⚠ Different Lean versions detected"
    echo "Updating $VERIFY_TOOLCHAIN from $AENEAS_TOOLCHAIN"
    echo "Change: $VERIFY_VERSION → $AENEAS_VERSION"
    
    # Update the verify toolchain file
    cp "$AENEAS_TOOLCHAIN" "$VERIFY_TOOLCHAIN"
    
    echo "✓ Update complete"
fi

echo
