#!/bin/bash

# Lean Project Setup Script
# This script sets up dependencies and builds the Lean project
# Note: Lake automatically installs Lean via elan if needed

set -e  # Exit on any error

HOME=$(cd `dirname $0`; pwd)
ROOT=$HOME/..

echo "=== Lean Project Setup Script ==="
echo

echo "Project root: $ROOT"
echo "Note: Lean project is co-located with Rust project"
echo

# Check if lakefile.toml exists
if [ ! -f "$ROOT/lakefile.toml" ]; then
    echo "Error: lakefile.toml not found in $ROOT"
    echo "This doesn't appear to be a valid Lean project."
    exit 1
fi

# Function to install elan if not present
install_elan_if_needed() {
    echo "Checking for elan (Lean version manager)..."
    
    if command -v elan &> /dev/null; then
        echo "✓ elan is already installed"
        elan --version
        return 0
    fi
    
    echo "elan not found. Installing elan..."
    
    # Check if curl is available
    if ! command -v curl &> /dev/null; then
        echo "Error: curl is required to install elan but is not available."
        echo "Please install curl first: sudo apt install curl (Ubuntu/Debian) or brew install curl (macOS)"
        exit 1
    fi
    
    # Install elan
    echo "Downloading and installing elan..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    
    # Source the environment to make elan available
    if [ -f "$HOME/.elan/env" ]; then
        source "$HOME/.elan/env"
    fi
    
    # Add to PATH for this session
    export PATH="$HOME/.elan/bin:$PATH"
    
    # Verify installation
    if command -v elan &> /dev/null; then
        echo "✓ elan installed successfully"
        elan --version
    else
        echo "Error: elan installation failed"
        exit 1
    fi
    
    echo
}

# Function to check for curl (needed for elan auto-install)
check_prerequisites() {
    echo "Checking prerequisites..."
    
    # Check if curl is available (needed for elan auto-install)
    if ! command -v curl &> /dev/null; then
        echo "Warning: curl not found. If Lean/elan needs to be installed, you may need curl."
        echo "Consider installing curl first: sudo apt install curl (Ubuntu/Debian) or brew install curl (macOS)"
    else
        echo "✓ curl is available"
    fi
    
    echo
}

# Function to setup the project
setup_project() {
    echo "Setting up Lean project..."
    
    cd "$ROOT"
    
    # Lake will automatically install Lean via elan if needed based on lean-toolchain file
    echo "Lake will automatically install/use Lean based on lean-toolchain file:"
    if [ -f "$ROOT/lean-toolchain" ]; then
        cat $ROOT/lean-toolchain
    else
        echo "Warning: No lean-toolchain file found"
    fi
    echo
    
    # Update dependencies
    echo "Updating dependencies..."
    lake update
    
    # Download precompiled caches (including mathlib)
    echo "Downloading dependency caches..."
    lake exe cache get || {
        echo "Warning: Cache download failed, but continuing with build..."
        echo "This may result in longer compilation times."
    }
    
    # Build the project
    echo "Building project..."
    lake build
    
    echo "✓ Lean project setup complete"
    echo
}

# Function to verify the setup
verify_setup() {
    echo "Verifying setup..."
    
    cd "$ROOT"
    
    # Check if we can build the main target
    if lake build Curve25519Dalek; then
        echo "✓ Project builds successfully"
    else
        echo "Warning: Build verification failed"
        echo "Check for compilation errors in your Lean files"
        return 1
    fi
    
    # Show Lean version if available
    if command -v lean &> /dev/null; then
        echo "✓ Lean version: $(lean --version)"
    fi
    
    echo
}

# Main execution
main() {
    echo "Starting Lean project setup..."
    echo
    
    check_prerequisites
    install_elan_if_needed
    setup_project
    verify_setup
    
    echo "=== Setup Complete! ==="
    echo
    echo "Your Lean project in $ROOT is ready!"
    echo
    echo "Useful commands:"
    echo "  cd $ROOT"
    echo "  lake build              # Build the project"
    echo "  lake exe cache get      # Download/update caches"
    echo "  lake update             # Update dependencies"
    echo "  lake clean              # Clean build artifacts"
    echo
    echo "If this was your first time:"
    echo "- Lake automatically installed Lean via elan"
    echo "- You may need to restart your shell to use 'lean' command directly"
}

# Run the main function
main "$@"
