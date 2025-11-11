#!/bin/bash

# Aeneas and Charon Setup Script
# This script downloads the Aeneas repo, sets up Charon, and builds both projects

set -e  # Exit on any error

echo "=== Aeneas and Charon Setup Script ==="
echo

# Check if required tools are installed
check_dependencies() {
    echo "Checking dependencies..."

    # Check for git
    if ! command -v git &> /dev/null; then
        echo "Error: git is not installed. Please install git first."
        exit 1
    fi

    # Check for OCaml/opam
    if ! command -v opam &> /dev/null; then
        echo "Error: opam is not installed. Please install OCaml and opam first."
        echo "Follow instructions at: https://ocaml.org/docs/install.html"
        exit 1
    fi

    # Check for make
    if ! command -v make &> /dev/null; then
        echo "Error: make is not installed. Please install make first."
        exit 1
    fi

    # Check for Rust toolchain
    if ! command -v rustup &> /dev/null; then
        if ! command -v nix &> /dev/null; then
            echo "Error: Neither rustup nor nix found. Please install one of them."
            echo "Rustup installation: https://rustup.rs/"
            echo "Nix installation: https://nixos.org/download/"
            exit 1
        else
            echo "✓ Nix found (will be used for Charon)"
        fi
    else
        echo "✓ Rustup found"

        # Check if cargo is available
        if ! command -v cargo &> /dev/null; then
            echo "Error: cargo is not available. Please ensure Rust toolchain is properly installed."
            exit 1
        fi

        # Display Rust version info
        echo "Rust version information:"
        rustc --version
        cargo --version
    fi

    echo "✓ All required dependencies found"
    echo
}

# Setup OCaml environment
setup_ocaml() {
    echo "Setting up OCaml environment..."

    # Check if OCaml switch already exists
    if opam switch list | grep -q "5.2.0"; then
        echo "✓ OCaml 5.2.0 switch already exists"
        opam switch 5.2.0
    else
        echo "Creating OCaml 5.2.0 switch..."
        opam switch create 5.2.0
    fi

    # Update opam environment
    eval "$(opam env)"

    echo "✓ OCaml environment ready"
    echo
}

# Install OCaml dependencies
install_ocaml_deps() {
    echo "Installing OCaml dependencies..."

    # Update opam package list to ensure we have latest package metadata
    echo "Updating opam package list..."
    opam update

    opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix odoc \
        ocamlgraph menhir ocamlformat unionFind domainslib progress

    echo "✓ OCaml dependencies installed"
    echo
}

# Clone Aeneas repository
clone_aeneas() {
    echo "Cloning Aeneas repository..."

    local AENEAS_BRANCH="main"

    if [ -d "aeneas" ]; then
        echo "✓ Aeneas directory already exists, pulling latest changes..."
        cd aeneas
        git fetch origin
        git checkout "$AENEAS_BRANCH"
        git pull origin "$AENEAS_BRANCH"
        cd ..
    else
        git clone --branch "$AENEAS_BRANCH" https://github.com/AeneasVerif/aeneas.git
        echo "✓ Aeneas repository cloned (branch: $AENEAS_BRANCH)"
    fi
    echo
}

# Install Rust nightly toolchain for Charon
install_rust_nightly() {
    local NIGHTLY_VERSION="$1"

    echo "Found Charon toolchain specification: $NIGHTLY_VERSION"
    rustup toolchain install "$NIGHTLY_VERSION"
    rustup component add --toolchain "$NIGHTLY_VERSION" rustfmt
    echo "✓ Installed $NIGHTLY_VERSION with rustfmt"
}

# Setup Charon
setup_charon() {
    echo "Setting up Charon..."

    cd aeneas

    # Display pinned commit if available
    if [ -f "charon-pin" ]; then
        local PINNED_COMMIT
        PINNED_COMMIT=$(tail -1 charon-pin)
        echo "Charon pinned commit: $PINNED_COMMIT"
    fi

    # Install the required nightly toolchain specified by Charon
    echo "Installing required Rust nightly toolchain for Charon..."

    # Check for rust-toolchain.toml (new format) or rust-toolchain (old format)
    if [ -f "charon/charon/rust-toolchain.toml" ]; then
        local NIGHTLY_VERSION
        NIGHTLY_VERSION=$(grep 'channel = ' charon/charon/rust-toolchain.toml | sed 's/.*"\(.*\)".*/\1/')
        install_rust_nightly "$NIGHTLY_VERSION"
    elif [ -f "charon/charon/rust-toolchain" ]; then
        local NIGHTLY_VERSION
        NIGHTLY_VERSION=$(grep 'channel = ' charon/charon/rust-toolchain | sed 's/.*"\(.*\)".*/\1/')
        install_rust_nightly "$NIGHTLY_VERSION"
    else
        echo "Warning: Charon rust-toolchain file not found, using latest nightly"
        rustup toolchain install nightly
        rustup component add --toolchain nightly rustfmt
        echo "✓ Installed nightly with rustfmt"
    fi
    echo

    # Clone and build Charon using the setup-charon target
    # Note: This runs `make test` in charon which builds in debug mode and runs tests
    echo "Cloning Charon and building (this will take a few minutes)..."
    make setup-charon

    echo "✓ Charon setup and build complete"
    echo

    cd .. # Back to original directory
}

# Build Aeneas
build_aeneas() {
    echo "Building Aeneas..."

    cd aeneas

    # Update opam environment in case it changed
    eval "$(opam env)"

    # Build the project
    make

    echo "✓ Aeneas build complete"
    echo

    cd .. # Back to original directory
}

# Main execution
main() {
    echo "Starting Aeneas and Charon setup..."
    echo "Working directory: $(pwd)"
    echo

    check_dependencies
    setup_ocaml
    install_ocaml_deps
    clone_aeneas
    setup_charon
    build_aeneas

    echo "=== Setup Complete! ==="
    echo
    echo "Aeneas has been successfully installed in: $(pwd)/aeneas"
    echo "The Aeneas binary is available at: $(pwd)/aeneas/bin/aeneas"
    echo "The Charon binary is available at: $(pwd)/aeneas/charon/bin/charon"
    echo
    echo "How to use:"
    echo "1. First, generate an LLBC file from your Rust project using Charon:"
    echo "   cd /path/to/your/rust/project"
    echo "   $(pwd)/aeneas/charon/bin/charon cargo --preset=aeneas"
    echo
    echo "2. Then, run Aeneas on the generated LLBC file:"
    echo "   $(pwd)/aeneas/bin/aeneas -backend lean [OPTIONS] your_project.llbc"
    echo
    echo "Available backends: fstar, coq, lean, hol4"
    echo "Use --help for more options: ./aeneas/bin/aeneas --help"
    echo
    echo "You can run tests later with: cd aeneas && make test"
}

# Run the main function
main "$@"
