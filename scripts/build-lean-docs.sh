#!/bin/bash
# Build Lean documentation using doc-gen4
# This generates API documentation for the Curve25519Dalek Lean library and all dependencies

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
DOCBUILD_DIR="$PROJECT_ROOT/docbuild"

echo "Building Lean documentation..."

# Ensure docbuild directory exists and has the toolchain
if [ ! -f "$DOCBUILD_DIR/lakefile.toml" ]; then
    echo "Error: docbuild/lakefile.toml not found. Please set up the docbuild directory first."
    exit 1
fi

# Copy lean-toolchain to docbuild if not present
if [ ! -f "$DOCBUILD_DIR/lean-toolchain" ]; then
    cp "$PROJECT_ROOT/lean-toolchain" "$DOCBUILD_DIR/"
fi

cd "$DOCBUILD_DIR"

# Update dependencies if needed
echo "Updating Lake dependencies..."
lake update Curve25519Dalek

# Build the documentation
echo "Building documentation (this may take a while on first run)..."
lake build Curve25519Dalek:docs

# Copy all generated docs to the site public directory
echo "Copying documentation to site/public/lean-doc/"
rm -rf "$PROJECT_ROOT/site/public/lean-doc"
cp -r "$DOCBUILD_DIR/.lake/build/doc" "$PROJECT_ROOT/site/public/lean-doc"

echo "Lean documentation built and copied to site/public/lean-doc/"
echo "View locally at: file://$PROJECT_ROOT/site/public/lean-doc/index.html"
