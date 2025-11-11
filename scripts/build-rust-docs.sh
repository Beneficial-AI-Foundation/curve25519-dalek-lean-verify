#!/bin/bash
# Build Rust documentation with the correct backend configuration
# The RUSTDOCFLAGS must match the configuration in .cargo/config.toml
# Using default features only to match verification scope

set -e

# Set both RUSTFLAGS (for compilation) and RUSTDOCFLAGS (for documentation)
# The backend flags must be in both to ensure vector backend files aren't compiled
export RUSTFLAGS='
  --cfg curve25519_dalek_backend="serial"
  --cfg curve25519_dalek_bits="64"
'

export RUSTDOCFLAGS='
  --cfg docsrs
  --cfg curve25519_dalek_backend="serial"
  --cfg curve25519_dalek_bits="64"
  --html-in-header curve25519-dalek/docs/assets/rustdoc-include-katex-header.html
'

cargo +nightly-2025-07-20 rustdoc \
  -p curve25519-dalek

# Copy generated docs to the site public directory
mkdir -p site/public/doc
cp -r target/doc/* site/public/doc/

echo "Rust documentation built and copied to site/public/doc/"
