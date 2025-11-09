#!/bin/bash
# Build Rust documentation with the correct backend configuration
# The RUSTDOCFLAGS must match the configuration in .cargo/config.toml
# The features list matches package.metadata.docs.rs in Cargo.toml

set -e

RUSTDOCFLAGS='
  --cfg docsrs
  --cfg curve25519_dalek_backend="serial"
  --cfg curve25519_dalek_bits="64"
  --html-in-header curve25519-dalek/docs/assets/rustdoc-include-katex-header.html
' \
cargo +nightly-2025-07-20 rustdoc \
  -p curve25519-dalek \
  --features 'serde rand_core digest legacy_compatibility group-bits'

# Copy generated docs to the site public directory
mkdir -p site/public/doc
cp -r target/doc/* site/public/doc/

echo "Rust documentation built and copied to site/public/doc/"
