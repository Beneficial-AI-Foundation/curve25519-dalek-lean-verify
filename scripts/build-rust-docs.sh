#!/bin/bash
# Build Rust documentation with the correct backend configuration
# The RUSTDOCFLAGS must match the configuration in .cargo/config.toml
# Using default features only to match verification scope

set -e

HERE=$(cd `dirname $0`; pwd)
ROOT=$HERE/..

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
  --html-in-header '"$ROOT/"'curve25519-dalek/docs/assets/rustdoc-include-katex-header.html
'

cargo +nightly-2025-07-20 rustdoc \
  -p curve25519-dalek

# Inject Lean verification panels into the generated rustdoc HTML (in-place
# under target/doc/). Uses functions.json as the per-function record and
# scans Curve25519Dalek/**/*.lean for accurate file:line links.
# See scripts/inject-lean-verification.ts for details.
echo "Injecting Lean verification panels into rustdoc HTML..."
npx tsx "$ROOT/scripts/inject-lean-verification.ts" \
  --rustdoc-root "$ROOT/target/doc" \
  --functions   "$ROOT/functions.json" \
  --source-root "$ROOT"

# Copy generated docs (with panels) to the site public directory
mkdir -p $ROOT/site/public/doc
cp -r $ROOT/target/doc/* $ROOT/site/public/doc/

echo "Rust documentation built and copied to $ROOT/site/public/doc/"
