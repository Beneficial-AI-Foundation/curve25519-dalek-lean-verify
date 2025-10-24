# Project details

## Source Information

This repository contains the curve25519-dalek Rust crate from:
- **Repository**: https://github.com/dalek-cryptography/curve25519-dalek
- **Commit**: `8016d6d9b9cdbaa681f24147e0b9377cc8cef934`
- **Tag**: `curve25519-4.2.0`
- **Version**: 4.2.0

Here we work exclusively with the 64 bit serial backend. I.e., we compile the Rust code with the flags:

```bash
RUSTFLAGS='--cfg curve25519_dalek_backend="serial" --cfg curve25519_dalek_bits="64"' cargo build
```

From this we have chosen a subset of functions which isn't all of those in this crate with this particular choice of backend but it is a useful complete set for typical cryptographic applications.

## Status tracking

- The file `status.csv` is the source of truth for tracking progress of the project, updates to this file should be made when functions are extracted, have specs added or if verification is complete
- The column `extracted` can be empty of have the value `extracted`
- The column `verified`  can be empty or have the values `draft spec`, `specified` or `verified`
    - ✏️ **draft spec** - Draft spec (in natural language) has been added
    - 📋 **specified** - Formal specification in Lean added
    - ✅ **verified** - Function has been formally verified (spec theorem has been proven)


## CI

- CI will automatically update the project site when the file `status.csv` is updated
- Whilst fixes to Aeneas are in progress we sometimes make modifications to the Rust source code in order to enable extraction, the changes are recorded in `src-modifications.diff` and CI checks that this file is updated
- The CI runs Aeneas on the source code and checks that the generated files, `Types.lean` and `Funs.lean` haven't been modified since extraction (not active, to be activated soon)
- CI checks that the Lean project builds without errors. It permits the presence of `sorry` since this often represents work in progress