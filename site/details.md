# Project details

## Curve25519-dalek

[Curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek) is a pure-Rust implementation of group operations on Curve25519. 
It provides fast, safe cryptographic primitives used by thousands of projects for key agreement, signatures and zero-knowledge proofs.

## Project aims

This project aims to **prove the functional correctness** of the curve25519-dalek implementation. 
Using [Aeneas](https://github.com/AeneasVerif/aeneas), we obtain a faithful representation of the Rust code in [Lean 4](https://lean-lang.org), a powerful proof assistant. This allows us to harness Lean's mathematical capabilities to write precise specifications and formally prove that the implementation satisfies them.

The aims are two fold:

- Formally verify the chosen subset of functions from this crate
- Figure out how formal verification can be done on large scale, quicker, cheaper and commonplace


## Our Progress

Check out the [verification status](status) to see which functions have been verified and track our progress through the codebase.

## The Scalability Challenge

Formal verification has traditionally been resource-intensive and time-consuming. 
**Can we find ways to solve the scalability problem of formal verification?** 

If you're interested in the verification methodology or formal methods at scale, we'd love your insights and contributions.

## Trust Model

Read more about the [trust model](trust), what we need to trust to rely on these proofs

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