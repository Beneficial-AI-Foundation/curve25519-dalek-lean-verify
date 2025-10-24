# Repository Structure

- `curve25519-dalek/` - Original Rust implementation from [dalek-cryptography][dalek]
  - `src/` - Rust source code of curve25519-dalek
- `Curve25519Dalek/` - Lean formalization and proofs
  - `Types.lean` - Type definitions extracted from Rust (**automatically updated by Aeneas and must not be manually edited**)
  - `Funs.lean` - Function definitions extracted from Rust (**automatically updated by Aeneas and must not be manually edited**)
  - `TypesExternal.lean` - Definition of types external to the crate
  - `FunsExternal.lean` - Definition of functions external to the crate
  - `Specs/` - Spec theorems (together with proofs), folder structure coincides with Rust modules
  - `Aux.lean` - Auxiliary lemmas and utilities
  - `Defs.lean` - Spec-specific definitions
  - `Tactics.lean` - Custom tactics
- `site/` - Verification project website source
- `scripts/` - Convenience scripts
<!-- - `Curve25519Dalek.lean` - Main entry point for the Lean project -->
<!-- - `lakefile.toml` - Lean project configuration -->
- `status.csv` - Verification progress tracking
- `src-modifications.diff` - Modifications to the upstream Rust code

[dalek]: https://github.com/dalek-cryptography/curve25519-dalek
