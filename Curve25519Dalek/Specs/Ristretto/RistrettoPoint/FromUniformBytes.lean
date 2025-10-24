import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # from_uniform_bytes

Specification and proof for `RistrettoPoint::from_uniform_bytes`.

This function constructs a point from uniform random bytes.

**Source**: curve25519-dalek/src/ristretto.rs:L786-L803

## TODO
- Write draft specification
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek

-- Specification theorem to be written here
