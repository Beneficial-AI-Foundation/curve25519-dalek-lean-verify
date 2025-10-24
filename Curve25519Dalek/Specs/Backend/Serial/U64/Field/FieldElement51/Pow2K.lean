import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # pow2k

Specification and proof for `FieldElement51::pow2k`.

This function computes 2^k power of the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs:L374-L456

## TODO
- Write draft specification
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open backend.serial.u64.field

-- Specification theorem to be written here
