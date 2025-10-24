/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # Spec Theorem for `FieldElement51::as_bytes`

Specification and proof for `FieldElement51::as_bytes`.

This function converts a field element to its byte representation.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Takes a field element fe (five 51-bit limbs stored in U64 values) and
      returns a 32-byte array b that represents the same field element value modulo p
      in little-endian byte representation.

natural language specs:

    • u8x32_to_nat(b) ≡ u64x5_to_nat(fe) (mod p)
-/

/-- **Spec and proof concerning `field.FieldElement51.as_bytes`**:
- No panic (always returns successfully)
- The result byte array represents the same number as the input field element modulo p
-/
theorem as_bytes_spec (fe : FieldElement51) :
    ∃ b,
    as_bytes fe = ok b ∧
    U8x32_as_Nat b % p = U64x5_as_Nat fe % p
    := by
    sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
