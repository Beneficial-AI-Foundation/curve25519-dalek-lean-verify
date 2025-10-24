/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # Spec Theorem for `FieldElement51::as_bytes`

Specification and proof for `FieldElement51::as_bytes`.

natural language description:

    • Takes a field element fe (five 51-bit limbs stored in U64 values) and
      returns a 32-byte array b that represents the same field element value modulo p
      in little-endian byte representation.

natural language specs:

    • u8x32_to_nat(b) ≡ u64x5_to_nat(fe) (mod p)

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Spec for `as_bytes` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.as_bytes`**:

Function was deprecated since 4.1.4 and renamed to `to_bytes`. Simply calls the other function. -/
@[progress]
theorem as_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    ∃ result, as_bytes self = ok result ∧
    U8x32_as_Nat result ≡ U64x5_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p := by
  unfold as_bytes
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51
