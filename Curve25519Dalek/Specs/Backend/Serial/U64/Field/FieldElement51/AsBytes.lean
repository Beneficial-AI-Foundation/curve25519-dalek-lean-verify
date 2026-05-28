/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::as_bytes`

This function takes a `FieldElement51` (five 51-bit limbs packed in `U64` values) and returns
a 32-byte little-endian array representing the same field element value modulo `p`. It was
deprecated in version 4.1.4 and now simply delegates to `to_bytes`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::as_bytes`**
• The function always succeeds (no panic)
• `U8x32_as_Nat result ≡ Field51_as_Nat self (mod p)`, i.e. byte and limb encodings agree mod `p`
• The returned 32-byte value, viewed as a natural number, is canonical (`< p`)
-/
@[step]
theorem as_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    as_bytes self ⦃ (result : Array U8 32#usize) =>
      U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
      U8x32_as_Nat result < p ⦄ := by
  unfold as_bytes
  step*

end curve25519_dalek.backend.serial.u64.field.FieldElement51
