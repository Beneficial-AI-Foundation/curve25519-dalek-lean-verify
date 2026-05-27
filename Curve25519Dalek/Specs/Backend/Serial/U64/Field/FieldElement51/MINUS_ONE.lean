/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::MINUS_ONE`

This constant represents the field element `-1`, i.e. the additive inverse of the
multiplicative identity element in the field. Its canonical representative is `p - 1`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::MINUS_ONE`**
• The function always succeeds (no panic)
• `Field51_as_Nat MINUS_ONE = 2^255 - 20 = p - 1`, the canonical representative of `-1 (mod p)`
-/
@[step]
theorem MINUS_ONE_spec : MINUS_ONE ⦃ result => Field51_as_Nat result = p - 1 ⦄ := by
  unfold MINUS_ONE from_limbs
  simp only [spec_ok];
  decide

end curve25519_dalek.backend.serial.u64.field.FieldElement51
