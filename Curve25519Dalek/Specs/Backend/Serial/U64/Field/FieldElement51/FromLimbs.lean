/-
Copyright (c) 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::from_limbs`

This function constructs a `FieldElement51` from an array of five `u64` limbs.
Since `FieldElement51` is just a type alias for `Array U64 5#usize`, this is essentially the
identity wrapped in `Result`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::from_limbs`**
• The function always succeeds (no panic)
• The result is identical to the input limbs array
• `Field51_as_Nat result = Field51_as_Nat a` (trivially, since `result = a`)
-/
@[step]
theorem from_limbs_spec (a : Array U64 5#usize) :
    from_limbs a ⦃ (r : FieldElement51) =>
      r = a ∧ Field51_as_Nat r = Field51_as_Nat a ⦄ := by
  simp [from_limbs]

end curve25519_dalek.backend.serial.u64.field.FieldElement51
