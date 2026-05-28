/-
Copyright (c) 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::ONE`

This constant represents the multiplicative identity element `1` in the field 𝔽_p (p = 2^255 - 19).
It is stored as the five-limb array `[1, 0, 0, 0, 0]`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::ONE`**
• The function always succeeds (no panic)
• `Field51_as_Nat ONE = 1`, the multiplicative identity of 𝔽_p
• Every limb is bounded by `2 ^ 51`
-/
@[step]
theorem ONE_spec :
    ONE ⦃ (result : FieldElement51) =>
      Field51_as_Nat result = 1 ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold ONE from_limbs
  simp only [spec_ok]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51
