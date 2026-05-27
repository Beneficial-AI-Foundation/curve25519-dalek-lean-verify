/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::add`

This function performs element-wise addition of two `FieldElement51` values by wrapping
`add_assign`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
open CoreOpsArithAddAssignSharedAFieldElement51
namespace curve25519_dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithAddSharedAFieldElement51FieldElement51

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::add`**
• The function always succeeds (no panic) provided each pair of limb sums fits in `U64`
• Each output limb equals the sum of the corresponding input limbs (element-wise, no reduction)
• Output bounds: every output limb is `< 2 ^ 54` when both inputs have limbs `< 2 ^ 53`
-/
@[step]
theorem add_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53) (hb : ∀ i < 5, b[i]!.val < 2 ^ 53) :
    add a b ⦃ (result : backend.serial.u64.field.FieldElement51) =>
      (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
      (∀ i < 5, result[i]!.val < 2^54) ⦄ := by
  unfold add
  step*

end CoreOpsArithAddSharedAFieldElement51FieldElement51
end curve25519_dalek.Shared0FieldElement51.Insts
