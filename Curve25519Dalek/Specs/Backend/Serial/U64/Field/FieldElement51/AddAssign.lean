/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::add_assign`

This function performs element-wise addition of two `FieldElement51` limb arrays in place.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

set_option linter.hashCommand false
#setup_aeneas_simps

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithAddAssignSharedAFieldElement51

/-! ## Spec for `add_assign_loop` -/

/-- **Spec for the inner loop `add_assign_loop` of `add_assign`**
• Iterates through the limb arrays adding `_rhs[j]` to `self[j]` from index `i` onwards
• Does not overflow when every pairwise limb sum is `≤ U64.max`
-/
@[step]
theorem add_assign_loop_spec (self _rhs : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (hab : ∀ j < 5, i.val ≤ j → self[j]!.val + _rhs[j]!.val ≤ U64.max) :
    add_assign_loop self _rhs i ⦃ (result : FieldElement51) =>
      (∀ j < 5, i.val ≤ j → result[j]!.val = self[j]!.val + _rhs[j]!.val) ∧
      (∀ j < 5, j < i.val → result[j]! = self[j]!) ⦄ := by
  unfold add_assign_loop
  split
  · let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
    let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    let* ⟨ i3, i3_post ⟩ ← U64.add_spec
    let* ⟨ a, a_post ⟩ ← Array.update_spec
    let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
    let* ⟨ result, result_post1, result_post2 ⟩ ← add_assign_loop_spec
    constructor
    · intro j _ _
      obtain _ | _ := (show j = i ∨ i + 1 ≤ j by omega) <;> simp_all
    · intro j hj _
      have := result_post2 j hj (by omega)
      simp_all
  · simp only [step_simps]
    grind
  termination_by 5 - i.val
  decreasing_by scalar_tac

/-! ## Spec for `add_assign` -/

/-- Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::add_assign`
• The function always succeeds (no panic) when both inputs have limbs `< 2 ^ 53`
• Each output limb equals the sum of the corresponding input limbs (element-wise)
• Every output limb is `< 2 ^ 54`
-/
@[step]
theorem add_assign_spec (self _rhs : Array U64 5#usize)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 53) (hb : ∀ i < 5, _rhs[i]!.val < 2 ^ 53) :
    add_assign self _rhs ⦃ (result : FieldElement51) =>
      (∀ i < 5, (result[i]!).val = (self[i]!).val + (_rhs[i]!).val) ∧
      (∀ i < 5, result[i]!.val < 2 ^ 54) ⦄ := by
  unfold add_assign
  step*

end CoreOpsArithAddAssignSharedAFieldElement51
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
