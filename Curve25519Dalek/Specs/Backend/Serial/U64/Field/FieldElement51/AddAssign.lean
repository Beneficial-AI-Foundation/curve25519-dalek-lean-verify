/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Funs

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::add_assign`

This function performs element-wise addition of field element limbs.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! ## Spec for `add_assign_loop` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreOpsArithAddAssignSharedAFieldElement51

/-- **Spec theorem for `add_assign_loop`**
• Does not overflow when limb sums don't exceed `U64.max`
• Each limb from index `i` onwards is updated to `self[j] + _rhs[j]`
• Limbs before index `i` are left unchanged
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
    case hmax =>
      have := hab i (by scalar_tac) (le_refl _)
      grind [Array.getElem!_Nat_eq, Array.val_getElem!_eq']
    let* ⟨ a, a_post ⟩ ← Array.update_spec
    let* ⟨ i4, i4_post ⟩ ← Usize.add_spec
    let* ⟨ result, result_post1, result_post2 ⟩ ← add_assign_loop_spec
    case hab =>
      intro j hj hj2
      have := hab j hj (by scalar_tac)
      simp only [a_post, Array.getElem!_Nat_eq, Array.set_val_eq] at *
      grind
    constructor
    · intro j _ _
      obtain h | h := (show j = i ∨ i + 1 ≤ j by omega)
      · subst h
        have hr := result_post2 (↑i) (by scalar_tac) (by scalar_tac)
        simp only [hr, a_post, Array.getElem!_Nat_eq, Array.set_val_eq] at *
        grind [List.getElem_set_self]
      · simp_all
    · intro j hj _
      have := result_post2 j hj (by omega)
      simp_all
  · simp only [step_simps]
    grind
  termination_by 5 - i.val
  decreasing_by scalar_tac

/-! ## Spec for `add_assign` -/

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::add_assign`**
• The function always succeeds (no panic) when both inputs have limbs `< 2 ^ 53`
• Each output limb equals the sum of the corresponding input limbs
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
