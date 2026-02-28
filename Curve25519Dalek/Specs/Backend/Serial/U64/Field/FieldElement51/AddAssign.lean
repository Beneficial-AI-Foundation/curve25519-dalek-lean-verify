/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs

/-! # AddAssign

Specification and proof for `FieldElement51::add_assign`.

This function performs element-wise addition of field element limbs.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

set_option linter.hashCommand false
#setup_aeneas_simps

/-! ## Spec for `add_assign_loop` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51

/-- **Spec for `backend.serial.u64.field.AddAssignFieldElement51SharedAFieldElement51.add_assign_loop`**:
- Iterates through limbs adding `b[i]` to `a[i]`
- Does not overflow if limb sums don't exceed `U64.max`. -/
@[progress]
theorem add_assign_loop_spec (self _rhs : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (hab : ∀ j < 5, i.val ≤ j → self[j]!.val + _rhs[j]!.val ≤ U64.max) :
    add_assign_loop self _rhs i ⦃ (result : FieldElement51) =>
      (∀ j < 5, i.val ≤ j → result[j]!.val = self[j]!.val + _rhs[j]!.val) ∧
      (∀ j < 5, j < i.val → result[j]! = self[j]!) ⦄ := by
  unfold add_assign_loop
  split
  · progress*
    constructor
    · intro j _ _
      obtain _ | _ := (show j = i ∨ i + 1 ≤ j by omega) <;> simp_all
    · intro j hj _
      have := res_post_2 j hj (by omega)
      simp_all
  · progress*
  termination_by 5 - i.val
  decreasing_by scalar_tac

/-! ## Spec for `add_assign` -/

/-- **Spec for `backend.serial.u64.field.AddAssignFieldElement51SharedAFieldElement51.add_assign`**:
- Does not overflow when limb sums don't exceed `U64.max`
- Returns a field element where each limb is the sum of corresponding input limbs
- Input bounds: both inputs have limbs < 2^53
- Output bounds: output has limbs < 2^54 -/
@[progress]
theorem add_assign_spec (self _rhs : Array U64 5#usize)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 53) (hb : ∀ i < 5, _rhs[i]!.val < 2 ^ 53) :
    add_assign self _rhs ⦃ (result : FieldElement51) =>
      (∀ i < 5, (result[i]!).val = (self[i]!).val + (_rhs[i]!).val) ∧
      (∀ i < 5, result[i]!.val < 2 ^ 54) ⦄ := by
  unfold add_assign
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51
