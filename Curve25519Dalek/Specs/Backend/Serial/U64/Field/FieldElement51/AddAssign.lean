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

open Aeneas
open scoped Aeneas
open Aeneas.Std Result

set_option linter.hashCommand false
#setup_aeneas_simps

/-! ## Spec for `add_assign_loop` -/

namespace curve25519_dalek.backend.serial.u64.field.AddAssignFieldElement51SharedAFieldElement51

/-- **Spec for `backend.serial.u64.field.AddAssignFieldElement51SharedAFieldElement51.add_assign_loop`**:
- Iterates through limbs adding `b[i]` to `a[i]`
- Does not overflow if limb sums don't exceed `U64.max`. -/
@[progress]
theorem add_assign_loop_spec (a b : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (hab : ∀ j < 5, i.val ≤ j → a[j]!.val + b[j]!.val ≤ U64.max) :
    add_assign_loop a b i ⦃ a' =>
      (∀ j < 5, i.val ≤ j → a'[j]!.val = a[j]!.val + b[j]!.val) ∧
      (∀ j < 5, j < i.val → a'[j]! = a[j]!) ⦄ := by
  sorry

/-! ## Spec for `add_assign` -/

/-- **Spec for `backend.serial.u64.field.AddAssignFieldElement51SharedAFieldElement51.add_assign`**:
- Does not overflow when limb sums don't exceed `U64.max`
- Returns a field element where each limb is the sum of corresponding input limbs
- Input bounds: both inputs have limbs < 2^53
- Output bounds: output has limbs < 2^54 -/
@[progress]
theorem add_assign_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 53) :
    add_assign a b ⦃ result =>
      (∀ i < 5, (result[i]!).val = (a[i]!).val + (b[i]!).val) ∧
      (∀ i < 5, result[i]!.val < 2 ^ 54) ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.field.AddAssignFieldElement51SharedAFieldElement51
