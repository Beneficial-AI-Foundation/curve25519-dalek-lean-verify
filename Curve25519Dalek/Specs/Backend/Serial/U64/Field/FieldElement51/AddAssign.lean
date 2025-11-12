/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs

/-! # AddAssign

Specification and proof for `FieldElement51::add_assign`.

This function performs element-wise addition of field element limbs.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas.Std Result

set_option linter.hashCommand false
#setup_aeneas_simps

/-! ## Spec for `add_assign_loop` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.AddAssign

/-- **Spec for `backend.serial.u64.field.FieldElement51.add_assign_loop`**:
- Iterates through limbs adding `b[i]` to `a[i]`
- Does not overflow if limb sums don't exceed `U64.max`. -/
@[progress]
theorem add_assign_loop_spec (a b : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (hab : ∀ (j : Nat), j < 5 → i.val ≤ j → a[j]!.val + b[j]!.val ≤ U64.max) :
    ∃ a', add_assign_loop a b i = ok a' ∧
    (∀ (j : Nat), j < 5 → i.val ≤ j → a'[j]!.val = a[j]!.val + b[j]!.val) ∧
    (∀ (j : Nat), j < 5 → j < i.val → a'[j]! = a[j]!) := by
  unfold add_assign_loop
  split
  · progress*
    · have := hab i (by scalar_tac) (by simp)
      scalar_tac
    · intro j hj _
      have := hab j hj
      have := hab j (by scalar_tac) (by omega)
      have : ↑i ≠ j := by scalar_tac
      simp_all
    · refine ⟨?_, ?_⟩
      · intro j hj _
        obtain hc | hc := (show j = i ∨ i + 1 ≤ j by omega)
        · simp_all
        · have := res_post_1 j hj (by omega)
          have : ↑i ≠ j := by omega
          simp_all [Array.getElem!_Nat_eq, Array.set_val_eq]
      · intro j hj _
        have := res_post_2 j hj (by omega)
        simp_all
  · use a
    simp only [implies_true, and_true, true_and]
    intro j hj _
    have : j = 5 := by scalar_tac
    omega
  termination_by 5 - i.val
  decreasing_by scalar_decr_tac

/-! ## Spec for `add_assign` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.add_assign`**:
- Does not overflow when limb sums don't exceed `U64.max`
- Returns a field element where each limb is the sum of corresponding input limbs -/
@[progress]
theorem add_assign_spec (a b : Array U64 5#usize)
    (hab : ∀ i, i < 5 → (a[i]!).val + (b[i]!).val ≤ U64.max) :
    ∃ result, add_assign a b = ok result ∧
    (∀ i, i < 5 → (result[i]!).val = (a[i]!).val + (b[i]!).val) := by
  unfold add_assign
  progress*
  · intro i hi
    simpa using hab i hi
  · intro i hi
    simpa using res_post_1 i hi (by simp)

end curve25519_dalek.backend.serial.u64.field.FieldElement51.AddAssign
