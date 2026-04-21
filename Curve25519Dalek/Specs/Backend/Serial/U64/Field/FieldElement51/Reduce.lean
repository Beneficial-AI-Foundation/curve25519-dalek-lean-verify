/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Mathlib.Tactic.IntervalCases
import Curve25519Dalek.Tactics.ExpandArray

/-! # Reduce -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

attribute [-simp] Int.reducePow Nat.reducePow
set_option linter.hashCommand false
#setup_aeneas_simps

attribute [local simp_lists_safe] UScalar.val_and Nat.and_two_pow_sub_one_eq_mod

/-! ## Spec for `reduce` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

@[step]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ result => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  step*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

set_option maxHeartbeats 1000000 in -- heavy
/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.reduce`**:
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p.
- The result value is < 2p. -/
@[step]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (result : FieldElement51) =>
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧
      Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] ∧
      Field51_as_Nat result < 2 * p ⦄ := by
  unfold reduce
  step*
  · scalar_tac
  · simp_lists [*]; scalar_tac
  · simp_lists [*]; scalar_tac
  · simp_lists [*]; scalar_tac
  · simp_lists [*]; scalar_tac
  · simp_lists [*]; scalar_tac
  · expand_array limbs10 using [UScalar.val_and]
    have hbounds : ∀ j < 5, limbs10[j]!.val < 2 ^ 52 := by
      intro j _; interval_cases j <;>
        simp only [hlimbs100, hlimbs101, hlimbs102, hlimbs103, hlimbs104,
          Nat.shiftRight_eq_div_pow, Array.getElem!_Nat_eq] at * <;> scalar_tac
    have hexact : Field51_as_Nat limbs = Field51_as_Nat limbs10 + c4.val * p := by
      simp [Field51_as_Nat, Finset.sum_range_succ, p, *, Nat.shiftRight_eq_div_pow]
      omega
    refine ⟨hbounds, by simp [hexact, Nat.ModEq], ?_⟩
    simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, p]
    scalar_tac


end curve25519_dalek.backend.serial.u64.field.FieldElement51
