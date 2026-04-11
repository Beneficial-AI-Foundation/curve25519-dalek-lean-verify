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
#setup_aeneas_simps

/-! ## Spec for `reduce` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

@[step]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ result => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  step*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

set_option maxHeartbeats 1000000 in -- heavy step, scalar_tac and simp_all's
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
  · simp_lists [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]
    scalar_tac
  · simp_lists [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]
    scalar_tac
  · simp_lists [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]
    scalar_tac
  · simp_lists [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]
    scalar_tac
  · simp_lists [*, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod]
    scalar_tac
  · rw [UScalar.val_and] at *
    expand_array limbs10
    simp_lists at hlimbs100 hlimbs101 hlimbs102 hlimbs103 hlimbs104
    simp only [*] at hlimbs100 hlimbs101 hlimbs102 hlimbs103 hlimbs104
    simp_lists at hlimbs100 hlimbs101 hlimbs102 hlimbs103 hlimbs104

    -- prove the bounds: (∀ i < 5, result[i]!.val < 2 ^ 52)

    -- prove: Field51_as_Nat limbs = Field51_as_Nat limbs10 + c4 * p
    -- where c4 = limbs[4].val >>> 51 = limbs[4].val / 2^51

    -- then uses these two facts to quickly derive the conclusion
    refine ⟨?_, ?_, ?_⟩
    · -- from above
      sorry
    · simp [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, p, *]
      scalar_tac
    · sorry





    -- constructor
    -- · intro i _
    --   interval_cases i
    --   all_goals simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
    --     UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, Nat.one_lt_ofNat, Nat.reduceLT,
    --     Nat.lt_add_one, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, Array.set_val_eq,
    --     List.length_set, ne_eq, zero_ne_one, not_false_eq_true, List.getElem_set_ne,
    --     OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero, one_ne_zero,
    --     List.getElem_set_self, OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.ofNat_pos,
    --     Array.getElem!_Nat_eq]; scalar_tac
    -- · simp only [Nat.ModEq, Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    --   Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
    --   List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
    --   Option.getD_some, one_mul, mul_one, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
    --   Nat.lt_add_one, p, Array.set_val_eq, List.length_set, ne_eq, OfNat.ofNat_ne_zero,
    --   not_false_eq_true, List.getElem_set_ne, one_ne_zero, List.getElem_set_self, getElem!_pos,
    --   UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, OfNat.ofNat_ne_one, zero_ne_one,
    --   Nat.reduceEqDiff, Nat.succ_ne_self, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, limbs10_post,
    --   limbs9_post, limbs8_post, limbs7_post, limbs6_post, limbs5_post, limbs4_post, limbs3_post,
    --   limbs2_post, limbs1_post, i17_post, i16_post, i6_post1, i_post, i5_post, i15_post, c4_post1,
    --   i4_post, i19_post, i18_post, i8_post1, i7_post, c0_post1, i21_post, i20_post, i10_post1,
    --   i9_post, c1_post1, i1_post, i23_post, i22_post, i12_post1, i11_post, c2_post1, i2_post,
    --   i25_post, i24_post, i14_post1, i13_post, c3_post1, i3_post]; scalar_tac

end curve25519_dalek.backend.serial.u64.field.FieldElement51
