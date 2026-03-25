/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Mathlib.Tactic.IntervalCases

/-! # Reduce -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `reduce` -/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

@[progress]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ result => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK
  progress*

end curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

set_option maxHeartbeats 400000 in -- heavy progress, scalar_tac and simp_all's
/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.reduce`**:
- All the limbs of the result are small, ≤ 2^(51 + ε)
- The result is equal to the input mod p. -/
@[progress]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (result : FieldElement51) =>
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧
      Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] ⦄ := by
  unfold reduce
  progress*
  · scalar_tac
  · simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq, List.length_set, List.Vector.length_val,
    Nat.ofNat_pos, getElem!_pos, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, List.getElem_set_ne,
    one_ne_zero, List.getElem_set_self, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod,
    Nat.lt_add_one, i16_post, limbs5_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post,
    i6_post1, i_post, i5_post, i15_post, c4_post1, i4_post]; scalar_tac
  · simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq, List.length_set, List.Vector.length_val,
    Nat.one_lt_ofNat, getElem!_pos, ne_eq, zero_ne_one, not_false_eq_true, List.getElem_set_ne,
    OfNat.ofNat_ne_one, List.getElem_set_self, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod,
    Nat.ofNat_pos, i18_post, limbs6_post, limbs5_post, limbs4_post, limbs3_post, limbs2_post,
    limbs1_post, i8_post1, i7_post, i5_post, c0_post1, i_post]; scalar_tac
  · simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq, List.length_set, List.Vector.length_val,
    Nat.reduceLT, getElem!_pos, ne_eq, OfNat.one_ne_ofNat, not_false_eq_true, List.getElem_set_ne,
    OfNat.zero_ne_ofNat, Nat.reduceEqDiff, Nat.succ_ne_self, List.getElem_set_self, UScalar.val_and,
    Nat.and_two_pow_sub_one_eq_mod, Nat.one_lt_ofNat, i20_post, limbs7_post, limbs6_post,
    limbs5_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post, i10_post1, i9_post, i5_post,
    c1_post1, i1_post]; scalar_tac
  · simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq, List.length_set, List.Vector.length_val,
    Nat.reduceLT, getElem!_pos, ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getElem_set_ne,
    OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, Nat.succ_ne_self, List.getElem_set_self,
    UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, i22_post, limbs8_post, limbs7_post,
    limbs6_post, limbs5_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post, i12_post1,
    i11_post, i5_post, c2_post1, i2_post]; scalar_tac
  · simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq, List.length_set, List.Vector.length_val,
    Nat.lt_add_one, getElem!_pos, ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getElem_set_ne,
    OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, List.getElem_set_self, UScalar.val_and,
    Nat.and_two_pow_sub_one_eq_mod, Nat.reduceLT, i24_post, limbs9_post, limbs8_post, limbs7_post,
    limbs6_post, limbs5_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post, i14_post1,
    i13_post, i5_post, c3_post1, i3_post]; scalar_tac
  · constructor
    · intro i _
      interval_cases i
      all_goals simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
        UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, Nat.one_lt_ofNat, Nat.reduceLT,
        Nat.lt_add_one, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, Array.set_val_eq,
        List.length_set, ne_eq, zero_ne_one, not_false_eq_true, List.getElem_set_ne,
        OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, Nat.reduceEqDiff, OfNat.ofNat_ne_zero, one_ne_zero,
        List.getElem_set_self, OfNat.ofNat_ne_one, Nat.succ_ne_self, Nat.ofNat_pos,
        Array.getElem!_Nat_eq]; scalar_tac
    · simp [Field51_as_Nat, Finset.sum_range_succ, p, Nat.ModEq, *]; omega

end curve25519_dalek.backend.serial.u64.field.FieldElement51
