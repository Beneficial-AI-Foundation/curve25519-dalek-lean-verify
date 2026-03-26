/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Liao Zhang
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M


set_option exponentiation.threshold 416

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `mul_internal` -/

set_option maxHeartbeats 400000 in -- heavy simp
/-- **Spec for `backend.serial.u64.scalar.Scalar52.mul_internal`**:
- The result represents the product of the two input field elements
- Requires that each input limb is at most 62 bits to prevent overflow -/
@[progress]
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    mul_internal a b ⦃ (result : Array U128 9#usize) =>
      Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b ∧
      (∀ i < 9, result[i]!.val < 2 ^ 127) ⦄ := by
  unfold mul_internal
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  progress*
  constructor
  · simp only [Scalar52_wide_as_Nat, Array.getElem!_Nat_eq, Array.set_val_eq, Array.repeat_val,
    UScalar.ofNatCore_val_eq, List.reduceReplicate, List.set_cons_zero, List.set_cons_succ,
    List.getElem!_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    mul_zero, pow_zero, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, List.Vector.length_val, getElem!_pos,
    one_mul, mul_one, Nat.one_lt_ofNat, List.getElem_cons_succ, Nat.reduceMul, Nat.reduceLT,
    Nat.lt_add_one, Scalar52_as_Nat, result_post, z8_post, z7_post, z6_post, z5_post, z4_post,
    z3_post, z2_post, z1_post, i2_post, i_post, i1_post, i7_post, i4_post, i3_post, i6_post,
    i5_post, i14_post, i11_post, i9_post, i8_post, i10_post, i13_post, i12_post, i23_post, i20_post,
    i18_post, i16_post, i15_post, i17_post, i19_post, i22_post, i21_post, i34_post, i31_post,
    i29_post, i27_post, i25_post, i24_post, i26_post, i28_post, i30_post, i33_post, i32_post,
    i41_post, i39_post, i37_post, i35_post, i36_post, i38_post, i40_post, i46_post, i44_post,
    i42_post, i43_post, i45_post, i49_post, i47_post, i48_post, i50_post]
    ring
  · intro i hi
    have := ha 0 (by simp); have := hb 0 (by simp)
    have := ha 1 (by simp); have := hb 1 (by simp)
    have := ha 2 (by simp); have := hb 2 (by simp)
    have := ha 3 (by simp); have := hb 3 (by simp)
    have := ha 4 (by simp); have := hb 4 (by simp)
    interval_cases i
    all_goals simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem!_pos,
      Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one, Array.set_val_eq, Array.repeat_val,
      List.reduceReplicate, List.set_cons_zero, List.set_cons_succ, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ,
      gt_iff_lt, i_post, i1_post,
      i3_post, i5_post, i4_post, i6_post, z1_post, i8_post, i9_post, i10_post, i12_post, i11_post,
      i13_post, z2_post, i15_post, i16_post, i17_post, i18_post, i19_post, i21_post, i20_post,
      i22_post, z3_post, i24_post, i25_post, i26_post, i27_post, i28_post, i29_post, i30_post,
      i32_post, i31_post, i33_post, z4_post, i35_post, i36_post, i37_post, i38_post, i39_post,
      i40_post, z5_post, i42_post, i43_post, i44_post, i45_post, z6_post, i47_post, i48_post,
      z7_post, z8_post, result_post, hi, i2_post] at *
    all_goals grind =>
        instantiate approx
        try lia


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
