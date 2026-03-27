/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang, Oliver Butterley
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Mathlib.Data.Nat.ModEq


/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

set_option exponentiation.threshold 280

attribute [-simp] Int.reducePow Nat.reducePow

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

set_option maxHeartbeats 300000 in -- heavy simp_all
/-- **Spec for `backend.serial.u64.scalar.Scalar52.add_loop`**:
- Starting from index `i` with accumulator `sum` and carry `carry`
- Computes limb-wise addition with carry propagation
- Result limbs are bounded by 2^52
- Parts of sum before index i are preserved
- The result satisfies the modular arithmetic property -/
@[step]
theorem add_loop_spec (a b sum : Scalar52) (mask carry : U64) (i : Usize)
    (ha : ∀ j < 5, a[j]!.val < 2 ^ 52) (hb : ∀ j < 5, b[j]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < 2 ^ 259) (hb' : Scalar52_as_Nat b < 2 ^ 259)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5)
    (hcarry : i.val = 5 → carry.val < 2 ^ 52)
    (hcarry' : ∀ i < 5, carry.val < 2 ^ 53)
    (hsum : ∀ j < 5, sum[j]!.val < 2 ^ 52)
    (hsum' : ∀ j < 5, i.val ≤ j → sum[j]!.val = 0) :
    add_loop a b sum mask carry i ⦃ (sum' : Scalar52) =>
      (∀ j < 5, sum'[j]!.val < 2 ^ 52) ∧
      (∀ j < i.val, sum'[j]!.val = sum[j]!.val) ∧
      ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * sum'[j]!.val =
        ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) +
        2 ^ (52 * i.val) * (carry.val / 2 ^ 52) ⦄ := by
  unfold add_loop
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  step*
  · have := ha i (by agrind)
    have := hb i (by agrind)
    scalar_tac
  · intro hi
    have : i.val = 4 := by agrind
    have : a[4]!.val < 2 ^ 51 := by agrind [Scalar52_top_limb_lt_of_as_Nat_lt]
    have : b[4]!.val < 2 ^ 51 := by agrind [Scalar52_top_limb_lt_of_as_Nat_lt]
    simp only [List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.lt_add_one, getElem!_pos,
      gt_iff_lt, *]
    have : carry.val >>> 52 ≤ 1 := by have := hcarry' i (by agrind); omega
    simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, UScalar.lt_equiv,
      UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, UScalar.val_and,
      List.Vector.length_val, Nat.lt_add_one, getElem!_pos, gt_iff_lt] at *; agrind
  · intro j hj
    have : carry.val >>> 52 ≤ 1 := by have := hcarry' i (by agrind); omega
    have := ha i (by agrind)
    have := hb i (by agrind)
    simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, UScalar.lt_equiv,
      UScalar.ofNatCore_val_eq, UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, UScalar.val_and,
      gt_iff_lt] at *; agrind
  · intro j hj
    by_cases hc : j = i
    · rw [hc]
      have := Array.set_of_eq sum i5 i (by agrind)
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq, gt_iff_lt] at this ⊢
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        getElem!_pos, List.getElem!_eq_getElem?_getD, UScalarTy.U64_numBits_eq,
        Bvify.U64.UScalar_bv, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod,
        UScalar.ofNat_self_val, List.length_set, List.getElem_set_self, Array.set_val_eq,
        getElem?_pos, Option.getD_some]
      agrind
    · have := Array.set_of_ne sum i5 j i (by agrind) (by agrind) (by agrind)
      have := hsum j (by agrind)
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        getElem!_pos, List.getElem!_eq_getElem?_getD, UScalarTy.U64_numBits_eq,
        Bvify.U64.UScalar_bv, UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod,
        UScalar.ofNat_self_val, Array.set_val_eq, List.length_set, gt_iff_lt]; agrind
  · intro j hj _
    have hne : j ≠ i := by agrind
    have := Array.set_of_ne' sum i5 j i (by agrind) (by omega)
    have := hsum' j hj (by omega)
    simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      getElem!_pos, UScalar.lt_equiv, UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv,
      UScalar.val_and, Nat.and_two_pow_sub_one_eq_mod, Order.add_one_le_iff, ne_eq,
      Array.set_val_eq, List.length_set]; agrind
  · refine ⟨by agrind, ?_, ?_⟩
    · intro j hj
      have := sum'_post2 j (by omega)
      have := Array.set_of_ne sum i5 j i (by scalar_tac) (by scalar_tac) (by omega)
      simp_all
    · have : carry1.val = a[i]!.val + b[i]!.val + carry.val / 2 ^ 52 := by
        simp only [List.getElem!_eq_getElem?_getD, Array.getElem!_Usize_eq, Nat.add_left_cancel_iff,
          carry1_post, i3_post, i1_post, i2_post, i4_post1]; omega
      have : sum'[i]! = carry1.val % 2 ^ 52 := by
        have := sum'_post2 i.val (by omega)
        have := Array.set_of_eq sum i5 i (by scalar_tac)
        simp_all
      have : ∑ j ∈ Finset.Ico (i.val + 1) 5, 2 ^ (52 * j) * sum'[j]!.val =
          ∑ j ∈ Finset.Ico (i.val + 1) 5, 2 ^ (52 * j) * ((a)[j]!.val + (b)[j]!.val) +
          2 ^ (52 * (i.val + 1)) * (↑carry1 / 2 ^ 52) := by
        have : 4503599627370496 = 2 ^ 52 := by agrind
        simp_all
      have : 2 ^ (52 * i.val) * (carry1.val % 2 ^ 52) +
          2 ^ (52 * (i.val + 1)) * (carry1.val / 2 ^ 52) = 2 ^ (52 * i.val) * carry1.val := by
        have : carry1.val % 2 ^ 52 + 2 ^ 52 * (carry1.val / 2 ^ 52) = carry1.val := by agrind
        agrind
      calc ∑ j ∈ Finset.Ico (↑i) 5, 2 ^ (52 * j) * sum'[j]!
        _ = 2 ^ (52 * ↑i) * sum'[i]! +
            ∑ j ∈ Finset.Ico (↑i + 1) 5, 2 ^ (52 * j) * sum'[j]! := by
          have hi : i.val < 5 := by agrind
          simp [Finset.sum_eq_sum_Ico_succ_bot hi]
        _ = ∑ j ∈ Finset.Ico (↑i) 5, 2 ^ (52 * j) * (↑a[j]! + ↑b[j]!) +
            2 ^ (52 * ↑i) * (↑carry / 2 ^ 52) := by
          have hi : i.val < 5 := by agrind
          rw [Finset.sum_eq_sum_Ico_succ_bot hi]
          agrind
  · refine ⟨by agrind, by agrind, ?_⟩
    have : i.val = 5 := by scalar_tac
    simp only [this, le_refl, Finset.Ico_eq_empty_of_le, Array.getElem!_Nat_eq,
      List.getElem!_eq_getElem?_getD, Finset.sum_empty, Nat.reduceMul, zero_add, zero_eq_mul,
      Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, and_true, Nat.div_eq_zero_iff,
      false_or, gt_iff_lt]; agrind
  termination_by 5 - i.val
  decreasing_by scalar_decr_tac

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- Requires the input values to be bounded by  2 ^ 259
- The result represents the sum of the two input scalars modulo L
-/
@[step]
theorem add_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < L) (hb' : Scalar52_as_Nat b ≤ L) :
    add a b ⦃ (v : Scalar52) =>
      Scalar52_as_Nat v ≡ Scalar52_as_Nat a + Scalar52_as_Nat b [MOD L] ∧
      Scalar52_as_Nat v < L ∧ ∀ i < 5, v[i]!.val < 2 ^ 52 ⦄ := by
  unfold add
  step*
  · have : L < 2 ^ 259 := by unfold L; agrind
    agrind
  · have : L < 2 ^ 259 := by unfold L; agrind
    agrind
  · intro j _
    unfold ZERO
    interval_cases j <;> decide
  · unfold ZERO; decide
  · intro i hi
    unfold constants.L
    interval_cases i <;> decide
  · rw [constants.L_spec]
    have : Scalar52_as_Nat sum = Scalar52_as_Nat a + Scalar52_as_Nat b := calc
      ∑ i ∈ Finset.Ico 0 5, 2 ^ (52 * i) * sum[i]!.val
      _ = ∑ i ∈ Finset.Ico 0 5, 2 ^ (52 * i) * (a[i]!.val + b[i]!.val) := by assumption
      _ = ∑ i ∈ Finset.Ico 0 5, (2 ^ (52 * i) * a[i]!.val + 2 ^ (52 * i) * b[i]!.val) := by grind
      _ = _ := by simp [Scalar52_as_Nat, Finset.sum_add_distrib]
    omega
  · agrind [constants.L_spec]
  · refine ⟨?_, by assumption, by assumption⟩
    rw [constants.L_spec] at *
    have h1 : Scalar52_as_Nat v ≡ Scalar52_as_Nat sum [MOD L] := by
      have hL_mod : L ≡ 0 [MOD L] := by
        rw [Nat.ModEq, Nat.zero_mod, Nat.mod_self]
      have : Scalar52_as_Nat v + L ≡ Scalar52_as_Nat v + 0 [MOD L] :=
        Nat.ModEq.add_left _ hL_mod
      simp only [add_zero] at this
      exact this.symm.trans v_post1
    have h2 : Scalar52_as_Nat sum = Scalar52_as_Nat a + Scalar52_as_Nat b := by
      unfold Scalar52_as_Nat
      simp only [Finset.range_eq_Ico] at v_post3 ⊢
      conv_lhs => rw [sum_post3]
      simp [Finset.sum_add_distrib, Nat.mul_add]
    agrind

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
