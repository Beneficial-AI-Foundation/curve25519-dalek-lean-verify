/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.LFACTOR
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub

import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

/-! # Spec Theorem for `Scalar52::montgomery_reduce`

Specification and proof for `Scalar52::montgomery_reduce`.

This function performs Montgomery reduction.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64
open Polynomial
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/-
natural language description:

    • **Motivation**: The Montgomery form `M(x) := x * R`, where `R = 2^{260} = 2^{5*52}`,
      is used to optimize chains of modular arithmetic operations (like elliptic curve scalar
      multiplication). The isomorphism induced by `* R` changes the multiplication to:
      `MontMul(x,y) := M(x) * M(y) * R⁻¹`. Therefore, instead of computing standard reduction
      (`x % L`) which requires complex division logic, one needs to compute `x * R⁻¹ (mod L)`.
      Montgomery reduction refers to the algorithm that computes this `x * R⁻¹` using efficient
      bitwise shifts.

    • **Mechanism**: The algorithm avoids division by adding multiples of `L` to the input `x`
      until the result is exactly divisible by `R = 2^{260}` (i.e., the lower 260 bits are all zero).
      Since `R = 2^{260}` and limbs are 52 bits, we perform 5 "zeroing" steps (`part1`)
      followed by 4 "result assembly" steps (`part2`).

    • **Part 1: The Zeroing Strategy**
      We iteratively ensure the lowest remaining limb is 0 by adding a carefully chosen multiple of `L`.
      The helper `part1` calculates a "zeroing factor" `p` using the precomputed `LFACTOR`
      (where `LFACTOR * L ≡ -1 (mod 2⁵²)`).

      - **Limb 0 (First part1)**:
        * **Problem**: `limbs[0]` is non-zero. We cannot shift yet.
        * **Action**: Calculate `p` such that `limbs[0] + p * L ≡ 0 (mod 2⁵²)`.
        * **Result**: The sum's lowest 52 bits become 0.
        * **Shift**: We discard these zero bits (effectively dividing by 2⁵²). The carry flows to the next limb.

      *This repeats 5 times (using updated carries) until the entire lower 260 bits are zero.*

    • **Part 2: Result Reconstruction**
      After 5 reductions, the number is divisible by `R`. The helper `part2` extracts the quotient.
      It takes the high-order accumulated bits, slices off the lower 52 bits as a result limb (`w`),
      and passes the remaining upper bits (`carry`) to the next position. This reassembles
      the final 256-bit result (`r0` through `r4`).

natural language specs:

    • For any 9-limb array `a` of u128 values (representing a 512-bit integer):
      - The function returns a `Scalar52` `m` such that:
        `Scalar52_as_Nat(m) * R ≡ U128x9_as_Nat(a) (mod L)`
-/

-- Bridge lemma: converts the existing LFACTOR_spec (on Nat) to the form needed for Int arithmetic
private lemma LFACTOR_prop :
  (↑constants.LFACTOR.val * ↑constants.L[0]!.val : Int) % (2 ^ 52) = (2 ^ 52) - 1 := by

  have h_nat := constants.LFACTOR_spec
  obtain ⟨h_mod_zero, _, _⟩ := h_nat

  have h_cong : (constants.L[0]!.val : Int) % (2^52) = (_root_.L : Int) % (2^52) := by
    rw [← constants.L_spec]; unfold Scalar52_as_Nat
    rw [Finset.sum_range_succ']; zify at h_mod_zero ⊢; simp only [mul_zero, pow_zero, one_mul]
    rw [Int.add_emod]

    have h_tail_div : (∑ x ∈ Finset.range 4, (2:Int)^(52 * (x + 1)) *
      (constants.L[x.succ]!).val) % 2^52 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      use (∑ x ∈ Finset.range 4, (2:Int)^(52 * x) * (constants.L[x.succ]!).val)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      try ring

    rw [h_tail_div, zero_add, Int.emod_emod]

  rw [mul_comm, Int.mul_emod, h_cong, ← Int.mul_emod]
  rw [← Int.add_sub_cancel (_root_.L * ↑constants.LFACTOR.val : Int) 1, Int.sub_emod]; norm_cast;
  rw [h_mod_zero]; exact rfl

/-- The "Montgomery Step": Proves that adding the reduction factor clears the lower 52 bits. -/
private lemma mont_step (x : Int) (p : Int) (carry_out : Int)
    (hp : p = (x * ↑constants.LFACTOR.val) % (2 ^ 52))
    (hcarry : carry_out = (x + p * ↑constants.L[0]!.val) / (2 ^ 52)) :
    x + p * ↑constants.L[0]!.val = carry_out * (2 ^ 52) := by

  have h_div : x + p * ↑constants.L[0]!.val = carry_out * (2 ^ 52) + (x + p * ↑constants.L[0]!.val) % (2 ^ 52) := by
    rw [hcarry]
    rw [mul_comm ((x + p * ↑constants.L[0]!.val) / 2 ^ 52)]
    rw [Int.mul_ediv_add_emod]

  have h_mod_zero : (x + p * ↑constants.L[0]!.val) % (2 ^ 52) = 0 := by
    rw [hp, Int.add_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, mul_assoc, Int.mul_emod]
    rw [LFACTOR_prop]
    have h_neg : (2  ^ 52 - 1) % 2 ^ 52 = -1 % 2 ^ 52 := by ring;
    rw [← Int.zero_emod (2 ^52)]
    have h_cast : (2 : Int) ^ 52 = ((2 ^ 52 : Nat) : Int) := by norm_cast;
    rw [h_cast]
    apply (ZMod.intCast_eq_intCast_iff' _ _ (2^52)).mp
    simp only [Int.cast_add, ZMod.intCast_mod, Int.cast_mul, Int.cast_sub]
    simp only [Nat.reducePow, Nat.cast_ofNat, Int.cast_ofNat, Aeneas.ReduceZMod.reduceZMod,
      Int.cast_one, zero_sub, mul_neg, mul_one, add_neg_cancel, Int.cast_zero]

  rw [h_div, h_mod_zero, add_zero]



@[progress]
private theorem part1_spec (sum : U128)
  (h_bound : sum.val + (2 ^ 52 - 1) * (constants.L[0]!).val ≤ U128.max) :
  ∃ p carry,
  montgomery_reduce.part1 sum = ok (carry, p) ∧
  p.val = (sum.val * constants.LFACTOR) % (2 ^ 52) ∧
  carry.val = (sum.val + p.val * (constants.L[0]!).val) / (2 ^ 52) ∧
  carry.val < 2 ^ 77 ∧
  p.val < 2 ^ 52 := by
  unfold montgomery_reduce.part1
  unfold backend.serial.u64.scalar.IndexScalar52UsizeU64.index
  have h_L_len : constants.L.val.length = 5 := by
    unfold constants.L; rfl
  progress as ⟨ i, i_post ⟩
  progress as ⟨ i1, i1_post ⟩
  progress as ⟨ i2, i2_post ⟩
  progress as ⟨ i3, i3_post ⟩
  progress as ⟨ p, p_post ⟩

  have h_p_val : p.val = (sum.val * constants.LFACTOR) % (2 ^ 52) := by
      rw [p_post]; simp only [UScalar.val_and];
      have h_mask : i3.val = 2^52 - 1 := by
        simp only [i3_post, i2_post]; scalar_tac
      rw [h_mask]; rw [i1_post, i_post];

      rw [land_pow_two_sub_one_eq_mod]
      simp only [UScalar.cast, UScalar.val, core.num.U64.wrapping_mul]
      simp only [UScalarTy.U64_numBits_eq, UScalar.wrapping_mul_bv_eq, UScalar.bv_toNat,
        Aeneas.Bvify.U64.UScalar_bv]
      rw [BitVec.toNat_mul, BitVec.toNat_setWidth, UScalar.bv_toNat, Nat.mod_mul_mod]
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 2^52 ∣ 2^64)]
      rfl

  have h_p_bound : p.val < 2^52 := by
      rw [h_p_val]; apply Nat.mod_lt; norm_num

  have h_add_safe : sum.val + p.val * (constants.L[0]!).val ≤ U128.max := by
      apply Nat.le_trans (m := sum.val + (2^52 - 1) * (constants.L[0]!).val)
      · apply Nat.add_le_add_left; apply Nat.mul_le_mul_right; apply Nat.le_pred_of_lt h_p_bound
      · exact h_bound

  progress as ⟨i4, i4_post⟩
  progress as ⟨i5, i5_post⟩
  progress as ⟨i6, i6_post⟩
  progress as ⟨i7, i7_post_1, i7_post_2⟩
  refine ⟨h_p_val, ?_, ?_, h_p_bound⟩
  · -- Main Equation 2
    rw [i7_post_1, i6_post, i5_post, i4_post]; rw [Nat.shiftRight_eq_div_pow];
    simp only [List.Vector.length_val, UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem!_pos,
     Array.getElem!_Nat_eq]

  · rw [i7_post_1, i6_post, i5_post, i4_post]; simp only [Nat.shiftRight_eq_div_pow]; scalar_tac













@[progress]
private theorem part2_spec (sum : U128) :
  ∃ carry w,
  montgomery_reduce.part2 sum = ok (carry, w) ∧
  w.val = sum.val % (2 ^ 52) ∧
  carry.val = sum.val / (2 ^ 52) ∧
  carry.val < 2 ^ 76 ∧
  w.val < 2 ^ 52 := by -- 2^128 / 2^52 = 2^76

  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
