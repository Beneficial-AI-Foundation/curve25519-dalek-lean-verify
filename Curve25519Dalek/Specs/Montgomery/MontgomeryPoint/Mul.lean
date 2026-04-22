/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Scalar.Scalar.AsBytes
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.AsAffine
import Curve25519Dalek.Specs.Montgomery.ProjectivePoint.DifferentialAddAndDouble

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul`

The core algorithm is the Montgomery ladder (Algorithm 8 from Costello-Smith 2017), which
performs constant-time scalar multiplication by processing scalar bits from bit 254 down to
bit 0:

- Interprets the `MontgomeryPoint`'s 32-byte encoding as a field element `u` via
  `FieldElement51::from_bytes`.
- Initializes two projective points: `x0 = (1 : 0)` (identity / point at infinity) and
  `x1 = (u : 1)` (the input point in projective coordinates).
- Processes scalar bits from most significant (bit 254) to least significant (bit 0): for each
  bit, conditionally swaps `x0` and `x1` based on bit transitions and applies differential
  add-and-double. By scalar invariant #1 the MSB (bit 255) is always 0, so iteration starts
  from bit 254. Constant-time execution is maintained via conditional operations.
- After processing all bits, performs a final conditional swap based on the LSB.
- Converts the projective result `x0` to affine coordinates via `ProjectivePoint::as_affine`.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::mul_loop`**
• The loop always terminates without panic given valid inputs satisfying the invariants
• When result flag is `true`: x1 encodes `m • P` with valid field elements and nonzero denominator
• When result flag is `false`: x0 encodes `m • P` with valid field elements and nonzero denominator
• In both branches, validity of both output projective point coordinates is preserved
-/
@[step, externally_verified]
theorem mul_loop_spec
    (affine_u : backend.serial.u64.field.FieldElement51)
    (x0 x1 : montgomery.ProjectivePoint)
    (scalar_bytes : Array U8 32#usize)
    (prev_bit : Bool)
    (i : Isize)
    (idx0W : Field51_as_Nat x0.W = 0)
    (idx1W : Field51_as_Nat x1.W = 1)
    (idx0U : Field51_as_Nat x0.U = 1) :
    mul_loop affine_u x0 x1 scalar_bytes prev_bit i
    ⦃ (result : montgomery.ProjectivePoint × montgomery.ProjectivePoint × Bool) =>
      (result.2.2 = true →
        let q := (i.val / 8).toNat
        let r := (i.val % 8).toNat
        let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
          + 2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
          + 2^(8 * q + r) * prev_bit.toNat
        let u := x1.U.toField
        let u_out := result.2.1.U.toField
        let w_out := result.2.1.W.toField
        let u_ord := u_out/w_out
        result.2.1.U.IsValid ∧
        result.2.1.W.IsValid ∧
        result.1.U.IsValid ∧
        result.1.W.IsValid ∧
        w_out ≠ 0 ∧
        MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ∧
      (result.2.2 = false →
        let q := (i.val / 8).toNat
        let r := (i.val % 8).toNat
        let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
        + 2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
        + 2^(8 * q + r) * prev_bit.toNat
        let u := x1.U.toField
        let u_out := result.1.U.toField
        let w_out := result.1.W.toField
        let u_ord := u_out/w_out
        result.2.1.U.IsValid ∧
        result.2.1.W.IsValid ∧
        result.1.U.IsValid ∧
        result.1.W.IsValid ∧
        w_out ≠ 0 ∧
        MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ⦄ := by
  induction h: i.val using Int.induction_on generalizing i x0 x1 prev_bit with
  | zero =>
      sorry
  | succ n _ =>
      sorry
  | pred n _ =>
      sorry

lemma aux_eq_mul (scalar : scalar.Scalar) : U8x32_as_Nat scalar.bytes =
    (∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) *
          ((scalar.bytes[((254 :ℤ )/ 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) ))
        + 2^ 255 * ((scalar.bytes[31]!).val/ 2^7) := by
  simp only [U8x32_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
    List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
    Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
    Nat.reduceLT, add_assoc, Nat.lt_add_one, Int.reduceDiv, Int.reduceToNat, getElem!_pos,
    Int.reduceMod, Nat.add_left_cancel_iff]
  have := Nat.mod_add_div ((scalar.bytes)[31]!).val 128
  simp only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
    Nat.lt_add_one, getElem!_pos] at this
  conv_lhs =>
    rw [← this, mul_add, ← mul_assoc]
  simp

lemma aux_lt_mul (i : ℕ) (scalar : scalar.Scalar) :
    ∑ x ∈ Finset.range i, 2 ^ (8 * x) * (scalar.bytes[x]!).val < 2^ (8*i) := by
  induction i
  · simp
  · rename_i n hn
    rw[Finset.sum_range_succ]
    have : (scalar.bytes[n]!).val ≤  2 ^8-1 := by scalar_tac
    have := mul_le_mul_right this (2 ^ (8 * n))
    have := add_lt_add_of_lt_of_le hn this
    apply lt_of_lt_of_le this
    ring_nf
    simp

lemma aux_lt254_mul (scalar : scalar.Scalar) :
    ∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) *
          ((scalar.bytes[((254 :ℤ ) / 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) )
        < 2^ 255 := by
  have eq1 := aux_lt_mul 31 scalar
  have := Nat.mod_lt (((scalar.bytes)[31]!).val) (by grind : 0< 64)
  have :(((scalar.bytes)[31]!).val) % 128 ≤  127 := by grind
  have := Nat.mul_le_mul_left (2 ^ 248) this
  have := add_lt_add_of_lt_of_le eq1 this
  simp only [Int.reduceDiv, Int.reduceToNat, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reduceMul, Nat.reducePow, List.Vector.length_val,
    UScalar.ofNatCore_val_eq, Nat.lt_add_one, getElem!_pos, Int.reduceMod, gt_iff_lt]
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow,
    List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.lt_add_one, getElem!_pos,
    Nat.reduceMul, Nat.reduceAdd] at this
  apply this

lemma aux_eq_mod_mul (scalar : scalar.Scalar) : (U8x32_as_Nat scalar.bytes) % 2^ 255 =
    (∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) *
          ((scalar.bytes[((254 :ℤ ) / 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) )) := by
  rw[aux_eq_mul,  Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  apply aux_lt254_mul

/-! ## Sub-lemmas for `mul_spec`

The following lemmas factor out the common proof patterns shared between the two
main branches (bit = true / bit = false) of the Montgomery ladder's final step.
-/

/-- **MontgomeryPoint result assembly**: Given:
    - The `from_bytes` modular congruence (`hmod_x`)
    - The `as_affine` result (`res_field`) and bound (`res_bound`)
    - The Montgomery ladder loop invariant with simplified scalar (`loop_inv`)
    derives `MontgomeryPoint.mkPoint res = m • MontgomeryPoint.mkPoint P`.

    This lemma captures the common end-game of both branches: converting the
    `U8x32_as_Field` representation to a natural-number cast modulo `2^255`,
    unfolding `MontgomeryPoint.mkPoint`, and applying the field lifting to
    relate `x.toField` to the input point's u-coordinate. -/
lemma mul_spec_mkPoint_from_affine
    (res : Array U8 32#usize)
    (P : montgomery.MontgomeryPoint)
    (scalar : scalar.Scalar)
    (x : backend.serial.u64.field.FieldElement51)
    (u_div_w : CurveField)
    (hmod_x : Field51_as_Nat x ≡ (U8x32_as_Nat P) % 2 ^ 255 [MOD p])
    (res_bound : U8x32_as_Nat res < 2 ^ 255)
    (res_field : U8x32_as_Field res = u_div_w)
    (hP_bound : U8x32_as_Nat P < 2 ^ 255)
    (loop_inv : MontgomeryPoint.u_affine_toPoint u_div_w =
        ((U8x32_as_Nat scalar.bytes) % 2 ^ 255) • MontgomeryPoint.u_affine_toPoint x.toField) :
    MontgomeryPoint.mkPoint res =
        ((U8x32_as_Nat scalar.bytes) % 2 ^ 255) • MontgomeryPoint.mkPoint P := by
  have eq1 := Nat.mod_eq_of_lt res_bound
  have := U8x32_as_Field_eq_cast res
  have eqP:= U8x32_as_Field_eq_cast P
  rw [this, ← eq1, ] at res_field
  have eq2 := U8x32_as_Field_eq_cast P
  unfold MontgomeryPoint.mkPoint
  have hxP : x.toField = U8x32_as_Field P := by
    rw [eq2]
    refine Edwards.lift_mod_eq _ _ ?_
    have hmodeq := hmod_x
    rw [Nat.mod_eq_of_lt hP_bound] at hmodeq
    exact hmodeq
  rw [this, ← eq1, res_field, loop_inv, hxP]

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul`**
• The function always succeeds (no panic) for any valid Montgomery point and scalar input
• The result encodes the u-coordinate of the scalar multiple `[m]P` on the Montgomery curve:
  `MontgomeryPoint.mkPoint result = m • MontgomeryPoint.mkPoint P`
  where `m = (U8x32_as_Nat scalar.bytes) % 2^255`
-/
@[step, externally_verified]
theorem mul_spec (P : montgomery.MontgomeryPoint) (scalar : scalar.Scalar)
    (hP_bound : U8x32_as_Nat P < 2 ^ 255) :
    mul P scalar ⦃ (result : montgomery.MontgomeryPoint) =>
      let m := (U8x32_as_Nat scalar.bytes) % 2^255
      MontgomeryPoint.mkPoint result = m • (MontgomeryPoint.mkPoint P) ⦄ := by
  unfold mul IdentityMontgomeryProjectivePoint.identity subtle.Choice.Insts.CoreConvertFromU8.from
  step as ⟨x , hmod_x, h_valid⟩
  step as ⟨ one, one_eq, one_bound⟩
  step as ⟨ zero, zero_eq, zero_bound⟩
  step as ⟨ one1, one1_eq, one_bound⟩
  step as ⟨ s, hs, hsb⟩
  step as ⟨ c, ct, cf⟩
  step as ⟨ y, hy⟩
  by_cases h: c.2.2 = true
  · simp_all only [Nat.reducePow, forall_const, Bool.true_eq_false, IsEmpty.forall_iff,
        Bool.toNat_true, Nat.not_eq, UScalar.ofNatCore_val_eq, ne_eq,
        one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, zero_lt_one, or_true, or_self,
        UScalar.val_not_eq_imp_not_eq, ↓reduceDIte]
    by_cases hi: y= 1#u8
    · simp only [hi, ↓reduceDIte, bind_tc_ok]
      unfold montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap
        zeroize.Zeroize.Blanket.zeroize
      simp only [↓reduceIte, core.default.DefaultBool.default, bind_tc_ok]
      step*
        -- Use `mul_spec_mkPoint_from_affine` to assemble the final result.
        -- We first construct the loop invariant with the simplified scalar.
      refine mul_spec_mkPoint_from_affine result P scalar x _
          hmod_x result_post2 result_post1 hP_bound ?_
      rw [ct.right.right.right.right.right]
      have := aux_eq_mod_mul scalar
      rw [← this]
      have : false.toNat = 0 := by decide
      rw [this]
      ring_nf
    · simp only [hi, ↓reduceDIte, bind_tc_fail, spec_fail]
      apply hi
      scalar_tac
  · have : c.2.2 = false := by grind
    simp_all only [Nat.reducePow, Bool.false_eq_true, ne_eq, Int.reduceDiv, Int.reduceToNat,
        Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reduceMul,
        List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.lt_add_one,
        getElem!_pos, Int.reduceMod, Nat.reduceAdd, Bool.toNat_false, mul_zero, add_zero,
        IsEmpty.forall_iff, forall_const, not_false_eq_true, Nat.not_eq, zero_ne_one,
        one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
        UScalar.val_not_eq_imp_not_eq, ↓reduceDIte]
    have :  y = 0#u8 := by scalar_tac
    simp only [this, ↓reduceDIte, bind_tc_ok]
    unfold montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap
      zeroize.Zeroize.Blanket.zeroize
    simp only [Nat.not_eq, UScalar.ofNatCore_val_eq, ne_eq, zero_ne_one, not_false_eq_true,
        one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
        UScalar.val_not_eq_imp_not_eq, ↓reduceIte, core.default.DefaultBool.default,
        bind_tc_ok]
    step*
      -- Use `mul_spec_mkPoint_from_affine` to assemble the final result.
      -- We first construct the loop invariant with the simplified scalar.
    refine mul_spec_mkPoint_from_affine result P scalar x _
        hmod_x result_post2 result_post1 hP_bound ?_
    rw [cf.right.right.right.right.right]
    have := aux_eq_mod_mul scalar
    simp only [Nat.reducePow, Int.reduceDiv, Int.reduceToNat, Array.getElem!_Nat_eq,
        List.getElem!_eq_getElem?_getD, Nat.reduceMul, List.Vector.length_val,
        UScalar.ofNatCore_val_eq, Nat.lt_add_one, getElem!_pos, Int.reduceMod,
        Nat.reduceAdd, Nat.reducePow] at this
    rw [← this]
    ring_nf

end curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

namespace curve25519_dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::{Mul<&MontgomeryPoint> for &Scalar}::mul`**
• The function always succeeds (no panic) for any valid Montgomery point and scalar input
• The result satisfies `MontgomeryPoint.mkPoint result = m • MontgomeryPoint.mkPoint P`,
  where `m = (U8x32_as_Nat scalar.bytes) % 2^255`
-/
@[step]
theorem mul_spec (scalar : scalar.Scalar) (P : montgomery.MontgomeryPoint)
    (hP_bound : U8x32_as_Nat P < 2 ^ 255) :
    mul scalar P ⦃ (result : montgomery.MontgomeryPoint) =>
      let m := (U8x32_as_Nat scalar.bytes) % 2^255
      MontgomeryPoint.mkPoint result = m • (MontgomeryPoint.mkPoint P) ⦄ := by
  unfold mul
  step*

end curve25519_dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts
namespace CoreOpsArithMulSharedBScalarMontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::{Mul<&Scalar> for MontgomeryPoint}::mul`**
• The function always succeeds (no panic) for any valid Montgomery point and scalar input
• The result satisfies `MontgomeryPoint.mkPoint result = m • MontgomeryPoint.mkPoint P`,
  where `m = (U8x32_as_Nat rhs.bytes) % 2^255`
-/
@[step]
theorem mul_spec (P : MontgomeryPoint) (rhs : scalar.Scalar)
    (hP_bound : U8x32_as_Nat P < 2 ^ 255) :
    mul P rhs ⦃ (result : MontgomeryPoint) =>
      let m := (U8x32_as_Nat rhs.bytes) % 2^255
      MontgomeryPoint.mkPoint result = m • (MontgomeryPoint.mkPoint P) ⦄ := by
  unfold mul
  step*

end CoreOpsArithMulSharedBScalarMontgomeryPoint
end curve25519_dalek.montgomery.MontgomeryPoint.Insts

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::{Mul<MontgomeryPoint> for Scalar}::mul`**
• The function always succeeds (no panic) for any valid Montgomery point and scalar input
• The result satisfies `MontgomeryPoint.mkPoint result = m • MontgomeryPoint.mkPoint P`,
  where `m = (U8x32_as_Nat scalar.bytes) % 2^255`
-/
@[step]
theorem mul_spec (scalar : Scalar) (P : montgomery.MontgomeryPoint)
    (hP_bound : U8x32_as_Nat P < 2 ^ 255) :
    mul scalar P ⦃ (result : montgomery.MontgomeryPoint) =>
      let m := (U8x32_as_Nat scalar.bytes) % 2^255
      MontgomeryPoint.mkPoint result = m • (MontgomeryPoint.mkPoint P) ⦄ := by
  unfold mul
  step*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint
