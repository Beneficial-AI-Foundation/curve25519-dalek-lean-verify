/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Scalar.Scalar.AsBytes
/-! # Spec Theorem for `MontgomeryPoint::mul`

Specification and proof for
`curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::scalar::Scalar), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::montgomery::MontgomeryPoint)}::mul`.

This function performs scalar multiplication of a Montgomery point using the Montgomery ladder
algorithm. It implements constant-time scalar multiplication by processing scalar bits from
most significant to least significant.

**Source**: curve25519-dalek/src/montgomery.rs, lines 413:4-450:5

## TODO
- Complete proof
--/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery

namespace curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

/-
Natural language description:

    - Interprets the MontgomeryPoint's 32-byte encoding as a field element u using
      `FieldElement51.from_bytes`.

    - Initializes two projective points:
      - x0 = (1 : 0) representing the identity (point at infinity)
      - x1 = (u : 1) representing the input point in projective coordinates

    - Processes scalar bits from most significant (bit 254) to least significant (bit 0)
      using the Montgomery ladder (Algorithm 8 from Costello-Smith 2017):
      - By scalar invariant #1, the MSB (bit 255) is always 0, so we start from bit 254
      - For each bit, conditionally swaps x0 and x1 based on bit transitions
      - Applies differential add-and-double operation
      - Maintains constant-time execution through conditional operations

    - After processing all bits, performs a final conditional swap based on the LSB

    - Converts the projective result x0 back to affine coordinates using `ProjectivePoint.as_affine`

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns a 32-byte MontgomeryPoint encoding the scalar multiplication result
    - The computation is constant-time with respect to the scalar value
    - The result represents the u-coordinate of [scalar]P on the Montgomery curve
-/


@[progress]
theorem mul_loop_spec
    (affine_u : backend.serial.u64.field.FieldElement51)
    (x0 x1 : montgomery.ProjectivePoint)
    (scalar_bytes : Array U8 32#usize)
    (prev_bit : Bool)
    (i : Isize)
    (idx0W : x0.W = backend.serial.u64.field.FieldElement51.ZERO)
    (idx1W : x1.W = backend.serial.u64.field.FieldElement51.ONE)
    (idx0U : x0.U = backend.serial.u64.field.FieldElement51.ONE)
    :
    mul_loop affine_u x0 x1 scalar_bytes prev_bit i ⦃ res =>
    (res.2.2 =true →
      let q := (i.val / 8).toNat
      let r := (i.val % 8).toNat
      let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
        +  2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
        + 2^(8 * q+r) * prev_bit.toNat
      let u := x1.U.toField
      let u_out := res.2.1.U.toField
      let w_out := res.2.1.W.toField
      let u_ord := u_out/w_out
      w_out ≠ 0 ∧
      MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ∧
    (res.2.2 = false →
      let q := (i.val / 8).toNat
      let r := (i.val % 8).toNat
      let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
      + 2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
      + 2^(8 * q+r) * prev_bit.toNat
      let u := x1.U.toField
      let u_out := res.1.U.toField
      let w_out := res.1.W.toField
      let u_ord := u_out/w_out
      w_out ≠ 0 ∧
      MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ⦄
    := by
    induction h: i.val using Int.induction_on generalizing i x0 x1 prev_bit with
    | zero =>
        unfold mul_loop
        have : i=0#isize := by scalar_tac
        simp[this]
        have : ((scalar_bytes)[0]!).val % 1 =0 := by grind
        simp at this
        sorry
    | succ i _ =>
        unfold mul_loop
        sorry
    | pred i _ =>
        unfold mul_loop
        sorry


/-- **Spec and proof concerning `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements the Montgomery ladder for constant-time scalar multiplication
- Processes scalar bits from bit 254 down to bit 0 using Algorithm 8 (Costello-Smith 2017)
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]P
  * If P has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]P), the u-coordinate of the n-fold sum of P on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by P throughout the computation
  * When the scalar is reduced modulo the group order L, the result corresponds to
    scalar multiplication in the prime-order subgroup
  * The result is computed via projective arithmetic and converted back to affine form
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
  * The computation maintains constant-time guarantees: the sequence of operations
    executed is independent of the scalar bit values (only conditional swaps and
    unconditional arithmetic operations are performed)
-/

@[progress]
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (h_valid : self.W.toField ≠ 0) :
    montgomery.ProjectivePoint.as_affine self ⦃ res =>
    ((U8x32_as_Nat res % 2^ 255) :ℕ ) = self.U.toField  / self.W.toField ⦄ := by
    sorry

lemma aux_eq_mul (scalar : scalar.Scalar) : U8x32_as_Nat scalar.bytes =
(∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) * ((scalar.bytes[((254 :ℤ )/ 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) ))
        + 2^ 255 * ((scalar.bytes[31]!).val/ 2^7)
        := by
        simp only [U8x32_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
    Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
    Nat.reduceLT, add_assoc, Nat.lt_add_one, Int.reduceDiv, Int.reduceToNat, getElem!_pos, Int.reduceMod,
    Nat.add_left_cancel_iff]
        have :=Nat.mod_add_div ((scalar.bytes)[31]!).val 128
        simp only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.lt_add_one, getElem!_pos] at this
        conv_lhs =>
          rw [← this, mul_add, ← mul_assoc]
        simp

lemma aux_lt_mul (i : ℕ) (scalar : scalar.Scalar) :
∑ x ∈ Finset.range i, 2 ^ (8 * x) * (scalar.bytes[x]!).val <  2^ (8*i)
        := by
    induction i
    · simp
    · rename_i n hn
      rw[Finset.sum_range_succ]
      have : (scalar.bytes[n]!).val ≤  2 ^8-1 := by scalar_tac
      have :=mul_le_mul_right this  (2 ^ (8 * n))
      have := add_lt_add_of_lt_of_le hn this
      apply lt_of_lt_of_le this
      ring_nf
      simp

lemma aux_lt254_mul (scalar : scalar.Scalar) :
∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) * ((scalar.bytes[((254 :ℤ ) / 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) )
        <  2^ 255
        := by
  have eq1 := aux_lt_mul 31  scalar
  have := Nat.mod_lt (((scalar.bytes)[31]!).val) (by grind : 0< 64)
  have :(((scalar.bytes)[31]!).val) % 128 ≤  127 := by grind
  have := Nat.mul_le_mul_left (2 ^ 248) this
  have := add_lt_add_of_lt_of_le eq1 this
  simp only [Int.reduceDiv, Int.reduceToNat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reduceMul,
    Nat.reducePow, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.lt_add_one, getElem!_pos, Int.reduceMod, gt_iff_lt]
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow, List.Vector.length_val,
    UScalar.ofNat_val_eq, Nat.lt_add_one, getElem!_pos, Nat.reduceMul, Nat.reduceAdd] at this
  apply this


lemma aux_eq_mod_mul (scalar : scalar.Scalar) : (U8x32_as_Nat scalar.bytes) % 2^ 255 =
(∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) * ((scalar.bytes[((254 :ℤ ) / 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) ))
        := by
       rw[aux_eq_mul,  Nat.add_mul_mod_self_left]
       apply Nat.mod_eq_of_lt
       apply aux_lt254_mul


/- **Spec and proof concerning `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements the Montgomery ladder for constant-time scalar multiplication
- Processes scalar bits from bit 254 down to bit 0 using Algorithm 8 (Costello-Smith 2017)
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]P
  * If P has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]P), the u-coordinate of the n-fold sum of P on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by P throughout the computation
  * When the scalar is reduced modulo the group order L, the result corresponds to
    scalar multiplication in the prime-order subgroup
  * The result is computed via projective arithmetic and converted back to affine form
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
  * The computation maintains constant-time guarantees: the sequence of operations
    executed is independent of the scalar bit values (only conditional swaps and
    unconditional arithmetic operations are performed)
-/

set_option maxHeartbeats 10000000 in
-- heavy simp
@[progress]
theorem mul_spec (P : montgomery.MontgomeryPoint) (scalar : scalar.Scalar) :
    mul P scalar ⦃ res =>
    let m:= (U8x32_as_Nat scalar.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
     := by
    unfold mul  IdentityMontgomeryProjectivePoint.identity subtle.Choice.Insts.CoreConvertFromU8.from
    progress as ⟨x , hmod_x, h_valid⟩
    progress as ⟨ s, hs, hsb⟩
    progress as ⟨ c, ct, cf⟩
    progress as ⟨ y, hy⟩
    set m:= (U8x32_as_Nat scalar.bytes) % 2^254 with hm
    by_cases h: c.2.2 = true
    · simp_all only [Nat.reducePow, forall_const, Bool.true_eq_false, IsEmpty.forall_iff, Bool.toNat_true, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq,
    one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, zero_lt_one, or_true, or_self,
    UScalar.val_not_eq_imp_not_eq, ↓reduceDIte]
      by_cases hi: y= 1#u8
      · simp only [hi, ↓reduceDIte, bind_tc_ok]
        unfold montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap  zeroize.Zeroize.Blanket.zeroize
        simp only [↓reduceIte, core.default.DefaultBool.default, bind_tc_ok]
        progress*
        unfold MontgomeryPoint.mkPoint
        rw[ res_post, ct.right]
        have := aux_eq_mod_mul scalar
        rw[← this]
        have : false.toNat =0 := by decide
        rw[this]
        ring_nf
        unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
        have := Edwards.lift_mod_eq (Field51_as_Nat x) ((U8x32_as_Nat P) % 2 ^ 255)
        rw[← Nat.ModEq] at this
        have := this hmod_x
        rw[this]
        ring_nf
      · simp only [hi, ↓reduceDIte, bind_tc_fail, spec_fail]
        apply hi
        scalar_tac
    · have : c.2.2 = false := by grind
      simp_all only [Nat.reducePow, Bool.false_eq_true, ne_eq, Int.reduceDiv, Int.reduceToNat, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Nat.reduceMul, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.lt_add_one,
    getElem!_pos, Int.reduceMod, Nat.reduceAdd, Bool.toNat_false, mul_zero, add_zero, IsEmpty.forall_iff, forall_const,
    not_false_eq_true, Nat.not_eq, zero_ne_one, one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
    UScalar.val_not_eq_imp_not_eq, ↓reduceDIte]
      have :  y = 0#u8 := by scalar_tac
      simp only [this, ↓reduceDIte, bind_tc_ok]
      unfold montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap  zeroize.Zeroize.Blanket.zeroize
      simp only [Nat.not_eq, UScalar.ofNat_val_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one,
      not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq, ↓reduceIte, core.default.DefaultBool.default,
      bind_tc_ok]
      progress*
      unfold MontgomeryPoint.mkPoint
      rw[ res_post, cf.right]
      have := aux_eq_mod_mul scalar
      simp only [Nat.reducePow, Int.reduceDiv, Int.reduceToNat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      Nat.reduceMul, List.Vector.length_val, UScalar.ofNat_val_eq, Nat.lt_add_one, getElem!_pos, Int.reduceMod, Nat.reduceAdd, Nat.reducePow] at this
      rw[← this]
      ring_nf
      unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
      have := Edwards.lift_mod_eq (Field51_as_Nat x) ((U8x32_as_Nat P) % 2 ^ 255)
      rw[← Nat.ModEq] at this
      have := this hmod_x
      rw[this]
      ring_nf


end curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

namespace curve25519_dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

/- [curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::montgomery::MontgomeryPoint), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::scalar::Scalar)}::mul]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 462:4-464:5
-/

/-
Natural language description:

    - This is the commutative variant of scalar multiplication: Scalar * MontgomeryPoint.

    - Simply delegates to the MontgomeryPoint * Scalar implementation by swapping arguments.

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns the same result as the reverse multiplication (point * scalar)
    - Inherits all mathematical properties from MontgomeryPoint::mul
-/
/-- **Spec and proof concerning `montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the reverse operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MontgomeryPoint::mul with swapped arguments
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/
@[progress]
theorem mul_spec (scalar : scalar.Scalar) (P : montgomery.MontgomeryPoint) :
    mul scalar P ⦃ res =>
    let m:= (U8x32_as_Nat scalar.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
    := by
  unfold mul
  progress*

end curve25519_dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint

/- [curve25519_dalek::montgomery::{core::ops::arith::Mul<&'b (curve25519_dalek::scalar::Scalar), curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::mul]:
   Source: 'curve25519-dalek/src/macros.rs', lines 93:12-95:13
-/

/-
Natural language description:

    - This is another variant of scalar multiplication: MontgomeryPoint * &'b Scalar.

    - Delegates to the core MontgomeryPoint * Scalar implementation.

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns the same result as the underlying scalar multiplication
    - Inherits all mathematical properties from MontgomeryPoint::mul
-/
/-- **Spec and proof concerning `montgomery.MulMontgomeryPointSharedBScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the underlying operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by point throughout the computation
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/
@[progress]
theorem mul_spec (P : MontgomeryPoint) (rhs : scalar.Scalar) :
    mul P rhs ⦃ res =>
    let m:= (U8x32_as_Nat rhs.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
 := by
  unfold mul
  progress*

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

/-
Natural language description:

    - This is the non-borrow variant of scalar multiplication: Scalar * MontgomeryPoint.

    - Delegates to the shared reference implementation
      MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul.

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns the same result as the underlying scalar multiplication
    - Inherits all mathematical properties from the core Montgomery ladder implementation
-/
/-- **Spec and proof concerning `montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the underlying operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by point throughout the computation
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/
@[progress]
theorem mul_spec (scalar : Scalar) (P : montgomery.MontgomeryPoint) :
    mul scalar P ⦃ res =>
    let m:= (U8x32_as_Nat scalar.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
 := by
  unfold mul
  progress*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint
