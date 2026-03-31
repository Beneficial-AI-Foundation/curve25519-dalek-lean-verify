/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-! # Spec Theorem for `FieldElement51::mul`

This function computes the product of two field elements.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## Proof strategy: Fold theorem decomposition

The function body is decomposed into 3 helper functions,
each with a fold theorem and `@[step]` spec.

### Stage 1 — Product computation (`mul_product_stage`)
### Stage 2 — Carry propagation (`mul_carry_prop_stage`)
### Stage 3 — Final reduction (`mul_final_reduce_stage`)
-/

set_option linter.hashCommand false
#setup_aeneas_simps

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
open MulShared0FieldElement51SharedAFieldElement51FieldElement51 (mul.m mul.LOW_51_BIT_MASK)

namespace curve25519_dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithMulSharedAFieldElement51FieldElement51

@[step]
theorem m_spec (x y : U64) :
    mul.m x y ⦃ (r : U128) =>
      r.val = x.val * y.val ⦄ := by
  unfold mul.m
  step*

@[step]
theorem LOW_51_BIT_MASK_spec :
    mul.LOW_51_BIT_MASK ⦃ (result : U64) => result.val = 2^51 - 1 ⦄ := by
  unfold mul.LOW_51_BIT_MASK
  step*

lemma decompose (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ) :
  (a0 +
  2 ^ 51 * a1 +
  2^ (2 * 51) * a2 +
  2^ (3 * 51) * a3 +
  2^ (4 * 51) * a4) * (b0 +
  2 ^ 51 * b1 +
  2^ (2 * 51) * b2 +
  2^ (3 * 51) * b3 +
  2^ (4 * 51) * b4)
  ≡ a0 * b0 +  a4 * (b1 * 19 )+  a3 * (b2 * 19) + a2 * (b3 * 19) + a1 * (b4 * 19) +
    2 ^ 51 * ( a1 * b0 + a0 * b1 + a4 * (b2 * 19 )+
    a3 * (b3 * 19) + a2 * (b4 * 19) ) +
    2 ^ (2 * 51) * (
      a2 * b0 + a1 * b1 + a0 * b2 +
      a4 * (b3 * 19) + a3 * (b4 * 19)
      ) +
    2 ^ (3 * 51) * (
      a3 * b0 + a2 * b1 + a1 * b2 +  a0 * b3 +
      a4 * (b4 * 19)
    ) +
    2 ^ (4 * 51) * (
      a4 * b0 + a3 * b1 + a2 * b2 +  a1 * b3 + a0 * b4
    )
   [MOD p] := by
  have : (a0 +
  2 ^ 51 * a1 +
  2^ (2 * 51) * a2 +
  2^ (3 * 51) * a3 +
  2^ (4 * 51) * a4) * (b0 +
  2 ^ 51 * b1 +
  2^ (2 * 51) * b2 +
  2^ (3 * 51) * b3 +
  2^ (4 * 51) * b4) =
  (a0 * b0 +
  2 ^ 51 * (a1 * b0 + a0 * b1) +
  2^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2) +
  2^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) +
  2^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4)) +
  2^ (255) * ( (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4) +
  2 ^ 51 * (a4 *  b2 + a3 * b3 + a2 * b4)  +
  2^ (2 * 51) * ( a4 * b3 + a3 * b4) +
  2^ (3 * 51) * (a4 * b4)) := by ring
  rw[this]
  have key  : (2:ℕ)^255 ≡ 19 [MOD p] := by
          unfold p
          rw [Nat.ModEq]
          norm_num
  have := Nat.ModEq.mul_right ( (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4) +
  2 ^ 51 * (a4 *  b2 + a3 * b3 + a2 * b4)  +
  2^ (2 * 51) * ( a4 * b3 + a3 * b4) +
  2^ (3 * 51) * (a4 * b4)) key
  have := Nat.ModEq.add_left  (a0 * b0 +
  2 ^ 51 * (a1 * b0 + a0 * b1) +
  2^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2) +
  2^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) +
  2^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4))  this
  apply Nat.ModEq.trans this
  have : a0 * b0 + 2 ^ 51 * (a1 * b0 + a0 * b1) + 2 ^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2) +
        2 ^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) +
      2 ^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4) +
    19 *
      (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4 + 2 ^ 51 * (a4 * b2 + a3 * b3 + a2 * b4) +
          2 ^ (2 * 51) * (a4 * b3 + a3 * b4) +
        2 ^ (3 * 51) * (a4 * b4)) =
        a0 * b0 + a4 * (b1 * 19) + a3 * (b2 * 19) + a2 * (b3 * 19) + a1 * (b4 * 19) +
          2 ^ 51 * (a1 * b0 + a0 * b1 + a4 * (b2 * 19) + a3 * (b3 * 19) + a2 * (b4 * 19)) +
        2 ^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2 + a4 * (b3 * 19) + a3 * (b4 * 19)) +
      2 ^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 + a4 * (b4 * 19)) +
    2 ^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4) := by ring
  rw[this]

/-! ## Helper Functions -/

/-- Stage 1: Compute the 5 intermediate products for field multiplication in radix-2^51. -/
def mul_product_stage (self _rhs : Array U64 5#usize) :
    Result (U128 × U128 × U128 × U128 × U128) := do
  let i ← Array.index_usize _rhs 1#usize
  let b1_19 ← i * 19#u64
  let i1 ← Array.index_usize _rhs 2#usize
  let b2_19 ← i1 * 19#u64
  let i2 ← Array.index_usize _rhs 3#usize
  let b3_19 ← i2 * 19#u64
  let i3 ← Array.index_usize _rhs 4#usize
  let b4_19 ← i3 * 19#u64
  let i4 ← Array.index_usize self 0#usize
  let i5 ← Array.index_usize _rhs 0#usize
  let i6 ← mul.m i4 i5
  let i7 ← Array.index_usize self 4#usize
  let i8 ← mul.m i7 b1_19
  let i9 ← i6 + i8
  let i10 ← Array.index_usize self 3#usize
  let i11 ← mul.m i10 b2_19
  let i12 ← i9 + i11
  let i13 ← Array.index_usize self 2#usize
  let i14 ← mul.m i13 b3_19
  let i15 ← i12 + i14
  let i16 ← Array.index_usize self 1#usize
  let i17 ← mul.m i16 b4_19
  let c0 ← i15 + i17
  let i18 ← mul.m i16 i5
  let i19 ← mul.m i4 i
  let i20 ← i18 + i19
  let i21 ← mul.m i7 b2_19
  let i22 ← i20 + i21
  let i23 ← mul.m i10 b3_19
  let i24 ← i22 + i23
  let i25 ← mul.m i13 b4_19
  let c1 ← i24 + i25
  let i26 ← mul.m i13 i5
  let i27 ← mul.m i16 i
  let i28 ← i26 + i27
  let i29 ← mul.m i4 i1
  let i30 ← i28 + i29
  let i31 ← mul.m i7 b3_19
  let i32 ← i30 + i31
  let i33 ← mul.m i10 b4_19
  let c2 ← i32 + i33
  let i34 ← mul.m i10 i5
  let i35 ← mul.m i13 i
  let i36 ← i34 + i35
  let i37 ← mul.m i16 i1
  let i38 ← i36 + i37
  let i39 ← mul.m i4 i2
  let i40 ← i38 + i39
  let i41 ← mul.m i7 b4_19
  let c3 ← i40 + i41
  let i42 ← mul.m i7 i5
  let i43 ← mul.m i10 i
  let i44 ← i42 + i43
  let i45 ← mul.m i13 i1
  let i46 ← i44 + i45
  let i47 ← mul.m i16 i2
  let i48 ← i46 + i47
  let i49 ← mul.m i4 i3
  let c4 ← i48 + i49
  ok (c0, c1, c2, c3, c4)

/-- Stage 2: Propagate carries through c0–c4. Returns `(array, carry, mask)`. Includes creation of
the fresh `out` array. -/
def mul_carry_prop_stage (c0 c1 c2 c3 c4 : U128) :
    Result (Array U64 5#usize × U64 × U64) := do
  let out := Array.repeat 5#usize 0#u64
  let i50 ← c0 >>> 51#i32
  let i51 ← lift (UScalar.cast .U64 i50)
  let i52 ← lift (UScalar.cast .U128 i51)
  let c11 ← c1 + i52
  let i53 ← lift (UScalar.cast .U64 c0)
  let i54 ← mul.LOW_51_BIT_MASK
  let i55 ← lift (i53 &&& i54)
  let out1 ← Array.update out 0#usize i55
  let i56 ← c11 >>> 51#i32
  let i57 ← lift (UScalar.cast .U64 i56)
  let i58 ← lift (UScalar.cast .U128 i57)
  let c21 ← c2 + i58
  let i59 ← lift (UScalar.cast .U64 c11)
  let i60 ← lift (i59 &&& i54)
  let out2 ← Array.update out1 1#usize i60
  let i61 ← c21 >>> 51#i32
  let i62 ← lift (UScalar.cast .U64 i61)
  let i63 ← lift (UScalar.cast .U128 i62)
  let c31 ← c3 + i63
  let i64 ← lift (UScalar.cast .U64 c21)
  let i65 ← lift (i64 &&& i54)
  let out3 ← Array.update out2 2#usize i65
  let i66 ← c31 >>> 51#i32
  let i67 ← lift (UScalar.cast .U64 i66)
  let i68 ← lift (UScalar.cast .U128 i67)
  let c41 ← c4 + i68
  let i69 ← lift (UScalar.cast .U64 c31)
  let i70 ← lift (i69 &&& i54)
  let out4 ← Array.update out3 3#usize i70
  let i71 ← c41 >>> 51#i32
  let carry ← lift (UScalar.cast .U64 i71)
  let i72 ← lift (UScalar.cast .U64 c41)
  let i73 ← lift (i72 &&& i54)
  let out5 ← Array.update out4 4#usize i73
  ok (out5, carry, i54)

/-- Stage 3: Fold carry back via `carry * 19`. Takes mask from `mul_carry_prop_stage`. -/
def mul_final_reduce_stage (out5 : Array U64 5#usize) (carry : U64) (i54 : U64) :
    Result (Array U64 5#usize) := do
  let i74 ← carry * 19#u64
  let i75 ← Array.index_usize out5 0#usize
  let i76 ← i75 + i74
  let out6 ← Array.update out5 0#usize i76
  let i77 ← Array.index_usize out6 0#usize
  let i78 ← i77 >>> 51#i32
  let i79 ← Array.index_usize out6 1#usize
  let i80 ← i79 + i78
  let out7 ← Array.update out6 1#usize i80
  let i81 ← Array.index_usize out7 0#usize
  let i82 ← lift (i81 &&& i54)
  let out8 ← Array.update out7 0#usize i82
  ok out8

/-! ## Fold Theorems -/

theorem fold_mul_product_stage {α : Type} (self _rhs : Array U64 5#usize)
    (f : U128 → U128 → U128 → U128 → U128 → Result α) :
    (do let i ← Array.index_usize _rhs 1#usize; let b1_19 ← i * 19#u64
        let i1 ← Array.index_usize _rhs 2#usize; let b2_19 ← i1 * 19#u64
        let i2 ← Array.index_usize _rhs 3#usize; let b3_19 ← i2 * 19#u64
        let i3 ← Array.index_usize _rhs 4#usize; let b4_19 ← i3 * 19#u64
        let i4 ← Array.index_usize self 0#usize; let i5 ← Array.index_usize _rhs 0#usize
        let i6 ← mul.m i4 i5
        let i7 ← Array.index_usize self 4#usize; let i8 ← mul.m i7 b1_19
        let i9 ← i6 + i8
        let i10 ← Array.index_usize self 3#usize; let i11 ← mul.m i10 b2_19
        let i12 ← i9 + i11
        let i13 ← Array.index_usize self 2#usize; let i14 ← mul.m i13 b3_19
        let i15 ← i12 + i14
        let i16 ← Array.index_usize self 1#usize; let i17 ← mul.m i16 b4_19
        let c0 ← i15 + i17
        let i18 ← mul.m i16 i5; let i19 ← mul.m i4 i; let i20 ← i18 + i19
        let i21 ← mul.m i7 b2_19; let i22 ← i20 + i21
        let i23 ← mul.m i10 b3_19; let i24 ← i22 + i23
        let i25 ← mul.m i13 b4_19; let c1 ← i24 + i25
        let i26 ← mul.m i13 i5; let i27 ← mul.m i16 i; let i28 ← i26 + i27
        let i29 ← mul.m i4 i1; let i30 ← i28 + i29
        let i31 ← mul.m i7 b3_19; let i32 ← i30 + i31
        let i33 ← mul.m i10 b4_19; let c2 ← i32 + i33
        let i34 ← mul.m i10 i5; let i35 ← mul.m i13 i; let i36 ← i34 + i35
        let i37 ← mul.m i16 i1; let i38 ← i36 + i37
        let i39 ← mul.m i4 i2; let i40 ← i38 + i39
        let i41 ← mul.m i7 b4_19; let c3 ← i40 + i41
        let i42 ← mul.m i7 i5; let i43 ← mul.m i10 i; let i44 ← i42 + i43
        let i45 ← mul.m i13 i1; let i46 ← i44 + i45
        let i47 ← mul.m i16 i2; let i48 ← i46 + i47
        let i49 ← mul.m i4 i3; let c4 ← i48 + i49
        f c0 c1 c2 c3 c4) =
    (do let r ← mul_product_stage self _rhs; f r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
  simp only [mul_product_stage, bind_assoc_eq, bind_tc_ok]

theorem fold_mul_carry_prop_stage {α : Type} (c0 c1 c2 c3 c4 : U128)
    (f : Array U64 5#usize → U64 → U64 → Result α) :
    (do let out := Array.repeat 5#usize 0#u64
        let i50 ← c0 >>> 51#i32; let i51 ← lift (UScalar.cast .U64 i50)
        let i52 ← lift (UScalar.cast .U128 i51); let c11 ← c1 + i52
        let i53 ← lift (UScalar.cast .U64 c0); let i54 ← mul.LOW_51_BIT_MASK
        let i55 ← lift (i53 &&& i54); let out1 ← Array.update out 0#usize i55
        let i56 ← c11 >>> 51#i32; let i57 ← lift (UScalar.cast .U64 i56)
        let i58 ← lift (UScalar.cast .U128 i57); let c21 ← c2 + i58
        let i59 ← lift (UScalar.cast .U64 c11); let i60 ← lift (i59 &&& i54)
        let out2 ← Array.update out1 1#usize i60
        let i61 ← c21 >>> 51#i32; let i62 ← lift (UScalar.cast .U64 i61)
        let i63 ← lift (UScalar.cast .U128 i62); let c31 ← c3 + i63
        let i64 ← lift (UScalar.cast .U64 c21); let i65 ← lift (i64 &&& i54)
        let out3 ← Array.update out2 2#usize i65
        let i66 ← c31 >>> 51#i32; let i67 ← lift (UScalar.cast .U64 i66)
        let i68 ← lift (UScalar.cast .U128 i67); let c41 ← c4 + i68
        let i69 ← lift (UScalar.cast .U64 c31); let i70 ← lift (i69 &&& i54)
        let out4 ← Array.update out3 3#usize i70
        let i71 ← c41 >>> 51#i32; let carry ← lift (UScalar.cast .U64 i71)
        let i72 ← lift (UScalar.cast .U64 c41); let i73 ← lift (i72 &&& i54)
        let out5 ← Array.update out4 4#usize i73
        f out5 carry i54) =
    (do let r ← mul_carry_prop_stage c0 c1 c2 c3 c4; f r.1 r.2.1 r.2.2) := by
  simp only [mul_carry_prop_stage, bind_assoc_eq, bind_tc_ok]

theorem fold_mul_final_reduce_stage {α : Type} (out5 : Array U64 5#usize) (carry i54 : U64)
    (f : Array U64 5#usize → Result α) :
    (do let i74 ← carry * 19#u64
        let i75 ← Array.index_usize out5 0#usize; let i76 ← i75 + i74
        let out6 ← Array.update out5 0#usize i76
        let i77 ← Array.index_usize out6 0#usize; let i78 ← i77 >>> 51#i32
        let i79 ← Array.index_usize out6 1#usize; let i80 ← i79 + i78
        let out7 ← Array.update out6 1#usize i80
        let i81 ← Array.index_usize out7 0#usize
        let i82 ← lift (i81 &&& i54)
        let out8 ← Array.update out7 0#usize i82
        f out8) =
    (do let r ← mul_final_reduce_stage out5 carry i54; f r) := by
  simp only [mul_final_reduce_stage, bind_assoc_eq, bind_tc_ok]

/-! ## Bounds Lemmas -/

/-- c0 = a0*b0 + a4*(19*b1) + a3*(19*b2) + a2*(19*b3) + a1*(19*b4).
Coefficient sum: 1 + 4*19 = 77; c0 < 77 * 2^108 < 2^115 -/
private lemma mul_c0_lt_pow2_115 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a0 * b0 + a4 * (b1 * 19) + a3 * (b2 * 19) + a2 * (b3 * 19) + a1 * (b4 * 19) < 2 ^ 115 := by
  have : a0 * b0 < 2 ^ 108 := by nlinarith
  have : a4 * (b1 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a3 * (b2 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (b3 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a1 * (b4 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : (77 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c1 < 59 * 2^108 < 2^115 -/
private lemma mul_c1_lt_pow2_115 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a1 * b0 + a0 * b1 + a4 * (b2 * 19) + a3 * (b3 * 19) + a2 * (b4 * 19) < 2 ^ 115 := by
  have : a1 * b0 < 2 ^ 108 := by nlinarith
  have : a0 * b1 < 2 ^ 108 := by nlinarith
  have : a4 * (b2 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a3 * (b3 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (b4 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : (59 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c2 < 41 * 2^108 < 2^115 -/
private lemma mul_c2_lt_pow2_115 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a2 * b0 + a1 * b1 + a0 * b2 + a4 * (b3 * 19) + a3 * (b4 * 19) < 2 ^ 115 := by
  have : a2 * b0 < 2 ^ 108 := by nlinarith
  have : a1 * b1 < 2 ^ 108 := by nlinarith
  have : a0 * b2 < 2 ^ 108 := by nlinarith
  have : a4 * (b3 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a3 * (b4 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : (41 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c3 < 23 * 2^108 < 2^115 -/
private lemma mul_c3_lt_pow2_115 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 + a4 * (b4 * 19) < 2 ^ 115 := by
  have : a3 * b0 < 2 ^ 108 := by nlinarith
  have : a2 * b1 < 2 ^ 108 := by nlinarith
  have : a1 * b2 < 2 ^ 108 := by nlinarith
  have : a0 * b3 < 2 ^ 108 := by nlinarith
  have : a4 * (b4 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : (23 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- c4 < 5 * 2^108 < 2^115 -/
private lemma mul_c4_lt_pow2_115 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4 < 2 ^ 115 := by
  have : a4 * b0 < 2 ^ 108 := by nlinarith
  have : a3 * b1 < 2 ^ 108 := by nlinarith
  have : a2 * b2 < 2 ^ 108 := by nlinarith
  have : a1 * b3 < 2 ^ 108 := by nlinarith
  have : a0 * b4 < 2 ^ 108 := by nlinarith
  have : (5 : ℕ) * 2 ^ 108 < 2 ^ 115 := by decide
  omega

/-- Tight bound: c1 formula < 59 * 2^108 -/
private lemma mul_c1_lt_tight (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (_ : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a1 * b0 + a0 * b1 + a4 * (b2 * 19) + a3 * (b3 * 19) + a2 * (b4 * 19) < 59 * 2 ^ 108 := by
  have : a1 * b0 < 2 ^ 108 := by nlinarith
  have : a0 * b1 < 2 ^ 108 := by nlinarith
  have : a4 * (b2 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a3 * (b3 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (b4 * 19) < 19 * 2 ^ 108 := by nlinarith
  omega

/-- Tight bound: c2 formula < 41 * 2^108 -/
private lemma mul_c2_lt_tight (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (_ : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a2 * b0 + a1 * b1 + a0 * b2 + a4 * (b3 * 19) + a3 * (b4 * 19) < 41 * 2 ^ 108 := by
  have : a2 * b0 < 2 ^ 108 := by nlinarith
  have : a1 * b1 < 2 ^ 108 := by nlinarith
  have : a0 * b2 < 2 ^ 108 := by nlinarith
  have : a4 * (b3 * 19) < 19 * 2 ^ 108 := by nlinarith
  have : a3 * (b4 * 19) < 19 * 2 ^ 108 := by nlinarith
  omega

/-- Tight bound: c3 formula < 23 * 2^108 -/
private lemma mul_c3_lt_tight (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (_ : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 + a4 * (b4 * 19) < 23 * 2 ^ 108 := by
  have : a3 * b0 < 2 ^ 108 := by nlinarith
  have : a2 * b1 < 2 ^ 108 := by nlinarith
  have : a1 * b2 < 2 ^ 108 := by nlinarith
  have : a0 * b3 < 2 ^ 108 := by nlinarith
  have : a4 * (b4 * 19) < 19 * 2 ^ 108 := by nlinarith
  omega

/-- Tight bound: c4 formula < 5 * 2^108 -/
private lemma mul_c4_lt_tight (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ)
    (ha0 : a0 < 2 ^ 54) (ha1 : a1 < 2 ^ 54) (ha2 : a2 < 2 ^ 54) (ha3 : a3 < 2 ^ 54)
    (ha4 : a4 < 2 ^ 54) (hb0 : b0 < 2 ^ 54) (hb1 : b1 < 2 ^ 54) (hb2 : b2 < 2 ^ 54)
    (hb3 : b3 < 2 ^ 54) (hb4 : b4 < 2 ^ 54) :
    a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4 < 5 * 2 ^ 108 := by
  have : a4 * b0 < 2 ^ 108 := by nlinarith
  have : a3 * b1 < 2 ^ 108 := by nlinarith
  have : a2 * b2 < 2 ^ 108 := by nlinarith
  have : a1 * b3 < 2 ^ 108 := by nlinarith
  have : a0 * b4 < 2 ^ 108 := by nlinarith
  omega

/-- Generic carry chain bound. -/
private lemma carry_chain_lt_pow2_115 (formula carry : ℕ) (K : ℕ)
    (hf : formula < K * 2 ^ 108) (hc : carry < 2 ^ 64) (hK : K ≤ 127) :
    formula + carry < 2 ^ 115 := by
  have : K * 2 ^ 108 + 2 ^ 64 ≤ 128 * 2 ^ 108 := by omega
  have : (128 : ℕ) * 2 ^ 108 = 2 ^ 115 := by decide
  omega

/-- Carry chain conservation. -/
private lemma carry_chain_eq (c0 c1 c2 c3 c4 a0 a1 a2 a3 a4 carry c1' c2' c3' c4' : ℕ)
    (ha0 : a0 = c0 % 2 ^ 51) (ha1 : a1 = c1' % 2 ^ 51) (ha2 : a2 = c2' % 2 ^ 51)
    (ha3 : a3 = c3' % 2 ^ 51) (ha4 : a4 = c4' % 2 ^ 51)
    (hc1' : c1' = c1 + c0 / 2 ^ 51) (hc2' : c2' = c2 + c1' / 2 ^ 51)
    (hc3' : c3' = c3 + c2' / 2 ^ 51) (hc4' : c4' = c4 + c3' / 2 ^ 51)
    (hcarry : carry = c4' / 2 ^ 51) :
    c0 + 2^51*c1 + 2^102*c2 + 2^153*c3 + 2^204*c4 =
    a0 + 2^51*a1 + 2^102*a2 + 2^153*a3 + 2^204*a4 + 2^255*carry := by omega

/-! ## Helper Specs -/

set_option maxHeartbeats 8000000 in
-- Required for step* through 25 monadic multiplication operations
@[step]
theorem mul_product_stage_spec (self _rhs : Array U64 5#usize)
    (hlhs : ∀ i < 5, self[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    mul_product_stage self _rhs ⦃ ((c0, c1, c2, c3, c4) : U128 × U128 × U128 × U128 × U128) =>
      c0.val = self[0]!.val * _rhs[0]!.val + self[4]!.val * (_rhs[1]!.val * 19) +
        self[3]!.val * (_rhs[2]!.val * 19) + self[2]!.val * (_rhs[3]!.val * 19) +
        self[1]!.val * (_rhs[4]!.val * 19) ∧
      c1.val = self[1]!.val * _rhs[0]!.val + self[0]!.val * _rhs[1]!.val +
        self[4]!.val * (_rhs[2]!.val * 19) + self[3]!.val * (_rhs[3]!.val * 19) +
        self[2]!.val * (_rhs[4]!.val * 19) ∧
      c2.val = self[2]!.val * _rhs[0]!.val + self[1]!.val * _rhs[1]!.val +
        self[0]!.val * _rhs[2]!.val + self[4]!.val * (_rhs[3]!.val * 19) +
        self[3]!.val * (_rhs[4]!.val * 19) ∧
      c3.val = self[3]!.val * _rhs[0]!.val + self[2]!.val * _rhs[1]!.val +
        self[1]!.val * _rhs[2]!.val + self[0]!.val * _rhs[3]!.val +
        self[4]!.val * (_rhs[4]!.val * 19) ∧
      c4.val = self[4]!.val * _rhs[0]!.val + self[3]!.val * _rhs[1]!.val +
        self[2]!.val * _rhs[2]!.val + self[1]!.val * _rhs[3]!.val +
        self[0]!.val * _rhs[4]!.val ∧
      c0.val < 2 ^ 115 ∧ c1.val < 2 ^ 115 ∧ c2.val < 2 ^ 115 ∧
      c3.val < 2 ^ 115 ∧ c4.val < 2 ^ 115 ∧
      c1.val < 59 * 2 ^ 108 ∧ c2.val < 41 * 2 ^ 108 ∧
      c3.val < 23 * 2 ^ 108 ∧ c4.val < 5 * 2 ^ 108 ⦄ := by
  unfold mul_product_stage
  simp only [step_simps]
  -- Index rhs limbs
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ b1_19, b1_19_post ⟩ ← U64.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  let* ⟨ b2_19, b2_19_post ⟩ ← U64.mul_spec
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ b3_19, b3_19_post ⟩ ← U64.mul_spec
  let* ⟨ i3, i3_post ⟩ ← Array.index_usize_spec
  let* ⟨ b4_19, b4_19_post ⟩ ← U64.mul_spec
  -- Index self limbs
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post ⟩ ← Array.index_usize_spec
  -- c0 products
  let* ⟨ i6, i6_post ⟩ ← m_spec
  let* ⟨ i7, i7_post ⟩ ← Array.index_usize_spec
  let* ⟨ i8, i8_post ⟩ ← m_spec
  let* ⟨ i9, i9_post ⟩ ← U128.add_spec
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec
  let* ⟨ i11, i11_post ⟩ ← m_spec
  let* ⟨ i12, i12_post ⟩ ← U128.add_spec
  let* ⟨ i13, i13_post ⟩ ← Array.index_usize_spec
  let* ⟨ i14, i14_post ⟩ ← m_spec
  let* ⟨ i15, i15_post ⟩ ← U128.add_spec
  let* ⟨ i16, i16_post ⟩ ← Array.index_usize_spec
  let* ⟨ i17, i17_post ⟩ ← m_spec
  let* ⟨ c0, c0_post ⟩ ← U128.add_spec
  -- c1 products
  let* ⟨ i18, i18_post ⟩ ← m_spec
  let* ⟨ i19, i19_post ⟩ ← m_spec
  let* ⟨ i20, i20_post ⟩ ← U128.add_spec
  let* ⟨ i21, i21_post ⟩ ← m_spec
  let* ⟨ i22, i22_post ⟩ ← U128.add_spec
  let* ⟨ i23, i23_post ⟩ ← m_spec
  let* ⟨ i24, i24_post ⟩ ← U128.add_spec
  let* ⟨ i25, i25_post ⟩ ← m_spec
  let* ⟨ c1, c1_post ⟩ ← U128.add_spec
  -- c2 products
  let* ⟨ i26, i26_post ⟩ ← m_spec
  let* ⟨ i27, i27_post ⟩ ← m_spec
  let* ⟨ i28, i28_post ⟩ ← U128.add_spec
  let* ⟨ i29, i29_post ⟩ ← m_spec
  let* ⟨ i30, i30_post ⟩ ← U128.add_spec
  let* ⟨ i31, i31_post ⟩ ← m_spec
  let* ⟨ i32, i32_post ⟩ ← U128.add_spec
  let* ⟨ i33, i33_post ⟩ ← m_spec
  let* ⟨ c2, c2_post ⟩ ← U128.add_spec
  -- c3 products
  let* ⟨ i34, i34_post ⟩ ← m_spec
  let* ⟨ i35, i35_post ⟩ ← m_spec
  let* ⟨ i36, i36_post ⟩ ← U128.add_spec
  let* ⟨ i37, i37_post ⟩ ← m_spec
  let* ⟨ i38, i38_post ⟩ ← U128.add_spec
  let* ⟨ i39, i39_post ⟩ ← m_spec
  let* ⟨ i40, i40_post ⟩ ← U128.add_spec
  let* ⟨ i41, i41_post ⟩ ← m_spec
  let* ⟨ c3, c3_post ⟩ ← U128.add_spec
  -- c4 products
  let* ⟨ i42, i42_post ⟩ ← m_spec
  let* ⟨ i43, i43_post ⟩ ← m_spec
  let* ⟨ i44, i44_post ⟩ ← U128.add_spec
  let* ⟨ i45, i45_post ⟩ ← m_spec
  let* ⟨ i46, i46_post ⟩ ← U128.add_spec
  let* ⟨ i47, i47_post ⟩ ← m_spec
  let* ⟨ i48, i48_post ⟩ ← U128.add_spec
  let* ⟨ i49, i49_post ⟩ ← m_spec
  let* ⟨ c4, c4_post ⟩ ← U128.add_spec
  subst_vars
  have hc0 : c0.val = self[0]!.val * _rhs[0]!.val + self[4]!.val * (_rhs[1]!.val * 19) +
      self[3]!.val * (_rhs[2]!.val * 19) + self[2]!.val * (_rhs[3]!.val * 19) +
      self[1]!.val * (_rhs[4]!.val * 19) := by simp [*]
  have hc1 : c1.val = self[1]!.val * _rhs[0]!.val + self[0]!.val * _rhs[1]!.val +
      self[4]!.val * (_rhs[2]!.val * 19) + self[3]!.val * (_rhs[3]!.val * 19) +
      self[2]!.val * (_rhs[4]!.val * 19) := by simp [*]
  have hc2 : c2.val = self[2]!.val * _rhs[0]!.val + self[1]!.val * _rhs[1]!.val +
      self[0]!.val * _rhs[2]!.val + self[4]!.val * (_rhs[3]!.val * 19) +
      self[3]!.val * (_rhs[4]!.val * 19) := by simp [*]
  have hc3 : c3.val = self[3]!.val * _rhs[0]!.val + self[2]!.val * _rhs[1]!.val +
      self[1]!.val * _rhs[2]!.val + self[0]!.val * _rhs[3]!.val +
      self[4]!.val * (_rhs[4]!.val * 19) := by simp [*]
  have hc4 : c4.val = self[4]!.val * _rhs[0]!.val + self[3]!.val * _rhs[1]!.val +
      self[2]!.val * _rhs[2]!.val + self[1]!.val * _rhs[3]!.val +
      self[0]!.val * _rhs[4]!.val := by simp [*]
  have hl0 := hlhs 0 (by simp)
  have hl1 := hlhs 1 (by simp)
  have hl2 := hlhs 2 (by simp)
  have hl3 := hlhs 3 (by simp)
  have hl4 := hlhs 4 (by simp)
  have hr0 := hrhs 0 (by simp)
  have hr1 := hrhs 1 (by simp)
  have hr2 := hrhs 2 (by simp)
  have hr3 := hrhs 3 (by simp)
  have hr4 := hrhs 4 (by simp)
  -- Bounds < 2^115 and tight bounds for carry chain
  refine ⟨hc0, hc1, hc2, hc3, hc4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc0]
    exact mul_c0_lt_pow2_115 _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc1]
    exact mul_c1_lt_pow2_115 _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc2]
    exact mul_c2_lt_pow2_115 _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc3]
    exact mul_c3_lt_pow2_115 _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc4]
    exact mul_c4_lt_pow2_115 _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc1]
    exact mul_c1_lt_tight _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc2]
    exact mul_c2_lt_tight _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc3]
    exact mul_c3_lt_tight _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4
  · rw [hc4]
    exact mul_c4_lt_tight _ _ _ _ _ _ _ _ _ _ hl0 hl1 hl2 hl3 hl4 hr0 hr1 hr2 hr3 hr4

set_option maxHeartbeats 8000000 in
-- Required for step* through ~30 monadic carry propagation operations
@[step]
theorem mul_carry_prop_stage_spec (c0 c1 c2 c3 c4 : U128)
    (hc0 : c0.val < 2 ^ 115) (_hc1 : c1.val < 2 ^ 115) (_hc2 : c2.val < 2 ^ 115)
    (_hc3 : c3.val < 2 ^ 115) (_hc4 : c4.val < 2 ^ 115)
    (hc1_tight : c1.val < 59 * 2 ^ 108) (hc2_tight : c2.val < 41 * 2 ^ 108)
    (hc3_tight : c3.val < 23 * 2 ^ 108) (hc4_tight : c4.val < 5 * 2 ^ 108) :
    mul_carry_prop_stage c0 c1 c2 c3 c4
    ⦃ ((a', carry, _mask) : Array U64 5#usize × U64 × U64) =>
      let c1' := c1.val + c0.val / 2 ^ 51
      let c2' := c2.val + c1' / 2 ^ 51
      let c3' := c3.val + c2' / 2 ^ 51
      let c4' := c4.val + c3' / 2 ^ 51
      a'[0]!.val = c0.val % 2 ^ 51 ∧
      a'[1]!.val = c1' % 2 ^ 51 ∧
      a'[2]!.val = c2' % 2 ^ 51 ∧
      a'[3]!.val = c3' % 2 ^ 51 ∧
      a'[4]!.val = c4' % 2 ^ 51 ∧
      carry.val = c4' / 2 ^ 51 ∧
      _mask.val = 2 ^ 51 - 1 ∧
      carry.val < 6 * 2 ^ 57 ⦄ := by
  unfold mul_carry_prop_stage
  simp only [step_simps]
  let* ⟨ i50, i50_post1, i50_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i51, i51_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i52, i52_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c11, c11_post ⟩ ← U128.add_spec
  let* ⟨ i53, i53_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i54, i54_post ⟩ ← LOW_51_BIT_MASK_spec
  let* ⟨ i55, i55_post1, i55_post2 ⟩ ← UScalar.and_spec
  let* ⟨ out1, out1_post ⟩ ← Array.update_spec
  let* ⟨ i56, i56_post1, i56_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i57, i57_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i58, i58_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c21, c21_post ⟩ ← U128.add_spec
  let* ⟨ i59, i59_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i60, i60_post1, i60_post2 ⟩ ← UScalar.and_spec
  let* ⟨ out2, out2_post ⟩ ← Array.update_spec
  let* ⟨ i61, i61_post1, i61_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i62, i62_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i63, i63_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c31, c31_post ⟩ ← U128.add_spec
  let* ⟨ i64, i64_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i65, i65_post1, i65_post2 ⟩ ← UScalar.and_spec
  let* ⟨ out3, out3_post ⟩ ← Array.update_spec
  let* ⟨ i66, i66_post1, i66_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i67, i67_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i68, i68_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c41, c41_post ⟩ ← U128.add_spec
  let* ⟨ i69, i69_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i70, i70_post1, i70_post2 ⟩ ← UScalar.and_spec
  let* ⟨ out4, out4_post ⟩ ← Array.update_spec
  let* ⟨ i71, i71_post1, i71_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ carry, carry_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i72, i72_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i73, i73_post1, i73_post2 ⟩ ← UScalar.and_spec
  let* ⟨ out5, out5_post ⟩ ← Array.update_spec
  -- Interleaved carry chain
  have hcarry0_fits : c0.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c0.val hc0
  have hc11_eq : c11.val = c1.val + c0.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc11_bound : c11.val < 2 ^ 115 := by
    rw [hc11_eq]; exact carry_chain_lt_pow2_115 _ _ 59 hc1_tight hcarry0_fits (by omega)
  have hcarry1_fits : c11.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c11.val hc11_bound
  have hc21_eq : c21.val = c2.val + c11.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc21_bound : c21.val < 2 ^ 115 := by
    rw [hc21_eq]; exact carry_chain_lt_pow2_115 _ _ 41 hc2_tight hcarry1_fits (by omega)
  have hcarry2_fits : c21.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c21.val hc21_bound
  have hc31_eq : c31.val = c3.val + c21.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc31_bound : c31.val < 2 ^ 115 := by
    rw [hc31_eq]; exact carry_chain_lt_pow2_115 _ _ 23 hc3_tight hcarry2_fits (by omega)
  have hcarry3_fits : c31.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c31.val hc31_bound
  have hc41_eq : c41.val = c4.val + c31.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  have hc41_bound : c41.val < 2 ^ 115 := by
    rw [hc41_eq]; exact carry_chain_lt_pow2_115 _ _ 5 hc4_tight hcarry3_fits (by omega)
  have hcarry4_fits : c41.val / 2 ^ 51 < 2 ^ 64 := carry_fits_U64 c41.val hc41_bound
  -- Array values
  have ha5_0 : out5[0]!.val = c0.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 0 4 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 0 3 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 0 2 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 0 1 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 0 (by agrind), UScalar.val_and, UScalar.cast_val_eq,
      UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_1 : out5[1]!.val = c11.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 1 4 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 1 3 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 1 2 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 1 (by agrind),
      UScalar.val_and, UScalar.cast_val_eq, UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_2 : out5[2]!.val = c21.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 2 4 (by agrind) (by agrind) (by omega),
      Array.set_of_ne_getElem! _ _ 2 3 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 2 (by agrind), UScalar.val_and, UScalar.cast_val_eq, UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_3 : out5[3]!.val = c31.val % 2 ^ 51 := by
    simp only [*, Array.set_of_ne_getElem! _ _ 3 4 (by agrind) (by agrind) (by omega),
      Array.set_of_eq _ _ 3 (by agrind), UScalar.val_and, UScalar.cast_val_eq,
      UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    omega
  have ha5_4 : out5[4]!.val = c41.val % 2 ^ 51 := by
    simp only [*, Array.set_of_eq _ _ 4 (by agrind), UScalar.val_and, UScalar.cast_val_eq,
      UScalarTy.numBits]
    simp only [Nat.and_two_pow_sub_one_eq_mod] at *
    agrind
  have hcarry_val : carry.val = c41.val / 2 ^ 51 := by
    simp only [*, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    omega
  exact ⟨ha5_0,
    by rw [ha5_1, hc11_eq],
    by rw [ha5_2, hc21_eq, hc11_eq],
    by rw [ha5_3, hc31_eq, hc21_eq, hc11_eq],
    by rw [ha5_4, hc41_eq, hc31_eq, hc21_eq, hc11_eq],
    by rw [hcarry_val, hc41_eq, hc31_eq, hc21_eq, hc11_eq],
    by simp [*],
    by rw [hcarry_val]
       have hc41_tight : c41.val < 6 * 2 ^ 108 := by
         rw [hc41_eq]; omega
       have : (6 : ℕ) * 2 ^ 108 / 2 ^ 51 = 6 * 2 ^ 57 := by decide
       calc c41.val / 2 ^ 51 ≤ (6 * 2 ^ 108 - 1) / 2 ^ 51 := Nat.div_le_div_right (by omega)
         _ < 6 * 2 ^ 57 := by decide⟩

set_option maxHeartbeats 8000000 in
-- Required for step* through final reduction operations
@[step]
theorem mul_final_reduce_stage_spec (a' : Array U64 5#usize) (carry i54 : U64)
    (ha' : ∀ i < 5, a'[i]!.val < 2 ^ 51) (hcarry : carry.val < 6 * 2 ^ 57)
    (hmask : i54.val = 2 ^ 51 - 1) :
    mul_final_reduce_stage a' carry i54 ⦃ (result : Array U64 5#usize) =>
      result[0]!.val = (a'[0]!.val + 19 * carry.val) % 2 ^ 51 ∧
      result[1]!.val = a'[1]!.val + (a'[0]!.val + 19 * carry.val) / 2 ^ 51 ∧
      result[2]!.val = a'[2]!.val ∧
      result[3]!.val = a'[3]!.val ∧
      result[4]!.val = a'[4]!.val ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold mul_final_reduce_stage
  let* ⟨ i74, i74_post ⟩ ← U64.mul_spec
  let* ⟨ i75, i75_post ⟩ ← Array.index_usize_spec
  let* ⟨ i76, i76_post ⟩ ← U64.add_spec
  let* ⟨ out6, out6_post ⟩ ← Array.update_spec
  let* ⟨ i77, i77_post ⟩ ← Array.index_usize_spec
  let* ⟨ i78, i78_post1, i78_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i79, i79_post ⟩ ← Array.index_usize_spec
  have h_i75 : i75.val = a'[0]!.val := by simp [*]
  have h_i76 : i76.val = a'[0]!.val + 19 * carry.val := by
    simp only [i76_post, h_i75, i74_post]; omega
  have h_i77 : i77.val = a'[0]!.val + 19 * carry.val := by
    simp [*]; omega
  have h_i78 : i78.val = (a'[0]!.val + 19 * carry.val) / 2 ^ 51 := by
    simp only [i78_post1, Nat.shiftRight_eq_div_pow, h_i77]
  have h_i79 : i79.val = a'[1]!.val := by
    simp [*]
  let* ⟨ i80, i80_post ⟩ ← U64.add_spec
  let* ⟨ out7, out7_post ⟩ ← Array.update_spec
  let* ⟨ i81, i81_post ⟩ ← Array.index_usize_spec
  let* ⟨ i82, i82_post1, i82_post2 ⟩ ← UScalar.and_spec
  let* ⟨ out8, out8_post ⟩ ← Array.update_spec
  have ha8_0 : out8[0]!.val = (a'[0]!.val + 19 * carry.val) % 2 ^ 51 := by
    simp only [out8_post, Array.set_of_eq _ _ 0 (by agrind)]
    simp only [i82_post1, UScalar.val_and, hmask]
    rw [show i81 = out7[0]! from by simp [i81_post]]
    rw [Nat.and_two_pow_sub_one_eq_mod]
    simp [out7_post, Array.set_of_ne_getElem! _ _ 0 1 (by agrind) (by agrind) (by omega),
      out6_post, h_i76]
  have ha8_1 : out8[1]!.val = a'[1]!.val + (a'[0]!.val + 19 * carry.val) / 2 ^ 51 := by
    simp only [out8_post, Array.set_of_ne_getElem! _ _ 1 0 (by agrind) (by agrind) (by omega),
      out7_post, Array.set_of_eq _ _ 1 (by agrind),
      i80_post, h_i79, h_i78]
  have ha8_2 : out8[2]!.val = a'[2]!.val := by
    simp only [out8_post,
      out7_post, Array.set_of_ne_getElem! _ _ 2 1 (by agrind) (by agrind) (by omega),
      out6_post, Array.set_of_ne_getElem! _ _ 2 0 (by agrind) (by agrind) (by omega)]
  have ha8_3 : out8[3]!.val = a'[3]!.val := by
    simp only [out8_post,
      out7_post, Array.set_of_ne_getElem! _ _ 3 1 (by agrind) (by agrind) (by omega),
      out6_post, Array.set_of_ne_getElem! _ _ 3 0 (by agrind) (by agrind) (by omega)]
  have ha8_4 : out8[4]!.val = a'[4]!.val := by
    simp only [out8_post,
      out7_post, Array.set_of_ne_getElem! _ _ 4 1 (by agrind) (by agrind) (by omega),
      out6_post, Array.set_of_ne_getElem! _ _ 4 0 (by agrind) (by agrind) (by omega)]
  have ha8_lt : ∀ i < 5, out8[i]!.val < 2 ^ 52 := by
    intro i hi; interval_cases i
    · rw [ha8_0]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by omega)
    · rw [ha8_1]
      have : a'[1]!.val < 2 ^ 51 := ha' 1 (by simp)
      have : a'[0]!.val < 2 ^ 51 := ha' 0 (by simp)
      have : (a'[0]!.val + 19 * carry.val) / 2 ^ 51 ≤ 2 ^ 13 - 1 := by omega
      omega
    · rw [ha8_2]; exact Nat.lt_of_lt_of_le (ha' 2 (by simp)) (by omega)
    · rw [ha8_3]; exact Nat.lt_of_lt_of_le (ha' 3 (by simp)) (by omega)
    · rw [ha8_4]; exact Nat.lt_of_lt_of_le (ha' 4 (by simp)) (by omega)
  exact ⟨ha8_0, ha8_1, ha8_2, ha8_3, ha8_4, ha8_lt⟩

/-! ## Main Proof -/

set_option maxHeartbeats 14000000 in
-- Required for step* through fold-decomposed mul body
@[step]
theorem mul_spec (lhs rhs : Array U64 5#usize)
    (hlhs : ∀ i < 5, lhs[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, rhs[i]!.val < 2 ^ 54) :
    mul lhs rhs ⦃ r =>
      Field51_as_Nat r ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] ∧
      (∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by
  unfold mul
  simp only [fold_mul_product_stage, fold_mul_carry_prop_stage, fold_mul_final_reduce_stage]
  step as ⟨ prod, prod_post ⟩
  step as ⟨ cp, cp_post ⟩
  step as ⟨ red, red_post1, red_post2, red_post3, red_post4, red_post5, red_post6 ⟩
  · intro i hi; obtain ⟨h0, h1, h2, h3, h4, _⟩ := cp_post
    interval_cases i <;> simp only [*] <;> exact Nat.mod_lt _ (by positivity)
  -- Extract carry prop postconditions
  have ha'_0 := cp_post.1
  have ha'_1 := cp_post.2.1
  have ha'_2 := cp_post.2.2.1
  have ha'_3 := cp_post.2.2.2.1
  have ha'_4 := cp_post.2.2.2.2.1
  have hcarry_val := cp_post.2.2.2.2.2.1
  -- Product identity mod p
  have a_mul : (prod.1.val + 2^51 * prod.2.1.val + 2^102 * prod.2.2.1.val +
      2^153 * prod.2.2.2.1.val + 2^204 * prod.2.2.2.2.val)
      ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] := by
    have := decompose lhs[0]!.val lhs[1]!.val lhs[2]!.val lhs[3]!.val lhs[4]!.val
      rhs[0]!.val rhs[1]!.val rhs[2]!.val rhs[3]!.val rhs[4]!.val
    have := prod_post.1; have := prod_post.2.1; have := prod_post.2.2.1
    have := prod_post.2.2.2.1; have := prod_post.2.2.2.2.1
    simp_all only [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, mul_zero, pow_zero, one_mul]
  -- Carry chain conservation
  set v0 := prod.1.val; set v1 := prod.2.1.val
  set v2 := prod.2.2.1.val; set v3 := prod.2.2.2.1.val
  set v4 := prod.2.2.2.2.val
  have h_chain := carry_chain_eq v0 v1 v2 v3 v4
      _ _ _ _ _ _
      (v1 + v0 / 2 ^ 51)
      (v2 + (v1 + v0 / 2 ^ 51) / 2 ^ 51)
      (v3 + (v2 + (v1 + v0 / 2 ^ 51) / 2 ^ 51) / 2 ^ 51)
      (v4 + (v3 + (v2 + (v1 + v0 / 2 ^ 51)
        / 2 ^ 51) / 2 ^ 51) / 2 ^ 51)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  -- Field51_as_Nat of the reduced result
  have hf_r : Field51_as_Nat red =
      (cp.1[0]!.val + 19 * cp.2.1.val) + 2^51 * cp.1[1]!.val + 2^102 * cp.1[2]!.val +
      2^153 * cp.1[3]!.val + 2^204 * cp.1[4]!.val := by
    unfold Field51_as_Nat
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [red_post1, red_post2, red_post3, red_post4, red_post5]
    have := Nat.mod_add_div (cp.1[0]!.val + 19 * cp.2.1.val) (2 ^ 51)
    omega
  -- h_key: Field51_as_Nat red + carry * p = c0 + 2^51*c1 + ...
  have h_key : Field51_as_Nat red + cp.2.1.val * p =
      prod.1.val + 2^51 * prod.2.1.val + 2^102 * prod.2.2.1.val +
      2^153 * prod.2.2.2.1.val + 2^204 * prod.2.2.2.2.val := by
    rw [hf_r, h_chain]
    simp only [ha'_0, ha'_1, ha'_2, ha'_3, ha'_4, hcarry_val]
    unfold p; omega
  have hmul : Field51_as_Nat red ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] :=
    (modeq_of_add_mul_eq _ _ cp.2.1.val p h_key).trans a_mul
  exact ⟨hmul, red_post6⟩

end CoreOpsArithMulSharedAFieldElement51FieldElement51
end curve25519_dalek.Shared0FieldElement51.Insts
