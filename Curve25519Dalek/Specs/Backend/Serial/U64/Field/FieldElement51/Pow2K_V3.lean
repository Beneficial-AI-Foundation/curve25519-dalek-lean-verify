/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-! # Pow2K — V3: Fold Theorem Decomposition

Refactoring of Pow2K.lean using the Aeneas "fold theorem" pattern.
The monadic function `pow2k_loop` is decomposed into 3 helper functions.
Each has a fold theorem and `@[step]` spec. The main proof uses
`simp_rw [fold_*]` to collapse the inline code, then `step*` applies the specs.
-/

set_option linter.hashCommand false
#setup_aeneas_simps

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.v3

open curve25519_dalek.backend.serial.u64.field.FieldElement51 (pow2k pow2k_loop)
open curve25519_dalek.backend.serial.u64.field.FieldElement51.pow2k (m LOW_51_BIT_MASK)

-- Re-prove step specs in our namespace
@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (result : U128) => result.val = x.val * y.val ⦄ := by
  unfold m; step*

@[step]
theorem LOW_51_BIT_MASK_spec :
    LOW_51_BIT_MASK ⦃ (result : U64) => result.val = 2^51 - 1 ⦄ := by
  unfold LOW_51_BIT_MASK; step*

/-! ## Helper Functions -/

/-- Stage 1: Compute the 5 intermediate products for field squaring. -/
def square_stage (a : Array U64 5#usize) : Result (U128 × U128 × U128 × U128 × U128) := do
  let i ← Array.index_usize a 3#usize
  let a3_19 ← 19#u64 * i
  let i1 ← Array.index_usize a 4#usize
  let a4_19 ← 19#u64 * i1
  let i2 ← Array.index_usize a 0#usize
  let i3 ← m i2 i2
  let i4 ← Array.index_usize a 1#usize
  let i5 ← m i4 a4_19
  let i6 ← Array.index_usize a 2#usize
  let i7 ← m i6 a3_19
  let i8 ← i5 + i7
  let i9 ← 2#u128 * i8
  let c0 ← i3 + i9
  let i10 ← m i a3_19
  let i11 ← m i2 i4
  let i12 ← m i6 a4_19
  let i13 ← i11 + i12
  let i14 ← 2#u128 * i13
  let c1 ← i10 + i14
  let i15 ← m i4 i4
  let i16 ← m i2 i6
  let i17 ← m i1 a3_19
  let i18 ← i16 + i17
  let i19 ← 2#u128 * i18
  let c2 ← i15 + i19
  let i20 ← m i1 a4_19
  let i21 ← m i2 i
  let i22 ← m i4 i6
  let i23 ← i21 + i22
  let i24 ← 2#u128 * i23
  let c3 ← i20 + i24
  let i25 ← m i6 i6
  let i26 ← m i2 i1
  let i27 ← m i4 i
  let i28 ← i26 + i27
  let i29 ← 2#u128 * i28
  let c4 ← i25 + i29
  ok (c0, c1, c2, c3, c4)

/-- Stage 2: Propagate carries through the 5 accumulators, producing reduced array + carry. -/
def carry_prop_stage (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U128) :
    Result (Array U64 5#usize × U64 × U64) := do
  let i30 ← c0 >>> 51#i32
  let i31 ← lift (UScalar.cast .U64 i30)
  let i32 ← lift (UScalar.cast .U128 i31)
  let c11 ← c1 + i32
  let i33 ← lift (UScalar.cast .U64 c0)
  let i34 ← LOW_51_BIT_MASK
  let i35 ← lift (i33 &&& i34)
  let a1 ← Array.update a 0#usize i35
  let i36 ← c11 >>> 51#i32
  let i37 ← lift (UScalar.cast .U64 i36)
  let i38 ← lift (UScalar.cast .U128 i37)
  let c21 ← c2 + i38
  let i39 ← lift (UScalar.cast .U64 c11)
  let i40 ← lift (i39 &&& i34)
  let a2 ← Array.update a1 1#usize i40
  let i41 ← c21 >>> 51#i32
  let i42 ← lift (UScalar.cast .U64 i41)
  let i43 ← lift (UScalar.cast .U128 i42)
  let c31 ← c3 + i43
  let i44 ← lift (UScalar.cast .U64 c21)
  let i45 ← lift (i44 &&& i34)
  let a3 ← Array.update a2 2#usize i45
  let i46 ← c31 >>> 51#i32
  let i47 ← lift (UScalar.cast .U64 i46)
  let i48 ← lift (UScalar.cast .U128 i47)
  let c41 ← c4 + i48
  let i49 ← lift (UScalar.cast .U64 c31)
  let i50 ← lift (i49 &&& i34)
  let a4 ← Array.update a3 3#usize i50
  let i51 ← c41 >>> 51#i32
  let carry ← lift (UScalar.cast .U64 i51)
  let i52 ← lift (UScalar.cast .U64 c41)
  let i53 ← lift (i52 &&& i34)
  let a5 ← Array.update a4 4#usize i53
  ok (a5, carry, i34)

/-- Stage 3: Final reduction — fold carry back via multiplication by 19.
    Takes the mask (from carry_prop_stage's LOW_51_BIT_MASK call) as parameter. -/
def final_reduce_stage (a5 : Array U64 5#usize) (carry : U64) (i34 : U64) :
    Result (Array U64 5#usize) := do
  let i54 ← carry * 19#u64
  let i55 ← Array.index_usize a5 0#usize
  let i56 ← i55 + i54
  let a6 ← Array.update a5 0#usize i56
  let i57 ← Array.index_usize a6 0#usize
  let i58 ← i57 >>> 51#i32
  let i59 ← Array.index_usize a6 1#usize
  let i60 ← i59 + i58
  let a7 ← Array.update a6 1#usize i60
  let i61 ← Array.index_usize a7 0#usize
  let i62 ← lift (i61 &&& i34)
  let a8 ← Array.update a7 0#usize i62
  ok a8

/-! ## Fold Theorems -/

theorem fold_square_stage {α : Type} (a : Array U64 5#usize)
    (f : U128 → U128 → U128 → U128 → U128 → Result α) :
    (do let i ← Array.index_usize a 3#usize; let a3_19 ← 19#u64 * i
        let i1 ← Array.index_usize a 4#usize; let a4_19 ← 19#u64 * i1
        let i2 ← Array.index_usize a 0#usize; let i3 ← m i2 i2
        let i4 ← Array.index_usize a 1#usize; let i5 ← m i4 a4_19
        let i6 ← Array.index_usize a 2#usize; let i7 ← m i6 a3_19
        let i8 ← i5 + i7; let i9 ← 2#u128 * i8; let c0 ← i3 + i9
        let i10 ← m i a3_19; let i11 ← m i2 i4; let i12 ← m i6 a4_19
        let i13 ← i11 + i12; let i14 ← 2#u128 * i13; let c1 ← i10 + i14
        let i15 ← m i4 i4; let i16 ← m i2 i6; let i17 ← m i1 a3_19
        let i18 ← i16 + i17; let i19 ← 2#u128 * i18; let c2 ← i15 + i19
        let i20 ← m i1 a4_19; let i21 ← m i2 i; let i22 ← m i4 i6
        let i23 ← i21 + i22; let i24 ← 2#u128 * i23; let c3 ← i20 + i24
        let i25 ← m i6 i6; let i26 ← m i2 i1; let i27 ← m i4 i
        let i28 ← i26 + i27; let i29 ← 2#u128 * i28; let c4 ← i25 + i29
        f c0 c1 c2 c3 c4) =
    (do let r ← square_stage a; f r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
  simp only [square_stage, bind_assoc_eq, bind_tc_ok]

theorem fold_carry_prop_stage {α : Type} (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U128)
    (f : Array U64 5#usize → U64 → U64 → Result α) :
    (do let i30 ← c0 >>> 51#i32; let i31 ← lift (UScalar.cast .U64 i30)
        let i32 ← lift (UScalar.cast .U128 i31); let c11 ← c1 + i32
        let i33 ← lift (UScalar.cast .U64 c0); let i34 ← LOW_51_BIT_MASK
        let i35 ← lift (i33 &&& i34); let a1 ← Array.update a 0#usize i35
        let i36 ← c11 >>> 51#i32; let i37 ← lift (UScalar.cast .U64 i36)
        let i38 ← lift (UScalar.cast .U128 i37); let c21 ← c2 + i38
        let i39 ← lift (UScalar.cast .U64 c11); let i40 ← lift (i39 &&& i34)
        let a2 ← Array.update a1 1#usize i40
        let i41 ← c21 >>> 51#i32; let i42 ← lift (UScalar.cast .U64 i41)
        let i43 ← lift (UScalar.cast .U128 i42); let c31 ← c3 + i43
        let i44 ← lift (UScalar.cast .U64 c21); let i45 ← lift (i44 &&& i34)
        let a3 ← Array.update a2 2#usize i45
        let i46 ← c31 >>> 51#i32; let i47 ← lift (UScalar.cast .U64 i46)
        let i48 ← lift (UScalar.cast .U128 i47); let c41 ← c4 + i48
        let i49 ← lift (UScalar.cast .U64 c31); let i50 ← lift (i49 &&& i34)
        let a4 ← Array.update a3 3#usize i50
        let i51 ← c41 >>> 51#i32; let carry ← lift (UScalar.cast .U64 i51)
        let i52 ← lift (UScalar.cast .U64 c41); let i53 ← lift (i52 &&& i34)
        let a5 ← Array.update a4 4#usize i53
        f a5 carry i34) =
    (do let r ← carry_prop_stage a c0 c1 c2 c3 c4; f r.1 r.2.1 r.2.2) := by
  simp only [carry_prop_stage, bind_assoc_eq, bind_tc_ok]

theorem fold_final_reduce_stage {α : Type} (a5 : Array U64 5#usize) (carry i34 : U64)
    (f : Array U64 5#usize → Result α) :
    (do let i54 ← carry * 19#u64
        let i55 ← Array.index_usize a5 0#usize; let i56 ← i55 + i54
        let a6 ← Array.update a5 0#usize i56
        let i57 ← Array.index_usize a6 0#usize; let i58 ← i57 >>> 51#i32
        let i59 ← Array.index_usize a6 1#usize; let i60 ← i59 + i58
        let a7 ← Array.update a6 1#usize i60
        let i61 ← Array.index_usize a7 0#usize
        let i62 ← lift (i61 &&& i34)
        let a8 ← Array.update a7 0#usize i62
        f a8) =
    (do let r ← final_reduce_stage a5 carry i34; f r) := by
  simp only [final_reduce_stage, bind_assoc_eq, bind_tc_ok]

/-! ## Helper Specs (sorry'd — structure only) -/

@[step]
theorem square_stage_spec (a : Array U64 5#usize) (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    square_stage a ⦃ (result : U128 × U128 × U128 × U128 × U128) =>
      let (c0, c1, c2, c3, c4) := result
      c0.val = a[0]!.val * a[0]!.val + 2 * (a[1]!.val * (19 * a[4]!.val) + a[2]!.val * (19 * a[3]!.val)) ∧
      c1.val = a[3]!.val * (19 * a[3]!.val) + 2 * (a[0]!.val * a[1]!.val + a[2]!.val * (19 * a[4]!.val)) ∧
      c2.val = a[1]!.val * a[1]!.val + 2 * (a[0]!.val * a[2]!.val + a[4]!.val * (19 * a[3]!.val)) ∧
      c3.val = a[4]!.val * (19 * a[4]!.val) + 2 * (a[0]!.val * a[3]!.val + a[1]!.val * a[2]!.val) ∧
      c4.val = a[2]!.val * a[2]!.val + 2 * (a[0]!.val * a[4]!.val + a[1]!.val * a[3]!.val) ∧
      c0.val < 2 ^ 115 ∧ c1.val < 2 ^ 115 ∧ c2.val < 2 ^ 115 ∧
      c3.val < 2 ^ 115 ∧ c4.val < 2 ^ 115 ⦄ := by
  unfold square_stage
  simp only [step_simps]
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ a3_19, a3_19_post ⟩ ← U64.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  let* ⟨ a4_19, a4_19_post ⟩ ← U64.mul_spec
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ i3, i3_post ⟩ ← m_spec
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post ⟩ ← m_spec
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post ⟩ ← m_spec
  let* ⟨ i8, i8_post ⟩ ← U128.add_spec
  let* ⟨ i9, i9_post ⟩ ← U128.mul_spec
  let* ⟨ c0, c0_post ⟩ ← U128.add_spec
  let* ⟨ i10, i10_post ⟩ ← m_spec
  let* ⟨ i11, i11_post ⟩ ← m_spec
  let* ⟨ i12, i12_post ⟩ ← m_spec
  let* ⟨ i13, i13_post ⟩ ← U128.add_spec
  let* ⟨ i14, i14_post ⟩ ← U128.mul_spec
  let* ⟨ c1, c1_post ⟩ ← U128.add_spec
  let* ⟨ i15, i15_post ⟩ ← m_spec
  let* ⟨ i16, i16_post ⟩ ← m_spec
  let* ⟨ i17, i17_post ⟩ ← m_spec
  let* ⟨ i18, i18_post ⟩ ← U128.add_spec
  let* ⟨ i19, i19_post ⟩ ← U128.mul_spec
  let* ⟨ c2, c2_post ⟩ ← U128.add_spec
  let* ⟨ i20, i20_post ⟩ ← m_spec
  let* ⟨ i21, i21_post ⟩ ← m_spec
  let* ⟨ i22, i22_post ⟩ ← m_spec
  let* ⟨ i23, i23_post ⟩ ← U128.add_spec
  let* ⟨ i24, i24_post ⟩ ← U128.mul_spec
  let* ⟨ c3, c3_post ⟩ ← U128.add_spec
  let* ⟨ i25, i25_post ⟩ ← m_spec
  let* ⟨ i26, i26_post ⟩ ← m_spec
  let* ⟨ i27, i27_post ⟩ ← m_spec
  let* ⟨ i28, i28_post ⟩ ← U128.add_spec
  let* ⟨ i29, i29_post ⟩ ← U128.mul_spec
  let* ⟨ c4, c4_post ⟩ ← U128.add_spec
  sorry

@[step]
theorem carry_prop_stage_spec (a : Array U64 5#usize) (c0 c1 c2 c3 c4 : U128)
    (hc0 : c0.val < 2 ^ 115) (hc1 : c1.val < 2 ^ 115) (hc2 : c2.val < 2 ^ 115)
    (hc3 : c3.val < 2 ^ 115) (hc4 : c4.val < 2 ^ 115) :
    carry_prop_stage a c0 c1 c2 c3 c4 ⦃ (result : Array U64 5#usize × U64 × U64) =>
      let (a', carry, _mask) := result
      a'[0]!.val = c0.val % 2 ^ 51 ∧
      a'[1]!.val = (c1.val + c0.val / 2 ^ 51) % 2 ^ 51 ∧
      a'[2]!.val = (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      a'[3]!.val = (c3.val + (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      a'[4]!.val = (c4.val + (c3.val + (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51 ∧
      carry.val = (c4.val + (c3.val + (c2.val + (c1.val + c0.val / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51 ⦄ := by
  unfold carry_prop_stage
  simp only [step_simps]
  let* ⟨ i30, i30_post1, i30_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i31, i31_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i32, i32_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c11, c11_post ⟩ ← U128.add_spec
  let* ⟨ i33, i33_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i34, i34_post ⟩ ← LOW_51_BIT_MASK_spec
  let* ⟨ i35, i35_post1, i35_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a1, a1_post ⟩ ← Array.update_spec
  let* ⟨ i36, i36_post1, i36_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i37, i37_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i38, i38_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c21, c21_post ⟩ ← U128.add_spec
  let* ⟨ i39, i39_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i40, i40_post1, i40_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a2, a2_post ⟩ ← Array.update_spec
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i42, i42_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i43, i43_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c31, c31_post ⟩ ← U128.add_spec
  let* ⟨ i44, i44_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i45, i45_post1, i45_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a3, a3_post ⟩ ← Array.update_spec
  let* ⟨ i46, i46_post1, i46_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ i47, i47_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i48, i48_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ c41, c41_post ⟩ ← U128.add_spec
  let* ⟨ i49, i49_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i50, i50_post1, i50_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a4, a4_post ⟩ ← Array.update_spec
  let* ⟨ i51, i51_post1, i51_post2 ⟩ ← U128.ShiftRight_IScalar_spec
  let* ⟨ carry, carry_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i52, i52_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ i53, i53_post1, i53_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a5, a5_post ⟩ ← Array.update_spec
  sorry

@[step]
theorem final_reduce_stage_spec (a' : Array U64 5#usize) (carry i34 : U64)
    (ha' : ∀ i < 5, a'[i]!.val < 2 ^ 51) (hcarry : carry.val < 2 ^ 13)
    (hmask : i34.val = 2 ^ 51 - 1) :
    final_reduce_stage a' carry i34 ⦃ (result : Array U64 5#usize) =>
      result[0]!.val = (a'[0]!.val + 19 * carry.val) % 2 ^ 51 ∧
      result[1]!.val = a'[1]!.val + (a'[0]!.val + 19 * carry.val) / 2 ^ 51 ∧
      result[2]!.val = a'[2]!.val ∧
      result[3]!.val = a'[3]!.val ∧
      result[4]!.val = a'[4]!.val ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold final_reduce_stage
  let* ⟨ i54, i54_post ⟩ ← U64.mul_spec
  let* ⟨ i55, i55_post ⟩ ← Array.index_usize_spec
  let* ⟨ i56, i56_post ⟩ ← U64.add_spec
  let* ⟨ a6, a6_post ⟩ ← Array.update_spec
  let* ⟨ i57, i57_post ⟩ ← Array.index_usize_spec
  let* ⟨ i58, i58_post1, i58_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i59, i59_post ⟩ ← Array.index_usize_spec
  let* ⟨ i60, i60_post ⟩ ← U64.add_spec
  · sorry
  let* ⟨ a7, a7_post ⟩ ← Array.update_spec
  let* ⟨ i61, i61_post ⟩ ← Array.index_usize_spec
  let* ⟨ i62, i62_post1, i62_post2 ⟩ ← UScalar.and_spec
  let* ⟨ a8, a8_post ⟩ ← Array.update_spec
  sorry

/-! ## Main Proof -/

@[step]
theorem pow2k_loop_spec (k : U32) (a : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    pow2k_loop k a ⦃ (result : Std.Array U64 5#usize) =>
      Field51_as_Nat result ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
      (if k.val = 0 then result = a else ∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k_loop
  split
  case isTrue hlt =>
    -- Fold the three stages
    simp_rw [fold_square_stage, fold_carry_prop_stage, fold_final_reduce_stage]
    -- Now step* should use square_stage_spec, carry_prop_stage_spec, final_reduce_stage_spec
    step*
    · simp [*]
      sorry
    · sorry
    · sorry
    · sorry
  case isFalse hge =>
    step*
    have : k.val = 0 := by grind
    simpa [this] using Nat.ModEq.trans rfl rfl
  termination_by k.val
  decreasing_by grind

@[step]
theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (_ : 0 < k.val)
    (_ : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow2k self k ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (Field51_as_Nat self)^(2^k.val) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow2k
  step*
  exact ⟨‹_›, by agrind⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51.v3
