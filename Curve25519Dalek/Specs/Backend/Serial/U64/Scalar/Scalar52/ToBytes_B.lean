/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.BitList_B

/-! # Spec Theorem for `Scalar52::to_bytes` -- Option B (standalone bitlistify approach)

This is a standalone proof of `to_bytes_spec` that uses the STANDARD Nat-level `@[step]` specs
(which `step*` provides automatically), then converts the Nat-level postconditions to BitList form
using conversion lemmas from `BitList_B.lean`.

## Proof flow

1. `unfold to_bytes; step*` -- step through all operations using standard Nat-level specs
2. Derive Nat-level byte values: `byte.val = limb.val / 2^shift % 2^8`
3. Convert to BitList form: `ofU8 byte = (ofU64 limb).extract shift (shift+8)`
4. Resolve `result[k]! = byte` and lift BitList equalities to `result` level
5. Use the bridge lemma to close the final goal
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52.v_b
open List BitList
attribute [local simp] Array.length_eq

/-! ## Bridge lemmas

These connect 32 byte-level BitList equalities to the Nat-level equality
`U8x32_as_Nat result = Scalar52_as_Nat self`. -/

/-- If `Scalar52_as_Nat a < L`, then the top limb `a[4]` is bounded by `2^48`. -/
private theorem top_limb_lt (a : Array U64 5#usize) (h : Scalar52_as_Nat a < L) :
    (a : List U64)[4]!.val < 2 ^ 48 := by
  unfold Scalar52_as_Nat at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  have : L < 2 ^ 253 := by unfold L; omega
  grind

/-- At a shared byte, the lower and upper nibble contributions recombine. -/
private theorem shared_byte_recombine (x a : Nat) :
    (x % 2 ^ 4) * 2 ^ a + (x / 2 ^ 4) * 2 ^ (a + 4) = x * 2 ^ a := by
  conv_lhs => rw [show (2 : Nat) ^ (a + 4) = 2 ^ 4 * 2 ^ a from by ring]
  have : x / 2 ^ 4 * (2 ^ 4 * 2 ^ a) = x / 2 ^ 4 * 2 ^ 4 * 2 ^ a := by ring
  rw [this, ← Nat.add_mul]
  grind

/-- Bridge from 5 BitList limb equivalences to the Nat-level equality. -/
private theorem scalar52_eq_of_bitList_limbs (a : Scalar52) (b : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i < 5, (a : List U64)[i]!.val < 2 ^ 52) (h' : (a : List U64)[4]!.val < 2 ^ 48)
    (hlimb0 : (ofU64 (a : List U64)[0]!).take 52 ≈ₗ ofU8 b[0]! ++ ofU8 b[1]! ++ ofU8 b[2]! ++
        ofU8 b[3]! ++ ofU8 b[4]! ++ ofU8 b[5]! ++ (ofU8 b[6]!).take 4)
    (hlimb1 : (ofU64 (a : List U64)[1]!).take 52 ≈ₗ (ofU8 b[6]!).drop 4 ++
        ofU8 b[7]! ++ ofU8 b[8]! ++ ofU8 b[9]! ++ ofU8 b[10]! ++ ofU8 b[11]! ++ ofU8 b[12]!)
    (hlimb2 : (ofU64 (a : List U64)[2]!).take 52 ≈ₗ ofU8 b[13]! ++ ofU8 b[14]! ++ ofU8 b[15]! ++
        ofU8 b[16]! ++ ofU8 b[17]! ++ ofU8 b[18]! ++ (ofU8 b[19]!).take 4)
    (hlimb3 : (ofU64 (a : List U64)[3]!).take 52 ≈ₗ (ofU8 b[19]!).drop 4 ++
        ofU8 b[20]! ++ ofU8 b[21]! ++ ofU8 b[22]! ++ ofU8 b[23]! ++ ofU8 b[24]! ++ ofU8 b[25]!)
    (hlimb4 : (ofU64 (a : List U64)[4]!).take 48 ≈ₗ ofU8 b[26]! ++ ofU8 b[27]! ++ ofU8 b[28]! ++
        ofU8 b[29]! ++ ofU8 b[30]! ++ ofU8 b[31]!) :
    U8x32_as_Nat b = Scalar52_as_Nat a := by
  have h0 := hlimb0.toNat_eq
  have h1 := hlimb1.toNat_eq
  have h2 := hlimb2.toNat_eq
  have h3 := hlimb3.toNat_eq
  have h4 := hlimb4.toNat_eq
  simp only [toNat_take, toNat_drop, toNat_append, toNat_ofU8, toNat_ofU64, ofU8_length,
    length_drop, length_append, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd] at h0 h1 h2 h3 h4
  unfold U8x32_as_Nat Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reducePow, Nat.reduceMul, one_mul]
  have hb0 := h 0 (by omega)
  have hb1 := h 1 (by omega)
  have hb2 := h 2 (by omega)
  have hb3 := h 3 (by omega)
  have hb6 := shared_byte_recombine b[6]!.val 48
  have hb19 := shared_byte_recombine b[19]!.val 152
  have hls : a.val.length = 5 := a.property
  have hlr : b.val.length = 32 := b.property
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem, Option.getD_some, hls, hlr, Nat.reduceLT] at *
  grind

/-- Bridge from 32 byte-level BitList equalities to `U8x32_as_Nat = Scalar52_as_Nat`. -/
private theorem scalar52_eq_of_bitList_bytes
    (self : Scalar52) (result : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i < 5, (self : List U64)[i]!.val < 2 ^ 52) (h' : Scalar52_as_Nat self < L)
    (hb0 : ofU8 result[0]! = (ofU64 (self : List U64)[0]!).extract 0 8)
    (hb1 : ofU8 result[1]! = (ofU64 (self : List U64)[0]!).extract 8 16)
    (hb2 : ofU8 result[2]! = (ofU64 (self : List U64)[0]!).extract 16 24)
    (hb3 : ofU8 result[3]! = (ofU64 (self : List U64)[0]!).extract 24 32)
    (hb4 : ofU8 result[4]! = (ofU64 (self : List U64)[0]!).extract 32 40)
    (hb5 : ofU8 result[5]! = (ofU64 (self : List U64)[0]!).extract 40 48)
    (hb6 : ofU8 result[6]! = (ofU64 (self : List U64)[0]!).extract 48 52 ++
                             (ofU64 (self : List U64)[1]!).extract 0 4)
    (hb7 : ofU8 result[7]! = (ofU64 (self : List U64)[1]!).extract 4 12)
    (hb8 : ofU8 result[8]! = (ofU64 (self : List U64)[1]!).extract 12 20)
    (hb9 : ofU8 result[9]! = (ofU64 (self : List U64)[1]!).extract 20 28)
    (hb10 : ofU8 result[10]! = (ofU64 (self : List U64)[1]!).extract 28 36)
    (hb11 : ofU8 result[11]! = (ofU64 (self : List U64)[1]!).extract 36 44)
    (hb12 : ofU8 result[12]! = (ofU64 (self : List U64)[1]!).extract 44 52)
    (hb13 : ofU8 result[13]! = (ofU64 (self : List U64)[2]!).extract 0 8)
    (hb14 : ofU8 result[14]! = (ofU64 (self : List U64)[2]!).extract 8 16)
    (hb15 : ofU8 result[15]! = (ofU64 (self : List U64)[2]!).extract 16 24)
    (hb16 : ofU8 result[16]! = (ofU64 (self : List U64)[2]!).extract 24 32)
    (hb17 : ofU8 result[17]! = (ofU64 (self : List U64)[2]!).extract 32 40)
    (hb18 : ofU8 result[18]! = (ofU64 (self : List U64)[2]!).extract 40 48)
    (hb19 : ofU8 result[19]! = (ofU64 (self : List U64)[2]!).extract 48 52 ++
                               (ofU64 (self : List U64)[3]!).extract 0 4)
    (hb20 : ofU8 result[20]! = (ofU64 (self : List U64)[3]!).extract 4 12)
    (hb21 : ofU8 result[21]! = (ofU64 (self : List U64)[3]!).extract 12 20)
    (hb22 : ofU8 result[22]! = (ofU64 (self : List U64)[3]!).extract 20 28)
    (hb23 : ofU8 result[23]! = (ofU64 (self : List U64)[3]!).extract 28 36)
    (hb24 : ofU8 result[24]! = (ofU64 (self : List U64)[3]!).extract 36 44)
    (hb25 : ofU8 result[25]! = (ofU64 (self : List U64)[3]!).extract 44 52)
    (hb26 : ofU8 result[26]! = (ofU64 (self : List U64)[4]!).extract 0 8)
    (hb27 : ofU8 result[27]! = (ofU64 (self : List U64)[4]!).extract 8 16)
    (hb28 : ofU8 result[28]! = (ofU64 (self : List U64)[4]!).extract 16 24)
    (hb29 : ofU8 result[29]! = (ofU64 (self : List U64)[4]!).extract 24 32)
    (hb30 : ofU8 result[30]! = (ofU64 (self : List U64)[4]!).extract 32 40)
    (hb31 : ofU8 result[31]! = (ofU64 (self : List U64)[4]!).extract 40 48) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
  apply scalar52_eq_of_bitList_limbs self result h
    (by have := h 4 (by omega); have := top_limb_lt self h'; grind)
  · -- hlimb0
    rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6]
    rw [List.extract_append_extract _ 0 8 16 (by omega) (by omega),
        List.extract_append_extract _ 0 16 24 (by omega) (by omega),
        List.extract_append_extract _ 0 24 32 (by omega) (by omega),
        List.extract_append_extract _ 0 32 40 (by omega) (by omega),
        List.extract_append_extract _ 0 40 48 (by omega) (by omega)]
    rw [List.take_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [List.extract_append_extract _ 0 48 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb1
    rw [hb6, List.drop_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [hb7, hb8, hb9, hb10, hb11, hb12]
    rw [List.extract_append_extract _ 0 4 12 (by omega) (by omega),
        List.extract_append_extract _ 0 12 20 (by omega) (by omega),
        List.extract_append_extract _ 0 20 28 (by omega) (by omega),
        List.extract_append_extract _ 0 28 36 (by omega) (by omega),
        List.extract_append_extract _ 0 36 44 (by omega) (by omega),
        List.extract_append_extract _ 0 44 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb2
    rw [hb13, hb14, hb15, hb16, hb17, hb18, hb19]
    rw [List.extract_append_extract _ 0 8 16 (by omega) (by omega),
        List.extract_append_extract _ 0 16 24 (by omega) (by omega),
        List.extract_append_extract _ 0 24 32 (by omega) (by omega),
        List.extract_append_extract _ 0 32 40 (by omega) (by omega),
        List.extract_append_extract _ 0 40 48 (by omega) (by omega)]
    rw [List.take_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [List.extract_append_extract _ 0 48 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb3
    rw [hb19, List.drop_left' (by simp [List.extract_eq_drop_take, ofU64_length])]
    rw [hb20, hb21, hb22, hb23, hb24, hb25]
    rw [List.extract_append_extract _ 0 4 12 (by omega) (by omega),
        List.extract_append_extract _ 0 12 20 (by omega) (by omega),
        List.extract_append_extract _ 0 20 28 (by omega) (by omega),
        List.extract_append_extract _ 0 28 36 (by omega) (by omega),
        List.extract_append_extract _ 0 36 44 (by omega) (by omega),
        List.extract_append_extract _ 0 44 52 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]
  · -- hlimb4
    rw [hb26, hb27, hb28, hb29, hb30, hb31]
    rw [List.extract_append_extract _ 0 8 16 (by omega) (by omega),
        List.extract_append_extract _ 0 16 24 (by omega) (by omega),
        List.extract_append_extract _ 0 24 32 (by omega) (by omega),
        List.extract_append_extract _ 0 32 40 (by omega) (by omega),
        List.extract_append_extract _ 0 40 48 (by omega) (by omega)]
    simp [List.extract_eq_drop_take]

/-! ## Conversion helpers -/

/-- Combined shift+cast+bitlistify: from raw `step*`
postconditions directly to BitList extract form. -/
private theorem shr_cast_to_extract
    {limb shr : U64} {byte : U8} {k : Nat}
    (hk : k + 8 ≤ 64)
    (hshr : shr.val = limb.val >>> k)
    (hbyte : byte = UScalar.cast .U8 shr) :
    ofU8 byte = (ofU64 limb).extract k (k + 8) := by
  apply bitlistify_simple hk
  rw [hbyte, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq,
      hshr, Nat.shiftRight_eq_div_pow]

/-! ## Main theorem -/

set_option maxHeartbeats 8000000 in -- step* over 32 byte operations + simp_lists resolution
/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`** (Option B):
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧ U8x32_as_Nat result < L ⦄ := by
    unfold to_bytes
    step*
    -- Phase 1: Extract limb bounds
    have hA0 : i.val < 2 ^ 52 := by
      rw [i_post]; have := h 0 (by omega); simpa only [Array.getElem!_Nat_eq] using this
    have hA1 : i14.val < 2 ^ 52 := by
      rw [i14_post]; have := h 1 (by omega); simpa only [Array.getElem!_Nat_eq] using this
    have hA2 : i30.val < 2 ^ 52 := by
      rw [i30_post]; have := h 2 (by omega); simpa only [Array.getElem!_Nat_eq] using this
    have hA3 : i44.val < 2 ^ 52 := by
      rw [i44_post]; have := h 3 (by omega); simpa only [Array.getElem!_Nat_eq] using this
    -- Phase 2: Convert all bytes to BitList extract form
    -- Simple bytes (30 of 32): shift+cast → extract
    have bl0 := shr_cast_to_extract (k := 0) (by omega) i1_post1 i2_post
    have bl1 := shr_cast_to_extract (k := 8) (by omega) i3_post1 i4_post
    have bl2 := shr_cast_to_extract (k := 16) (by omega) i5_post1 i6_post
    have bl3 := shr_cast_to_extract (k := 24) (by omega) i7_post1 i8_post
    have bl4 := shr_cast_to_extract (k := 32) (by omega) i9_post1 i10_post
    have bl5 := shr_cast_to_extract (k := 40) (by omega) i11_post1 i12_post
    have bl7 := shr_cast_to_extract (k := 4) (by omega) i18_post1 i19_post
    have bl8 := shr_cast_to_extract (k := 12) (by omega) i20_post1 i21_post
    have bl9 := shr_cast_to_extract (k := 20) (by omega) i22_post1 i23_post
    have bl10 := shr_cast_to_extract (k := 28) (by omega) i24_post1 i25_post
    have bl11 := shr_cast_to_extract (k := 36) (by omega) i26_post1 i27_post
    have bl12 := shr_cast_to_extract (k := 44) (by omega) i28_post1 i29_post
    have bl13 := shr_cast_to_extract (k := 0) (by omega) i31_post1 i32_post
    have bl14 := shr_cast_to_extract (k := 8) (by omega) i33_post1 i34_post
    have bl15 := shr_cast_to_extract (k := 16) (by omega) i35_post1 i36_post
    have bl16 := shr_cast_to_extract (k := 24) (by omega) i37_post1 i38_post
    have bl17 := shr_cast_to_extract (k := 32) (by omega) i39_post1 i40_post
    have bl18 := shr_cast_to_extract (k := 40) (by omega) i41_post1 i42_post
    have bl20 := shr_cast_to_extract (k := 4) (by omega) i48_post1 i49_post
    have bl21 := shr_cast_to_extract (k := 12) (by omega) i50_post1 i51_post
    have bl22 := shr_cast_to_extract (k := 20) (by omega) i52_post1 i53_post
    have bl23 := shr_cast_to_extract (k := 28) (by omega) i54_post1 i55_post
    have bl24 := shr_cast_to_extract (k := 36) (by omega) i56_post1 i57_post
    have bl25 := shr_cast_to_extract (k := 44) (by omega) i58_post1 i59_post
    have bl26 := shr_cast_to_extract (k := 0) (by omega) i61_post1 i62_post
    have bl27 := shr_cast_to_extract (k := 8) (by omega) i63_post1 i64_post
    have bl28 := shr_cast_to_extract (k := 16) (by omega) i65_post1 i66_post
    have bl29 := shr_cast_to_extract (k := 24) (by omega) i67_post1 i68_post
    have bl30 := shr_cast_to_extract (k := 32) (by omega) i69_post1 i70_post
    have bl31 := shr_cast_to_extract (k := 40) (by omega) i71_post1 i72_post
    -- Shared bytes (2 of 32): shift+OR+cast → concat of extracts
    have bl6 := bitlistify_shared hA0 hA1
      (by rw [i13_post1, Nat.shiftRight_eq_div_pow])
      (by rw [i15_post1, Nat.shiftLeft_eq])
      i16_post2 i17_post
    have bl19 := bitlistify_shared hA2 hA3
      (by rw [i43_post1, Nat.shiftRight_eq_div_pow])
      (by rw [i45_post1, Nat.shiftLeft_eq])
      i46_post2 i47_post
    -- Phase 3: Apply bridge lemma
    have h_list : ∀ i < 5, (self : List U64)[i]!.val < 2 ^ 52 := by
      intro i hi; have := h i hi
      simp only [Array.getElem!_Nat_eq] at this; exact this
    suffices h_eq : U8x32_as_Nat result = Scalar52_as_Nat self from
      ⟨h_eq, h_eq ▸ h'⟩
    apply scalar52_eq_of_bitList_bytes self result h_list h'
    -- 32 subgoals: resolve result[k]! to the byte variable, then use blN
    all_goals (
      subst_vars
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
      simp_lists
      assumption)

end curve25519_dalek.backend.serial.u64.scalar.Scalar52.v_b
