/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Tactics
import Curve25519Dalek.ExternallyVerified


/-! # to_bytes

Specification and proof for `FieldElement51::to_bytes`.

Much of the proof and aux lemmas contributed by Son Ho.

This function converts a field element to its canonical 32-byte little-endian representation.
It performs reduction modulo 2^255-19 and encodes the result as bytes.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
- move general helpers lemmas to a more central location
- move to standard library the following:
  attribute [simp_scalar_simps] BitVec.toNat_shiftLeft
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

-- TODO: generalize and add to the standard library
@[local simp]
theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  simp only [UScalar.cast, UScalarTy.U64_numBits_eq, UScalarTy.U8_numBits_eq,
    Aeneas.Bvify.U64.UScalar_bv, BitVec.truncate_eq_setWidth]
  simp only [UScalar.val]
  simp only [UScalarTy.U8_numBits_eq, BitVec.toNat_setWidth, UScalar.bv_toNat,
    UScalarTy.U64_numBits_eq, Aeneas.Bvify.U64.UScalar_bv]

-- This is specific to the problem below
theorem recompose_decomposed_limb (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val =
  limb.val % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 8 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 48 % 2 ^ 8)
  := by
  bvify 64 at *
  bv_decide

-- TODO: move to standard library
attribute [simp_scalar] BitVec.toNat_shiftLeft

-- TODO: move general helpers lemmas to a more central location


-- Byte reconstruction for split limbs at each boundary.
-- Boundary byte k uses (limb_lo >>> hi_shift ||| limb_hi <<< lo_shift).
-- The 4 boundaries have lo_shifts: 3, 6, 1, 4.

theorem recompose_decomposed_limb_shift3 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 3 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 5 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 13 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 21 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 29 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 37 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 45 % 2 ^ 8) =
  2 ^ 3 * limb.val := by bvify 64 at *; bv_decide

theorem recompose_decomposed_limb_shift6 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 6 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 2 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 10 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 18 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 26 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 34 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 42 % 2 ^ 8)
  + 2 ^ 56 * (limb.val >>> 50 % 2 ^ 8) =
  2 ^ 6 * limb.val := by bvify 64 at *; bv_decide

theorem recompose_decomposed_limb_shift1 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 1 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 7 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 15 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 23 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 31 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 39 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 47 % 2 ^ 8) =
  2 ^ 1 * limb.val := by bvify 64 at *; bv_decide

theorem recompose_decomposed_limb_shift4 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 4 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 4 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 12 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 20 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 28 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 36 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 44 % 2 ^ 8) =
  2 ^ 4 * limb.val := by bvify 64 at *; bv_decide

-- OR decomposition at boundary bytes: the shifted halves occupy disjoint bit ranges.
-- One lemma per boundary shift.
theorem decompose_or_limbs_shift3 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 48 ||| limb1.val <<< 3 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 48 % 2 ^ 8) + ((limb1.val <<< 3) % 2 ^ 8) := by
  bvify 64 at *
  have : BitVec.ofNat 64 (limb1.val <<< 3 % U64.size) = limb1.bv <<< 3 := by
    natify; simp_scalar
  rw [this]; bv_decide

theorem decompose_or_limbs_shift6 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 45 ||| limb1.val <<< 6 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 45 % 2 ^ 8) + ((limb1.val <<< 6) % 2 ^ 8) := by
  bvify 64 at *
  have : BitVec.ofNat 64 (limb1.val <<< 6 % U64.size) = limb1.bv <<< 6 := by
    natify; simp_scalar
  rw [this]; bv_decide

theorem decompose_or_limbs_shift1 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 50 ||| limb1.val <<< 1 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 50 % 2 ^ 8) + ((limb1.val <<< 1) % 2 ^ 8) := by
  bvify 64 at *
  have : BitVec.ofNat 64 (limb1.val <<< 1 % U64.size) = limb1.bv <<< 1 := by
    natify; simp_scalar
  rw [this]; bv_decide

theorem decompose_or_limbs_shift4 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 47 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 47 % 2 ^ 8) + ((limb1.val <<< 4) % 2 ^ 8) := by
  bvify 64 at *
  have : BitVec.ofNat 64 (limb1.val <<< 4 % U64.size) = limb1.bv <<< 4 := by
    natify; simp_scalar
  rw [this]; bv_decide

/-- Byte-by-byte packing formula for 5 × 51-bit limbs into 32 LE bytes.
    Matches the Rust source (field.rs:419-452) and the Lean extraction.
    The 4 boundary bytes (6, 12, 19, 25) combine bits from adjacent limbs.

    NOTE: This describes the byte packing of CANONICALIZED limbs (each < 2^51).
    The full `to_bytes` function first reduces and canonicalizes before packing. -/
def bytes_match_limbs (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  -- Limb 0 (bits 0-50) → bytes 0-6
  s.val[0]!.val = L.val[0]!.val % 2^8 ∧
  s.val[1]!.val = L.val[0]!.val >>> 8 % 2^8 ∧
  s.val[2]!.val = L.val[0]!.val >>> 16 % 2^8 ∧
  s.val[3]!.val = L.val[0]!.val >>> 24 % 2^8 ∧
  s.val[4]!.val = L.val[0]!.val >>> 32 % 2^8 ∧
  s.val[5]!.val = L.val[0]!.val >>> 40 % 2^8 ∧
  s.val[6]!.val = (L.val[0]!.val >>> 48 ||| L.val[1]!.val <<< 3 % U64.size) % 2^8 ∧
  -- Limb 1 (bits 51-101) → bytes 7-12
  s.val[7]!.val = L.val[1]!.val >>> 5 % 2^8 ∧
  s.val[8]!.val = L.val[1]!.val >>> 13 % 2^8 ∧
  s.val[9]!.val = L.val[1]!.val >>> 21 % 2^8 ∧
  s.val[10]!.val = L.val[1]!.val >>> 29 % 2^8 ∧
  s.val[11]!.val = L.val[1]!.val >>> 37 % 2^8 ∧
  s.val[12]!.val = (L.val[1]!.val >>> 45 ||| L.val[2]!.val <<< 6 % U64.size) % 2^8 ∧
  -- Limb 2 (bits 102-152) → bytes 13-19
  s.val[13]!.val = L.val[2]!.val >>> 2 % 2^8 ∧
  s.val[14]!.val = L.val[2]!.val >>> 10 % 2^8 ∧
  s.val[15]!.val = L.val[2]!.val >>> 18 % 2^8 ∧
  s.val[16]!.val = L.val[2]!.val >>> 26 % 2^8 ∧
  s.val[17]!.val = L.val[2]!.val >>> 34 % 2^8 ∧
  s.val[18]!.val = L.val[2]!.val >>> 42 % 2^8 ∧
  s.val[19]!.val = (L.val[2]!.val >>> 50 ||| L.val[3]!.val <<< 1 % U64.size) % 2^8 ∧
  -- Limb 3 (bits 153-203) → bytes 20-25
  s.val[20]!.val = L.val[3]!.val >>> 7 % 2^8 ∧
  s.val[21]!.val = L.val[3]!.val >>> 15 % 2^8 ∧
  s.val[22]!.val = L.val[3]!.val >>> 23 % 2^8 ∧
  s.val[23]!.val = L.val[3]!.val >>> 31 % 2^8 ∧
  s.val[24]!.val = L.val[3]!.val >>> 39 % 2^8 ∧
  s.val[25]!.val = (L.val[3]!.val >>> 47 ||| L.val[4]!.val <<< 4 % U64.size) % 2^8 ∧
  -- Limb 4 (bits 204-254) → bytes 26-31
  s.val[26]!.val = L.val[4]!.val >>> 4 % 2^8 ∧
  s.val[27]!.val = L.val[4]!.val >>> 12 % 2^8 ∧
  s.val[28]!.val = L.val[4]!.val >>> 20 % 2^8 ∧
  s.val[29]!.val = L.val[4]!.val >>> 28 % 2^8 ∧
  s.val[30]!.val = L.val[4]!.val >>> 36 % 2^8 ∧
  s.val[31]!.val = L.val[4]!.val >>> 44 % 2^8


/-- Byte packing correctness: when all limbs < 2^51 and bytes match the packing formula,
    the little-endian byte interpretation equals the radix-2^51 limb interpretation. -/
theorem byte_packing_eq (L : Array U64 5#usize) (s : Array U8 32#usize)
    (hL : ∀ i < 5, (L.val[i]! : U64).val < 2 ^ 51)
    (hbytes : bytes_match_limbs L s) :
    U8x32_as_Nat s = Field51_as_Nat L := by
  unfold bytes_match_limbs at hbytes
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
          hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
          hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31⟩ := hbytes
  have hL0 : (L.val[0]! : U64).val < 2 ^ 51 := hL 0 (by omega)
  have hL1 : (L.val[1]! : U64).val < 2 ^ 51 := hL 1 (by omega)
  have hL2 : (L.val[2]! : U64).val < 2 ^ 51 := hL 2 (by omega)
  have hL3 : (L.val[3]! : U64).val < 2 ^ 51 := hL 3 (by omega)
  have hL4 : (L.val[4]! : U64).val < 2 ^ 51 := hL 4 (by omega)
  have hd6 := decompose_or_limbs_shift3 L.val[0]! L.val[1]! hL0
  have hd12 := decompose_or_limbs_shift6 L.val[1]! L.val[2]! hL1
  have hd19 := decompose_or_limbs_shift1 L.val[2]! L.val[3]! hL2
  have hd25 := decompose_or_limbs_shift4 L.val[3]! L.val[4]! hL3
  have hr0 := recompose_decomposed_limb L.val[0]! hL0
  have hr1 := recompose_decomposed_limb_shift3 L.val[1]! hL1
  have hr2 := recompose_decomposed_limb_shift6 L.val[2]! hL2
  have hr3 := recompose_decomposed_limb_shift1 L.val[3]! hL3
  have hr4 := recompose_decomposed_limb_shift4 L.val[4]! hL4
  unfold U8x32_as_Nat Field51_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Array.getElem!_Nat_eq, Nat.reduceMul,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
    hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
    hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31,
    hd6, hd12, hd19, hd25]
  linarith

/-- AND with a mask whose value is 2^51-1 gives a value < 2^51. -/
private lemma and_mask_lt_pow (x mask : U64) (hm : mask.val = 2 ^ 51 - 1) :
    (x &&& mask).val < 2^51 := by
  rw [UScalar.val_and, hm]
  have := @Nat.and_le_right x.val (2^51 - 1)
  omega

/-- For a U8 value < 128, AND with 128 is 0 (bit 7 is clear). -/
private lemma u8_and_128_eq_zero_of_lt (x : U8) (h : x.val < 128) :
    (x &&& 128#u8).val = 0 := by
  bvify 8 at *
  bv_decide

/-- A 64-bit value AND'd with 2^51-1, then shifted right by 44, fits in 7 bits. -/
private lemma masked_shift44_lt_128 (x : BitVec 64) :
    ((x &&& (BitVec.ofNat 64 (2^51 - 1))) >>> 44).toNat < 128 := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have := @Nat.and_le_right x.toNat (2^51 - 1)
  norm_num at *; omega

/-- Canonical reduction: the q-computation + conditional subtraction + carry chain
    produces a value that is congruent mod p and canonical (< p).

    The algorithm computes q = ⌊(F + 19) / 2^255⌋ ∈ {0,1}, then adds 19*q to limb 0
    and carry-propagates with masking to 51 bits. The result satisfies:
    - Field51_as_Nat(output) ≡ Field51_as_Nat(input) [MOD p]
    - Field51_as_Nat(output) < p

    Ported from Verus `lemma_to_bytes_reduction` in dalek-lite. -/
private lemma canonical_reduction_mod_p
    (f0 f1 f2 f3 f4 : ℕ)
    (hf0 : f0 < 2 ^ 52) (hf1 : f1 < 2 ^ 52) (hf2 : f2 < 2 ^ 52)
    (hf3 : f3 < 2 ^ 52) (hf4 : f4 < 2 ^ 52)
    -- q = quotient bit from carry chain on (F + 19)
    (q : ℕ)
    (hq : q = (((((f0 + 19) / 2 ^ 51 + f1) / 2 ^ 51 + f2) / 2 ^ 51 + f3) / 2 ^ 51 + f4) / 2 ^ 51)
    -- output limbs = carry-propagate(input + 19*q) masked to 51 bits
    (l0 l1 l2 l3 l4 : ℕ)
    (hl0 : l0 = (f0 + 19 * q) % 2 ^ 51)
    (hl1 : l1 = (f1 + (f0 + 19 * q) / 2 ^ 51) % 2 ^ 51)
    (hl2 : l2 = (f2 + (f1 + (f0 + 19 * q) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    (hl3 : l3 = (f3 + (f2 + (f1 + (f0 + 19 * q) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51)
    (hl4 : l4 = (f4 + (f3 + (f2 + (f1 + (f0 + 19 * q) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) / 2 ^ 51) % 2 ^ 51) :
    (l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4) % (2 ^ 255 - 19) =
      (f0 + 2 ^ 51 * f1 + 2 ^ 102 * f2 + 2 ^ 153 * f3 + 2 ^ 204 * f4) % (2 ^ 255 - 19) ∧
    l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4 < 2 ^ 255 - 19 := by
  sorry

/-! ## Spec for `to_bytes` -/

set_option maxHeartbeats 800000 in -- heavy progress*
/-- **Spec for `backend.serial.u64.field.FieldElement51.to_bytes`**:

This function converts a field element to its canonical 32-byte little-endian representation.
The implementation performs reduction modulo p = 2^255-19 to ensure the result is in
canonical form.

The algorithm:
1. Reduces the field element using `reduce` to ensure all limbs are within bounds
2. Performs a final conditional reduction to ensure the result is < p
3. Packs the 5 limbs (each 51 bits) into 32 bytes in little-endian format

Specification:
- The function succeeds (no panic)
- The natural number interpretation of the byte array is congruent to the field element value modulo p
- The byte array represents the unique canonical form (0 ≤ value < p)
-/
@[externally_verified, progress] -- proven in Verus
theorem to_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    to_bytes self ⦃ result =>
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p ⦄ := by
  unfold to_bytes
  simp only [step_simps]
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← reduce_spec
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ i1, i1_post ⟩ ← U64.add_spec
  let* ⟨ q, q_post1, q_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ i3, i3_post ⟩ ← U64.add_spec
  · expand fe_post1 with 5; scalar_tac
  let* ⟨ q1, q1_post1, q1_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post ⟩ ← U64.add_spec
  · expand fe_post1 with 5; scalar_tac
  let* ⟨ q2, q2_post1, q2_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post ⟩ ← U64.add_spec
  · expand fe_post1 with 5; scalar_tac
  let* ⟨ q3, q3_post1, q3_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
  let* ⟨ i9, i9_post ⟩ ← U64.add_spec
  · expand fe_post1 with 5; scalar_tac
  let* ⟨ q4, q4_post1, q4_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i10, i10_post ⟩ ← U64.mul_spec
  · expand fe_post1 with 5; scalar_tac
  let* ⟨ i11, i11_post ⟩ ← U64.add_spec
  · expand fe_post1 with 5; scalar_tac
  let* ⟨ limbs, limbs_post ⟩ ← Array.update_spec
  let* ⟨ i12, i12_post1, i12_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ low_51_bit_mask, low_51_bit_mask_post1, low_51_bit_mask_post2 ⟩ ← U64.sub_spec
  let* ⟨ i13, i13_post ⟩ ← Array.index_usize_spec
  let* ⟨ i14, i14_post1, i14_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i15, i15_post ⟩ ← Array.index_usize_spec
  let* ⟨ i16, i16_post ⟩ ← U64.add_spec
  · have h14 : (i14 : U64).val < (2^13 : ℕ) := by
      have : (i13 : U64).val < (2^64 : ℕ) := by agrind
      rw [i14_post1, Nat.shiftRight_eq_div_pow]; agrind
    have h15 : (i15 : U64).val < (2^52 : ℕ) := by
      simp only [i15_post, limbs_post, Array.set_val_eq] at *;
      simp_all only [Array.getElem!_Nat_eq,
        List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
        Nat.ofNat_pos, UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, Nat.one_lt_ofNat,
        Nat.reduceLT, Nat.lt_add_one, Nat.reduceShiftLeft, U64.ofNat_bv, BitVec.reduceHShiftLeft,
        List.length_set, List.getElem_set_self, Nat.not_eq, ne_eq, zero_ne_one, not_false_eq_true,
        one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self, ↓List.getElem!_set_ne]
    grind only [= U64.max_eq]
  let* ⟨ limbs1, limbs1_post ⟩ ← Array.update_spec
  let* ⟨ i17, i17_post ⟩ ← Array.index_usize_spec
  let* ⟨ i18, i18_post1, i18_post2 ⟩ ← UScalar.and_spec
  let* ⟨ limbs2, limbs2_post ⟩ ← Array.update_spec
  let* ⟨ i19, i19_post ⟩ ← Array.index_usize_spec
  let* ⟨ i20, i20_post1, i20_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i21, i21_post ⟩ ← Array.index_usize_spec
  let* ⟨ i22, i22_post ⟩ ← U64.add_spec
  · have h20 : (i20 : U64).val < (2^13 : ℕ) := by
      have : (i19 : U64).val < (2^64 : ℕ) := by agrind
      rw [i20_post1, Nat.shiftRight_eq_div_pow]; agrind
    have h21 : (i21 : U64).val < (2^52 : ℕ) := by
      simp only [i21_post, limbs2_post, limbs1_post, limbs_post, Array.set_val_eq] at *; simp_all
    grind only [= U64.max_eq]
  let* ⟨ limbs3, limbs3_post ⟩ ← Array.update_spec
  let* ⟨ i23, i23_post ⟩ ← Array.index_usize_spec
  let* ⟨ i24, i24_post1, i24_post2 ⟩ ← UScalar.and_spec
  let* ⟨ limbs4, limbs4_post ⟩ ← Array.update_spec
  let* ⟨ i25, i25_post ⟩ ← Array.index_usize_spec
  let* ⟨ i26, i26_post1, i26_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i27, i27_post ⟩ ← Array.index_usize_spec
  let* ⟨ i28, i28_post ⟩ ← U64.add_spec
  · have h26 : (i26 : U64).val < (2^13 : ℕ) := by
      have : (i25 : U64).val < (2^64 : ℕ) := by agrind
      rw [i26_post1, Nat.shiftRight_eq_div_pow]; omega
    have h27 : (i27 : U64).val < (2^52 : ℕ) := by
      simp only [i27_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post, limbs_post,
        Array.set_val_eq] at *; simp_all
    grind only [= U64.max_eq]
  let* ⟨ limbs5, limbs5_post ⟩ ← Array.update_spec
  let* ⟨ i29, i29_post ⟩ ← Array.index_usize_spec
  let* ⟨ i30, i30_post1, i30_post2 ⟩ ← UScalar.and_spec
  let* ⟨ limbs6, limbs6_post ⟩ ← Array.update_spec
  let* ⟨ i31, i31_post ⟩ ← Array.index_usize_spec
  let* ⟨ i32, i32_post1, i32_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i33, i33_post ⟩ ← Array.index_usize_spec
  let* ⟨ i34, i34_post ⟩ ← U64.add_spec
  · have h32 : (i32 : U64).val < (2^13 : ℕ) := by
      have : (i31 : U64).val < (2^64 : ℕ) := by agrind
      rw [i32_post1, Nat.shiftRight_eq_div_pow]; omega
    have h33 : (i33 : U64).val < (2^52 : ℕ) := by
      simp only [i33_post, limbs6_post, limbs5_post, limbs4_post, limbs3_post, limbs2_post,
        limbs1_post, limbs_post, Array.set_val_eq] at *; simp_all
    grind only [= U64.max_eq]
  let* ⟨ limbs7, limbs7_post ⟩ ← Array.update_spec
  let* ⟨ i35, i35_post ⟩ ← Array.index_usize_spec
  let* ⟨ i36, i36_post1, i36_post2 ⟩ ← UScalar.and_spec
  let* ⟨ limbs8, limbs8_post ⟩ ← Array.update_spec
  let* ⟨ i37, i37_post ⟩ ← Array.index_usize_spec
  let* ⟨ i38, i38_post1, i38_post2 ⟩ ← UScalar.and_spec
  let* ⟨ limbs9, limbs9_post ⟩ ← Array.update_spec
  let* ⟨ i39, i39_post ⟩ ← Array.index_usize_spec
  let* ⟨ i40, i40_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s1, s1_post ⟩ ← Array.update_spec
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i42, i42_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s2, s2_post ⟩ ← Array.update_spec
  let* ⟨ i43, i43_post1, i43_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i44, i44_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s3, s3_post ⟩ ← Array.update_spec
  let* ⟨ i45, i45_post1, i45_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i46, i46_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s4, s4_post ⟩ ← Array.update_spec
  let* ⟨ i47, i47_post1, i47_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i48, i48_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s5, s5_post ⟩ ← Array.update_spec
  let* ⟨ i49, i49_post1, i49_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i50, i50_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s6, s6_post ⟩ ← Array.update_spec
  let* ⟨ i51, i51_post1, i51_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i52, i52_post ⟩ ← Array.index_usize_spec
  let* ⟨ i53, i53_post1, i53_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i54, i54_post1, i54_post2 ⟩ ← UScalar.or_spec
  let* ⟨ i55, i55_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s7, s7_post ⟩ ← Array.update_spec
  let* ⟨ i56, i56_post1, i56_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i57, i57_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s8, s8_post ⟩ ← Array.update_spec
  let* ⟨ i58, i58_post1, i58_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i59, i59_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s9, s9_post ⟩ ← Array.update_spec
  let* ⟨ i60, i60_post1, i60_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i61, i61_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s10, s10_post ⟩ ← Array.update_spec
  let* ⟨ i62, i62_post1, i62_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i63, i63_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s11, s11_post ⟩ ← Array.update_spec
  let* ⟨ i64, i64_post1, i64_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i65, i65_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s12, s12_post ⟩ ← Array.update_spec
  let* ⟨ i66, i66_post1, i66_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i67, i67_post ⟩ ← Array.index_usize_spec
  let* ⟨ i68, i68_post1, i68_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i69, i69_post1, i69_post2 ⟩ ← UScalar.or_spec
  let* ⟨ i70, i70_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s13, s13_post ⟩ ← Array.update_spec
  let* ⟨ i71, i71_post1, i71_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i72, i72_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s14, s14_post ⟩ ← Array.update_spec
  let* ⟨ i73, i73_post1, i73_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i74, i74_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s15, s15_post ⟩ ← Array.update_spec
  let* ⟨ i75, i75_post1, i75_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i76, i76_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s16, s16_post ⟩ ← Array.update_spec
  let* ⟨ i77, i77_post1, i77_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i78, i78_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s17, s17_post ⟩ ← Array.update_spec
  let* ⟨ i79, i79_post1, i79_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i80, i80_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s18, s18_post ⟩ ← Array.update_spec
  let* ⟨ i81, i81_post1, i81_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i82, i82_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s19, s19_post ⟩ ← Array.update_spec
  let* ⟨ i83, i83_post1, i83_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i84, i84_post ⟩ ← Array.index_usize_spec
  let* ⟨ i85, i85_post1, i85_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i86, i86_post1, i86_post2 ⟩ ← UScalar.or_spec
  let* ⟨ i87, i87_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s20, s20_post ⟩ ← Array.update_spec
  let* ⟨ i88, i88_post1, i88_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i89, i89_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s21, s21_post ⟩ ← Array.update_spec
  let* ⟨ i90, i90_post1, i90_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i91, i91_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s22, s22_post ⟩ ← Array.update_spec
  let* ⟨ i92, i92_post1, i92_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i93, i93_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s23, s23_post ⟩ ← Array.update_spec
  let* ⟨ i94, i94_post1, i94_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i95, i95_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s24, s24_post ⟩ ← Array.update_spec
  let* ⟨ i96, i96_post1, i96_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i97, i97_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s25, s25_post ⟩ ← Array.update_spec
  let* ⟨ i98, i98_post1, i98_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i99, i99_post ⟩ ← Array.index_usize_spec
  let* ⟨ i100, i100_post1, i100_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i101, i101_post1, i101_post2 ⟩ ← UScalar.or_spec
  let* ⟨ i102, i102_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s26, s26_post ⟩ ← Array.update_spec
  let* ⟨ i103, i103_post1, i103_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i104, i104_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s27, s27_post ⟩ ← Array.update_spec
  let* ⟨ i105, i105_post1, i105_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i106, i106_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s28, s28_post ⟩ ← Array.update_spec
  let* ⟨ i107, i107_post1, i107_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i108, i108_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s29, s29_post ⟩ ← Array.update_spec
  let* ⟨ i109, i109_post1, i109_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i110, i110_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s30, s30_post ⟩ ← Array.update_spec
  let* ⟨ i111, i111_post1, i111_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i112, i112_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s31, s31_post ⟩ ← Array.update_spec
  let* ⟨ i113, i113_post1, i113_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i114, i114_post ⟩ ← UScalar.cast.step_spec
  let* ⟨ s32, s32_post ⟩ ← Array.update_spec
  let* ⟨ i115, i115_post ⟩ ← Array.index_usize_spec
  let* ⟨ i116, i116_post1, i116_post2 ⟩ ← UScalar.and_spec
  let* ⟨ ⟩ ← massert_spec
  · -- Resolve array lookups to concrete variables
    have h99 : i99 = i38 := by simp only [i99_post, limbs9_post, Array.set_val_eq,
      UScalar.ofNatCore_val_eq, List.length_set, List.Vector.length_val, Nat.lt_add_one,
      getElem!_pos, List.getElem_set_self]
    have h115_eq : i115 = i114 := by simp only [i115_post, s32_post, Array.set_val_eq,
      UScalar.ofNatCore_val_eq, List.length_set, List.Vector.length_val, Nat.lt_add_one,
      getElem!_pos, List.getElem_set_self]
    -- Compute mask value: low_51_bit_mask = (1 <<< 51) - 1 = 2^51 - 1
    have hmask : low_51_bit_mask.val = 2^51 - 1 := by
      simp only [low_51_bit_mask_post1, i12_post1, U64.size, U64.numBits,
        UScalarTy.U64_numBits_eq]; norm_num; bv_normalize
    -- i38 < 2^51 via helper (clean context, no scanning 164 hypotheses)
    have h38 : i38.val < 2^51 := by
      rw [i38_post1]; exact and_mask_lt_pow i37 low_51_bit_mask hmask
    -- i113 = i99 >>> 44 = i38 >>> 44 < 128 (since i38 < 2^51)
    have h113 : i113.val < 128 := by
      rw [i113_post1, h99, Nat.shiftRight_eq_div_pow]; omega
    -- i114 = cast U8 i113, preserves value since < 128 < 256
    have h114_bound : i114.val < 128 := by
      simp only [i114_post, U64_cast_U8]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h113
    -- i116 = (i115 &&& 128) = (i114 &&& 128) = 0 via helper
    have h116_val : i116.val = 0 := by
      simp only [i116_post1, h115_eq]
      exact u8_and_128_eq_zero_of_lt i114 h114_bound
    exact UScalar.eq_of_val_eq h116_val
  -- Final goal: U8x32_as_Nat s32 ≡ Field51_as_Nat self [MOD p] ∧ U8x32_as_Nat s32 < p
  -- Mask value (reused from massert proof; re-derive for this goal)
  have hmask : low_51_bit_mask.val = 2^51 - 1 := by
    simp only [low_51_bit_mask_post1, i12_post1, U64.size, U64.numBits,
      UScalarTy.U64_numBits_eq]; norm_num; bv_normalize
  -- (A) Byte packing: U8x32_as_Nat s32 = Field51_as_Nat limbs9
  -- Array resolution: limbs9[0]!=i18, [1]!=i24, [2]!=i30, [3]!=i36, [4]!=i38
  have h_l0 : limbs9.val[0]! = i18 := by
    simp only [limbs9_post, limbs8_post, limbs7_post, limbs6_post, limbs5_post,
      limbs4_post, limbs3_post, limbs2_post, Array.set_val_eq,
      getElem!_pos, List.length_set, List.Vector.length_val,
      List.getElem_set_self, ne_eq, List.getElem_set_ne, UScalar.ofNatCore_val_eq,
      not_false_eq_true, one_ne_zero, OfNat.ofNat_ne_zero, Nat.ofNat_pos]
  have h_l1 : limbs9.val[1]! = i24 := by
    simp only [limbs9_post, limbs8_post, limbs7_post, limbs6_post, limbs5_post,
      limbs4_post, Array.set_val_eq,
      getElem!_pos, List.length_set, List.Vector.length_val,
      List.getElem_set_self, ne_eq, List.getElem_set_ne, UScalar.ofNatCore_val_eq,
      Nat.reduceLT, not_false_eq_true, OfNat.ofNat_ne_one]
  have h_l2 : limbs9.val[2]! = i30 := by
    simp only [limbs9_post, limbs8_post, limbs7_post, limbs6_post, Array.set_val_eq,
      getElem!_pos, List.length_set, List.Vector.length_val,
      List.getElem_set_self, ne_eq, List.getElem_set_ne, UScalar.ofNatCore_val_eq,
      Nat.reduceLT, not_false_eq_true, Nat.reduceEqDiff, Nat.succ_ne_self]
  have h_l3 : limbs9.val[3]! = i36 := by
    simp only [limbs9_post, limbs8_post, Array.set_val_eq,
      getElem!_pos, List.length_set, List.Vector.length_val,
      List.getElem_set_self, ne_eq, List.getElem_set_ne, UScalar.ofNatCore_val_eq,
      Nat.reduceLT, not_false_eq_true, Nat.succ_ne_self]
  have h_l4 : limbs9.val[4]! = i38 := by
    simp only [limbs9_post, Array.set_val_eq,
      getElem!_pos, List.length_set, List.Vector.length_val,
      List.getElem_set_self, UScalar.ofNatCore_val_eq, Nat.lt_add_one]
  have hlimbs : ∀ i < 5, (limbs9.val[i]! : U64).val < 2 ^ 51 := by
    intro i hi; interval_cases i
    · rw [h_l0, i18_post1]; exact and_mask_lt_pow i17 low_51_bit_mask hmask
    · rw [h_l1, i24_post1]; exact and_mask_lt_pow i23 low_51_bit_mask hmask
    · rw [h_l2, i30_post1]; exact and_mask_lt_pow i29 low_51_bit_mask hmask
    · rw [h_l3, i36_post1]; exact and_mask_lt_pow i35 low_51_bit_mask hmask
    · rw [h_l4, i38_post1]; exact and_mask_lt_pow i37 low_51_bit_mask hmask
  have hbytes : bytes_match_limbs limbs9 s32 := by
    unfold bytes_match_limbs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [
      Array.set_val_eq, getElem!_pos, List.length_set, List.Vector.length_val,
      List.getElem_set_self, List.getElem_set_ne, ne_eq, not_false_eq_true,
      UScalar.ofNatCore_val_eq, U64_cast_U8, UScalar.val_or,
      Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos,
      Nat.reduceEqDiff, Nat.succ_ne_self,
      one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, *]
  have hpack := byte_packing_eq limbs9 s32 hlimbs hbytes
  rw [hpack]
  -- (B) Canonical reduction in clean context
  clear *-
    fe_post1 fe_post2
    i_post i1_post q_post1 i2_post i3_post q1_post1
    i4_post i5_post q2_post1 i6_post i7_post q3_post1
    i8_post i9_post q4_post1
    i10_post i11_post limbs_post
    i12_post1 low_51_bit_mask_post1
    i13_post i14_post1 i15_post i16_post limbs1_post
    i17_post i18_post1 limbs2_post
    i19_post i20_post1 i21_post i22_post limbs3_post
    i23_post i24_post1 limbs4_post
    i25_post i26_post1 i27_post i28_post limbs5_post
    i29_post i30_post1 limbs6_post
    i31_post i32_post1 i33_post i34_post limbs7_post
    i35_post i36_post1 limbs8_post
    i37_post i38_post1 limbs9_post
  -- Mask value: &&&(2^51-1) → %2^51 conversion for hl proofs
  have hmask : low_51_bit_mask.val = 2 ^ 51 - 1 := by
    simp only [low_51_bit_mask_post1, i12_post1, U64.size, U64.numBits,
      UScalarTy.U64_numBits_eq]; norm_num; bv_normalize
  -- Remove raw mask hypotheses that conflict with hmask in simp's `*`
  -- (both rewrite low_51_bit_mask.val; hmask gives symbolic 2^51-1, they give concrete junk)
  clear low_51_bit_mask_post1 i12_post1
  -- Apply the standalone canonical reduction lemma.
  have hcanon := canonical_reduction_mod_p
    fe[0]!.val fe[1]!.val fe[2]!.val fe[3]!.val fe[4]!.val
    (fe_post1 0 (by omega)) (fe_post1 1 (by omega)) (fe_post1 2 (by omega))
    (fe_post1 3 (by omega)) (fe_post1 4 (by omega))
    q4.val
    (by -- hq: q4.val = q-chain formula
      simp only [q4_post1, i9_post, q3_post1, i7_post, q2_post1, i5_post,
        q1_post1, i3_post, q_post1, i1_post, i_post,
        i8_post, i6_post, i4_post, i2_post,
        Nat.shiftRight_eq_div_pow]; agrind)
    limbs9[0]!.val limbs9[1]!.val limbs9[2]!.val limbs9[3]!.val limbs9[4]!.val
    -- hl0..hl4: each resolves a limb's carry chain (array updates → &&&→% via hmask, >>>→/)
    (by simp only [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.ofNatCore_val_eq,
    List.length_set, List.Vector.length_val, getElem!_pos, ne_eq, not_false_eq_true,
    List.getElem_set_ne, List.getElem_set_self, UScalar.val_and, Nat.shiftRight_eq_div_pow,
    Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos, one_ne_zero, OfNat.ofNat_ne_zero,
    land_pow_two_sub_one_eq_mod, *])
    (by simp only [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.ofNatCore_val_eq,
    List.length_set, List.Vector.length_val, getElem!_pos, ne_eq, not_false_eq_true,
    List.getElem_set_ne, List.getElem_set_self, UScalar.val_and, Nat.shiftRight_eq_div_pow,
    Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos, zero_ne_one, OfNat.ofNat_ne_one,
    land_pow_two_sub_one_eq_mod, *])
    (by simp only [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.ofNatCore_val_eq,
    List.length_set, List.Vector.length_val, getElem!_pos, ne_eq, not_false_eq_true,
    List.getElem_set_ne, List.getElem_set_self, UScalar.val_and, Nat.shiftRight_eq_div_pow,
    Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos, Nat.reduceEqDiff,
    Nat.succ_ne_self, zero_ne_one, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat,
    land_pow_two_sub_one_eq_mod, *])
    (by simp only [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.ofNatCore_val_eq,
    List.length_set, List.Vector.length_val, getElem!_pos, ne_eq, not_false_eq_true,
    List.getElem_set_ne, List.getElem_set_self, UScalar.val_and, Nat.shiftRight_eq_div_pow,
    Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos, Nat.reduceEqDiff,
    Nat.succ_ne_self, zero_ne_one, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat,
    land_pow_two_sub_one_eq_mod, *])
    (by simp only [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.ofNatCore_val_eq,
    List.length_set, List.Vector.length_val, getElem!_pos, ne_eq, not_false_eq_true,
    List.getElem_set_ne, List.getElem_set_self, UScalar.val_and, Nat.shiftRight_eq_div_pow,
    Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos, Nat.reduceEqDiff, zero_ne_one,
    OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat, land_pow_two_sub_one_eq_mod, *])
  -- Unfold Field51_as_Nat/p/ModEq everywhere so hcanon (explicit sums) and
  -- fe_post2 (Field51_as_Nat) are in the same form. Then omega chains them.
  obtain ⟨hmod, hlt⟩ := hcanon
  constructor
  · simp only [Nat.ModEq, Field51_as_Nat, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, p, Nat.reduceMul, zero_add, Array.getElem!_Nat_eq] at *
    omega
  · simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, p, Nat.reduceMul, zero_add, Array.getElem!_Nat_eq] at *
    omega

end curve25519_dalek.backend.serial.u64.field.FieldElement51
