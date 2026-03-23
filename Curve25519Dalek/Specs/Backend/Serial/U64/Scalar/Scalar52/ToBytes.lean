/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.BitList
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorem for `Scalar52::to_bytes`

Specification and proof for `Scalar52::to_bytes`.

This function converts the structure to its byte representation.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## Rust Source

```rust
/// Pack the limbs of this `Scalar52` into 32 bytes
pub fn to_bytes(self) -> [u8; 32] {
    let mut s = [0u8; 32];

    s[ 0] =  (self.0[ 0] >>  0)                      as u8;
    s[ 1] =  (self.0[ 0] >>  8)                      as u8;
    s[ 2] =  (self.0[ 0] >> 16)                      as u8;
    s[ 3] =  (self.0[ 0] >> 24)                      as u8;
    s[ 4] =  (self.0[ 0] >> 32)                      as u8;
    s[ 5] =  (self.0[ 0] >> 40)                      as u8;
    s[ 6] = ((self.0[ 0] >> 48) | (self.0[ 1] << 4)) as u8;
    s[ 7] =  (self.0[ 1] >>  4)                      as u8;
    s[ 8] =  (self.0[ 1] >> 12)                      as u8;
    s[ 9] =  (self.0[ 1] >> 20)                      as u8;
    s[10] =  (self.0[ 1] >> 28)                      as u8;
    s[11] =  (self.0[ 1] >> 36)                      as u8;
    s[12] =  (self.0[ 1] >> 44)                      as u8;
    s[13] =  (self.0[ 2] >>  0)                      as u8;
    s[14] =  (self.0[ 2] >>  8)                      as u8;
    s[15] =  (self.0[ 2] >> 16)                      as u8;
    s[16] =  (self.0[ 2] >> 24)                      as u8;
    s[17] =  (self.0[ 2] >> 32)                      as u8;
    s[18] =  (self.0[ 2] >> 40)                      as u8;
    s[19] = ((self.0[ 2] >> 48) | (self.0[ 3] << 4)) as u8;
    s[20] =  (self.0[ 3] >>  4)                      as u8;
    s[21] =  (self.0[ 3] >> 12)                      as u8;
    s[22] =  (self.0[ 3] >> 20)                      as u8;
    s[23] =  (self.0[ 3] >> 28)                      as u8;
    s[24] =  (self.0[ 3] >> 36)                      as u8;
    s[25] =  (self.0[ 3] >> 44)                      as u8;
    s[26] =  (self.0[ 4] >>  0)                      as u8;
    s[27] =  (self.0[ 4] >>  8)                      as u8;
    s[28] =  (self.0[ 4] >> 16)                      as u8;
    s[29] =  (self.0[ 4] >> 24)                      as u8;
    s[30] =  (self.0[ 4] >> 32)                      as u8;
    s[31] =  (self.0[ 4] >> 40)                      as u8;

    s
}
```

## Bit layout

Each limb holds 52 bits. Since 52 = 6×8 + 4, each limb fills 6 full bytes plus 4 bits that
spill into a shared byte with the adjacent limb. The two shared bytes are s[6] and s[19],
constructed via OR of the overflow bits from one limb and the start bits of the next.

  | Limb | Bits  | Bytes                              | Shared |
  |------|-------|------------------------------------|--------|
  |  0   | 0–51  | s[0]–s[5], lower nibble of s[6]    | s[6]   |
  |  1   | 0–51  | upper nibble of s[6], s[7]–s[12]   | s[6]   |
  |  2   | 0–51  | s[13]–s[18], lower nibble of s[19] | s[19]  |
  |  3   | 0–51  | upper nibble of s[19], s[20]–s[25] | s[19]  |
  |  4   | 0–47  | s[26]–s[31] (48 bits)              | none   |

Limb 4 uses only 48 of its 52 bits because the precondition `Scalar52_as_Nat self < L < 2^253`
implies `self[4] < 2^(253−208) = 2^45 < 2^48`.

Total: limbs hold 5×52 = 260 bits, but the value fits in 32×8 = 256 bits.

## Proof overview

We prove 5 results, one for each limb, describing the rows of the above table in terms of `BitList`.


-/

set_option linter.style.setOption false
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52
open List BitList
attribute [local simp] Array.length_eq

-- Note: this is a strengthening of `Scalar52_top_limb_lt_of_as_Nat_lt` in Aux.lean (which gives
-- < 2^51 from < 2^259). This tighter bound should be moved to the central location.
/-- If `Scalar52_as_Nat a < L`, then the top limb `a[4]` is bounded by `2^45`.
This follows because `2^208 * a[4] ≤ Scalar52_as_Nat a < L < 2^253`. -/
theorem Scalar52_top_limb_lt_of_canonical (a : Array U64 5#usize) (h : Scalar52_as_Nat a < L) :
  a[4].val < 2 ^ 45 := by
  unfold Scalar52_as_Nat at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  have : L < 2 ^ 253 := by unfold L; omega
  grind

/-- Two bit lists of the same length with the same `toNat` value are equal. -/
theorem eq_of_toNat_eq_of_length_eq (bs₁ bs₂ : List Bool)
    (h : toNat bs₁ = toNat bs₂) (hl : bs₁.length = bs₂.length) : bs₁ = bs₂ := by
  conv_lhs => rw [← ofNat_toNat bs₁]
  conv_rhs => rw [← ofNat_toNat bs₂]
  rw [hl, h]

/-- Two bit lists of the same length with the same `toNat` value are Equiv. -/
theorem Equiv.of_toNat_eq_of_length_eq (bs₁ bs₂ : List Bool)
    (h : toNat bs₁ = toNat bs₂) (hl : bs₁.length = bs₂.length) : bs₁ ≈ₗ bs₂ := by
  rw [eq_of_toNat_eq_of_length_eq bs₁ bs₂ h hl]

/-- At a shared byte (s[6] or s[19]), the lower and upper nibble contributions recombine:
    `(x % 2^4) * 2^a + (x / 2^4) * 2^(a+4) = x * 2^a`. -/
theorem shared_byte_recombine (x a : Nat) :
    (x % 2 ^ 4) * 2 ^ a + (x / 2 ^ 4) * 2 ^ (a + 4) = x * 2 ^ a := by
  conv_lhs => rw [show (2 : Nat) ^ (a + 4) = 2 ^ 4 * 2 ^ a from by ring]
  have : x / 2 ^ 4 * (2 ^ 4 * 2 ^ a) = x / 2 ^ 4 * 2 ^ 4 * 2 ^ a := by ring
  rw [this, ← Nat.add_mul]
  congr 1; omega

/-- Casting a right-shifted U64 to U8 gives the corresponding 8-bit slice as a BitList.
    Given `z.val = x.val / 2^k % 2^8` (which holds after shift-right by k then cast to U8),
    we get `ofU8 z = ((ofU64 x).drop k).take 8`. -/
theorem ofU8_val_eq_ofU64_drop_take (z : U8) (x : U64) (k : Nat)
    (hk : k + 8 ≤ 64) (hval : z.val = x.val / 2 ^ k % 2 ^ 8) :
    ofU8 z = ((ofU64 x).drop k).take 8 := by
  show ofNat 8 z.val = ((ofNat 64 x.val).drop k).take 8
  rw [hval, ofNat_mod, ofNat_drop k 64 x.val (by omega), ofNat_take 8 (64 - k) _ (by omega)]

/-- Bridge from 32 byte-level BitList equalities to the Nat-level equality
    `U8x32_as_Nat result = Scalar52_as_Nat self`.
    Each simple byte hypothesis states that the byte equals an 8-bit slice of the corresponding limb.
    Shared bytes 6 and 19 each carry 4 bits from two adjacent limbs. -/
theorem scalar52_eq_of_bitList_bytes
    (self : Scalar52) (result : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h4_bound : self[4].val < 2 ^ 48)
    -- Limb 0 → bytes 0–5
    (hb0  : ofU8 result[0]!  = ((ofU64 self[0]).drop  0).take 8)
    (hb1  : ofU8 result[1]!  = ((ofU64 self[0]).drop  8).take 8)
    (hb2  : ofU8 result[2]!  = ((ofU64 self[0]).drop 16).take 8)
    (hb3  : ofU8 result[3]!  = ((ofU64 self[0]).drop 24).take 8)
    (hb4  : ofU8 result[4]!  = ((ofU64 self[0]).drop 32).take 8)
    (hb5  : ofU8 result[5]!  = ((ofU64 self[0]).drop 40).take 8)
    -- Shared byte 6 (4 bits from limb 0 top + 4 bits from limb 1 bottom)
    (hb6  : ofU8 result[6]!  = ((ofU64 self[0]).drop 48).take 4 ++
                                ((ofU64 self[1]).drop  0).take 4)
    -- Limb 1 → bytes 7–12
    (hb7  : ofU8 result[7]!  = ((ofU64 self[1]).drop  4).take 8)
    (hb8  : ofU8 result[8]!  = ((ofU64 self[1]).drop 12).take 8)
    (hb9  : ofU8 result[9]!  = ((ofU64 self[1]).drop 20).take 8)
    (hb10 : ofU8 result[10]! = ((ofU64 self[1]).drop 28).take 8)
    (hb11 : ofU8 result[11]! = ((ofU64 self[1]).drop 36).take 8)
    (hb12 : ofU8 result[12]! = ((ofU64 self[1]).drop 44).take 8)
    -- Limb 2 → bytes 13–18
    (hb13 : ofU8 result[13]! = ((ofU64 self[2]).drop  0).take 8)
    (hb14 : ofU8 result[14]! = ((ofU64 self[2]).drop  8).take 8)
    (hb15 : ofU8 result[15]! = ((ofU64 self[2]).drop 16).take 8)
    (hb16 : ofU8 result[16]! = ((ofU64 self[2]).drop 24).take 8)
    (hb17 : ofU8 result[17]! = ((ofU64 self[2]).drop 32).take 8)
    (hb18 : ofU8 result[18]! = ((ofU64 self[2]).drop 40).take 8)
    -- Shared byte 19 (4 bits from limb 2 top + 4 bits from limb 3 bottom)
    (hb19 : ofU8 result[19]! = ((ofU64 self[2]).drop 48).take 4 ++
                                ((ofU64 self[3]).drop  0).take 4)
    -- Limb 3 → bytes 20–25
    (hb20 : ofU8 result[20]! = ((ofU64 self[3]).drop  4).take 8)
    (hb21 : ofU8 result[21]! = ((ofU64 self[3]).drop 12).take 8)
    (hb22 : ofU8 result[22]! = ((ofU64 self[3]).drop 20).take 8)
    (hb23 : ofU8 result[23]! = ((ofU64 self[3]).drop 28).take 8)
    (hb24 : ofU8 result[24]! = ((ofU64 self[3]).drop 36).take 8)
    (hb25 : ofU8 result[25]! = ((ofU64 self[3]).drop 44).take 8)
    -- Limb 4 → bytes 26–31 (48 bits, no shared byte)
    (hb26 : ofU8 result[26]! = ((ofU64 self[4]).drop  0).take 8)
    (hb27 : ofU8 result[27]! = ((ofU64 self[4]).drop  8).take 8)
    (hb28 : ofU8 result[28]! = ((ofU64 self[4]).drop 16).take 8)
    (hb29 : ofU8 result[29]! = ((ofU64 self[4]).drop 24).take 8)
    (hb30 : ofU8 result[30]! = ((ofU64 self[4]).drop 32).take 8)
    (hb31 : ofU8 result[31]! = ((ofU64 self[4]).drop 40).take 8) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
  -- Phase 1: Convert each BitList equality to a Nat identity via congr_arg toNat
  replace hb0  := congr_arg toNat hb0
  replace hb1  := congr_arg toNat hb1
  replace hb2  := congr_arg toNat hb2
  replace hb3  := congr_arg toNat hb3
  replace hb4  := congr_arg toNat hb4
  replace hb5  := congr_arg toNat hb5
  replace hb6  := congr_arg toNat hb6
  replace hb7  := congr_arg toNat hb7
  replace hb8  := congr_arg toNat hb8
  replace hb9  := congr_arg toNat hb9
  replace hb10 := congr_arg toNat hb10
  replace hb11 := congr_arg toNat hb11
  replace hb12 := congr_arg toNat hb12
  replace hb13 := congr_arg toNat hb13
  replace hb14 := congr_arg toNat hb14
  replace hb15 := congr_arg toNat hb15
  replace hb16 := congr_arg toNat hb16
  replace hb17 := congr_arg toNat hb17
  replace hb18 := congr_arg toNat hb18
  replace hb19 := congr_arg toNat hb19
  replace hb20 := congr_arg toNat hb20
  replace hb21 := congr_arg toNat hb21
  replace hb22 := congr_arg toNat hb22
  replace hb23 := congr_arg toNat hb23
  replace hb24 := congr_arg toNat hb24
  replace hb25 := congr_arg toNat hb25
  replace hb26 := congr_arg toNat hb26
  replace hb27 := congr_arg toNat hb27
  replace hb28 := congr_arg toNat hb28
  replace hb29 := congr_arg toNat hb29
  replace hb30 := congr_arg toNat hb30
  replace hb31 := congr_arg toNat hb31
  -- Phase 2: Expand toNat of BitList operations to Nat arithmetic
  -- Avoid Nat.reducePow to prevent computing huge numbers like 2^208
  simp only [toNat_take, toNat_drop, toNat_append, toNat_ofU8, toNat_ofU64,
    ofU8_length, ofU64_length, length_take, length_drop, length_append, ofNat_length,
    Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Nat.min_def, Nat.reduceLT, ite_true,
    Nat.pow_zero, Nat.div_one] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hb16 hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb24 hb25 hb26 hb27 hb28 hb29 hb30 hb31
  -- Phase 3: Expand both Nat sums (keep 2^k symbolic)
  unfold U8x32_as_Nat Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reduceMul, one_mul, Nat.pow_zero]
  -- Phase 4: Normalize getElem! to getElem so all indexing is consistent
  have hls : self.val.length = 5 := self.property
  have hlr : result.val.length = 32 := result.property
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem, Option.getD_some, hls, hlr, Nat.reduceLT] at *
  -- Phase 5: Substitute byte values into the goal and close with omega
  -- Each hbN says result[N].val = self[L].val / 2^K % 2^8 (or similar for shared bytes)
  simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9,
    hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19,
    hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29, hb30, hb31]
  sorry

/-
/-- Bridge from 5 BitList limb equivalences to the Nat-level equality
    `U8x32_as_Nat result = Scalar52_as_Nat self`. -/
theorem scalar52_eq_of_bitList_limbs
    (self : Scalar52) (result : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i : Fin 5, self[i].val < 2 ^ 52)
    (h4_bound : self[4].val < 2 ^ 48)
    (hlimb0 : (ofU64 self[0]).take 52 ≈ₗ
        ofU8 result[0]! ++ ofU8 result[1]! ++ ofU8 result[2]! ++
        ofU8 result[3]! ++ ofU8 result[4]! ++ ofU8 result[5]! ++
        (ofU8 result[6]!).take 4)
    (hlimb1 : (ofU64 self[1]).take 52 ≈ₗ
        (ofU8 result[6]!).drop 4 ++
        ofU8 result[7]! ++ ofU8 result[8]! ++ ofU8 result[9]! ++
        ofU8 result[10]! ++ ofU8 result[11]! ++ ofU8 result[12]!)
    (hlimb2 : (ofU64 self[2]).take 52 ≈ₗ
        ofU8 result[13]! ++ ofU8 result[14]! ++ ofU8 result[15]! ++
        ofU8 result[16]! ++ ofU8 result[17]! ++ ofU8 result[18]! ++
        (ofU8 result[19]!).take 4)
    (hlimb3 : (ofU64 self[3]).take 52 ≈ₗ
        (ofU8 result[19]!).drop 4 ++
        ofU8 result[20]! ++ ofU8 result[21]! ++ ofU8 result[22]! ++
        ofU8 result[23]! ++ ofU8 result[24]! ++ ofU8 result[25]!)
    (hlimb4 : (ofU64 self[4]).take 48 ≈ₗ
        ofU8 result[26]! ++ ofU8 result[27]! ++ ofU8 result[28]! ++
        ofU8 result[29]! ++ ofU8 result[30]! ++ ofU8 result[31]!) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
  -- Convert each BitList equivalence to a Nat identity
  have h0 := hlimb0.toNat_eq
  have h1 := hlimb1.toNat_eq
  have h2 := hlimb2.toNat_eq
  have h3 := hlimb3.toNat_eq
  have h4 := hlimb4.toNat_eq
  -- Phase 1: Expand toNat of bit list operations
  simp only [toNat_take, toNat_drop, toNat_append, toNat_ofU8, toNat_ofU64, ofU8_length,
    length_drop, length_append, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd] at h0 h1 h2 h3 h4
  -- Expand both Nat sums
  unfold U8x32_as_Nat Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reducePow, Nat.reduceMul, one_mul]
  -- Provide limb bounds for omega and recombine shared bytes
  have hb0 : self[0].val < 2 ^ 52 := h ⟨0, by omega⟩
  have hb1 : self[1].val < 2 ^ 52 := h ⟨1, by omega⟩
  have hb2 : self[2].val < 2 ^ 52 := h ⟨2, by omega⟩
  have hb3 : self[3].val < 2 ^ 52 := h ⟨3, by omega⟩
  have hb6 := shared_byte_recombine result[6]!.val 48
  have hb19 := shared_byte_recombine result[19]!.val 152
  -- Normalize all getElem! to getElem so self[i]! (from Scalar52_as_Nat) and
  -- self[i] (from hlimb hypotheses) become the same term.
  -- Aeneas disables List.getElem!_eq_getElem?_getD, so we must apply it explicitly.
  -- We provide explicit length facts so simp can discharge getElem? side conditions.
  have hls : self.val.length = 5 := self.property
  have hlr : result.val.length = 32 := result.property
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem, Option.getD_some, hls, hlr, Nat.reduceLT] at *
  grind
-/

/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
@[progress]
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧ U8x32_as_Nat result < L ⦄ := by
    unfold to_bytes
    simp only [progress_simps]
    let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
    let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i2, i2_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s1, s1_post ⟩ ← Array.update_spec
    let* ⟨ i3, i3_post1, i3_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i4, i4_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s2, s2_post ⟩ ← Array.update_spec
    let* ⟨ i5, i5_post1, i5_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i6, i6_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s3, s3_post ⟩ ← Array.update_spec
    let* ⟨ i7, i7_post1, i7_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i8, i8_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s4, s4_post ⟩ ← Array.update_spec
    let* ⟨ i9, i9_post1, i9_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i10, i10_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s5, s5_post ⟩ ← Array.update_spec
    let* ⟨ i11, i11_post1, i11_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i12, i12_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s6, s6_post ⟩ ← Array.update_spec
    let* ⟨ i13, i13_post1, i13_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
    let* ⟨ i15, i15_post1, i15_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i16, i16_post1, i16_post2 ⟩ ← UScalar.or_spec
    let* ⟨ i17, i17_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s7, s7_post ⟩ ← Array.update_spec
    let* ⟨ i18, i18_post1, i18_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i19, i19_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s8, s8_post ⟩ ← Array.update_spec
    let* ⟨ i20, i20_post1, i20_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i21, i21_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s9, s9_post ⟩ ← Array.update_spec
    let* ⟨ i22, i22_post1, i22_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i23, i23_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s10, s10_post ⟩ ← Array.update_spec
    let* ⟨ i24, i24_post1, i24_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i25, i25_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s11, s11_post ⟩ ← Array.update_spec
    let* ⟨ i26, i26_post1, i26_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i27, i27_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s12, s12_post ⟩ ← Array.update_spec
    let* ⟨ i28, i28_post1, i28_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i29, i29_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s13, s13_post ⟩ ← Array.update_spec
    let* ⟨ i30, i30_post ⟩ ← Array.index_usize_spec
    let* ⟨ i31, i31_post1, i31_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i32, i32_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s14, s14_post ⟩ ← Array.update_spec
    let* ⟨ i33, i33_post1, i33_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i34, i34_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s15, s15_post ⟩ ← Array.update_spec
    let* ⟨ i35, i35_post1, i35_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i36, i36_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s16, s16_post ⟩ ← Array.update_spec
    let* ⟨ i37, i37_post1, i37_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i38, i38_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s17, s17_post ⟩ ← Array.update_spec
    let* ⟨ i39, i39_post1, i39_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i40, i40_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s18, s18_post ⟩ ← Array.update_spec
    let* ⟨ i41, i41_post1, i41_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i42, i42_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s19, s19_post ⟩ ← Array.update_spec
    let* ⟨ i43, i43_post1, i43_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i44, i44_post ⟩ ← Array.index_usize_spec
    let* ⟨ i45, i45_post1, i45_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i46, i46_post1, i46_post2 ⟩ ← UScalar.or_spec
    let* ⟨ i47, i47_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s20, s20_post ⟩ ← Array.update_spec
    let* ⟨ i48, i48_post1, i48_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i49, i49_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s21, s21_post ⟩ ← Array.update_spec
    let* ⟨ i50, i50_post1, i50_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i51, i51_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s22, s22_post ⟩ ← Array.update_spec
    let* ⟨ i52, i52_post1, i52_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i53, i53_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s23, s23_post ⟩ ← Array.update_spec
    let* ⟨ i54, i54_post1, i54_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i55, i55_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s24, s24_post ⟩ ← Array.update_spec
    let* ⟨ i56, i56_post1, i56_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i57, i57_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s25, s25_post ⟩ ← Array.update_spec
    let* ⟨ i58, i58_post1, i58_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i59, i59_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s26, s26_post ⟩ ← Array.update_spec
    let* ⟨ i60, i60_post ⟩ ← Array.index_usize_spec
    let* ⟨ i61, i61_post1, i61_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i62, i62_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s27, s27_post ⟩ ← Array.update_spec
    let* ⟨ i63, i63_post1, i63_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i64, i64_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s28, s28_post ⟩ ← Array.update_spec
    let* ⟨ i65, i65_post1, i65_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i66, i66_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s29, s29_post ⟩ ← Array.update_spec
    let* ⟨ i67, i67_post1, i67_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i68, i68_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s30, s30_post ⟩ ← Array.update_spec
    let* ⟨ i69, i69_post1, i69_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i70, i70_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ s31, s31_post ⟩ ← Array.update_spec
    let* ⟨ i71, i71_post1, i71_post2 ⟩ ← U64.ShiftRight_IScalar_spec
    let* ⟨ i72, i72_post ⟩ ← UScalar.cast.progress_spec
    let* ⟨ result, result_post ⟩ ← Array.update_spec

    -- Byte-level BitList statements: each byte equals an 8-bit slice of the corresponding limb.
    -- Simple bytes use: subst_vars → simp set chain → ofU8_val_eq_ofU64_drop_take → cast_val_eq
    -- → shift postcondition → getElem! normalization → congr.
    -- Shared bytes (6, 19) are proved separately.

    -- Limb 0 → bytes 0–5
    have hbyte0 : ofU8 result[0]! = ((ofU64 self[0]).drop 0).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 0 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i1_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT, Nat.pow_zero, Nat.div_one]; congr 1
    have hbyte1 : ofU8 result[1]! = ((ofU64 self[0]).drop 8).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 8 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i3_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte2 : ofU8 result[2]! = ((ofU64 self[0]).drop 16).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 16 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i5_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte3 : ofU8 result[3]! = ((ofU64 self[0]).drop 24).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 24 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i7_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte4 : ofU8 result[4]! = ((ofU64 self[0]).drop 32).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 32 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i9_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte5 : ofU8 result[5]! = ((ofU64 self[0]).drop 40).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 40 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i11_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    -- Shared byte 6: ((self[0] >> 48) | (self[1] << 4)) as u8
    have hbyte6 : ofU8 result[6]! = ((ofU64 self[0]).drop 48).take 4 ++
                                      ((ofU64 self[1]).drop 0).take 4 := by
      sorry
    -- Limb 1 → bytes 7–12
    have hbyte7 : ofU8 result[7]! = ((ofU64 self[1]).drop 4).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 4 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i18_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte8 : ofU8 result[8]! = ((ofU64 self[1]).drop 12).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 12 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i20_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte9 : ofU8 result[9]! = ((ofU64 self[1]).drop 20).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 20 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i22_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte10 : ofU8 result[10]! = ((ofU64 self[1]).drop 28).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 28 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i24_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte11 : ofU8 result[11]! = ((ofU64 self[1]).drop 36).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 36 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i26_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte12 : ofU8 result[12]! = ((ofU64 self[1]).drop 44).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 44 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i28_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    -- Limb 2 → bytes 13–18
    have hbyte13 : ofU8 result[13]! = ((ofU64 self[2]).drop 0).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 0 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i31_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT, Nat.pow_zero, Nat.div_one]; congr 1
    have hbyte14 : ofU8 result[14]! = ((ofU64 self[2]).drop 8).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 8 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i33_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte15 : ofU8 result[15]! = ((ofU64 self[2]).drop 16).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 16 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i35_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte16 : ofU8 result[16]! = ((ofU64 self[2]).drop 24).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 24 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i37_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte17 : ofU8 result[17]! = ((ofU64 self[2]).drop 32).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 32 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i39_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte18 : ofU8 result[18]! = ((ofU64 self[2]).drop 40).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 40 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i41_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    -- Shared byte 19: ((self[2] >> 48) | (self[3] << 4)) as u8
    have hbyte19 : ofU8 result[19]! = ((ofU64 self[2]).drop 48).take 4 ++
                                        ((ofU64 self[3]).drop 0).take 4 := by
      sorry
    -- Limb 3 → bytes 20–25
    have hbyte20 : ofU8 result[20]! = ((ofU64 self[3]).drop 4).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 4 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i48_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte21 : ofU8 result[21]! = ((ofU64 self[3]).drop 12).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 12 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i50_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte22 : ofU8 result[22]! = ((ofU64 self[3]).drop 20).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 20 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i52_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte23 : ofU8 result[23]! = ((ofU64 self[3]).drop 28).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 28 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i54_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte24 : ofU8 result[24]! = ((ofU64 self[3]).drop 36).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 36 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i56_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte25 : ofU8 result[25]! = ((ofU64 self[3]).drop 44).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 44 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i58_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    -- Limb 4 → bytes 26–31
    have hbyte26 : ofU8 result[26]! = ((ofU64 self[4]).drop 0).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 0 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i61_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT, Nat.pow_zero, Nat.div_one]; congr 1
    have hbyte27 : ofU8 result[27]! = ((ofU64 self[4]).drop 8).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 8 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i63_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte28 : ofU8 result[28]! = ((ofU64 self[4]).drop 16).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 16 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i65_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte29 : ofU8 result[29]! = ((ofU64 self[4]).drop 24).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 24 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i67_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte30 : ofU8 result[30]! = ((ofU64 self[4]).drop 32).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 32 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i69_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1
    have hbyte31 : ofU8 result[31]! = ((ofU64 self[4]).drop 40).take 8 := by
      subst_vars; simp only [Array.getElem!_Nat_eq, Array.set_val_eq]; simp_lists
      apply ofU8_val_eq_ofU64_drop_take _ _ 40 (by omega)
      simp only [UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
      rw [i71_post1, Nat.shiftRight_eq_div_pow]
      have hlen : (↑self : List U64).length = 5 := self.property
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some,
        hlen, Nat.reduceLT]; congr 1

    have : U8x32_as_Nat result = Scalar52_as_Nat self :=
      scalar52_eq_of_bitList_bytes self result h
        (by have := Scalar52_top_limb_lt_of_canonical self h'; omega)
        hbyte0 hbyte1 hbyte2 hbyte3 hbyte4 hbyte5 hbyte6
        hbyte7 hbyte8 hbyte9 hbyte10 hbyte11 hbyte12
        hbyte13 hbyte14 hbyte15 hbyte16 hbyte17 hbyte18 hbyte19
        hbyte20 hbyte21 hbyte22 hbyte23 hbyte24 hbyte25
        hbyte26 hbyte27 hbyte28 hbyte29 hbyte30 hbyte31
    refine ⟨this, ?_⟩
    rw [this]
    exact h'

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
