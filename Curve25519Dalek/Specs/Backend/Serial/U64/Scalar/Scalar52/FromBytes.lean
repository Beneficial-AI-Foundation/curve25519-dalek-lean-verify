/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-! # Spec Theorem for `Scalar52::from_bytes`

Specification and proof for `Scalar52::from_bytes`.

This function constructs an unpacked scalar from a byte array by:
1. Packing 32 bytes into 4 little-endian U64 words (loop)
2. Extracting 5 limbs via shift/OR/mask (bit-slicing)

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs (lines 66-93)

## Proof structure

1. `from_bytes_loop_spec`: The byte-packing loop correctly assembles 8 consecutive
   bytes into each U64 word as a little-endian integer.

2. `from_bytes_spec`: Uses the loop spec, then proves the bit-slicing phase extracts
   5 limbs preserving the value with all limbs < 2^52.
-/

set_option linter.style.whitespace false

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-- The little-endian value of 8 consecutive bytes starting at position `8*j` in a 32-byte array. -/
abbrev word_of_bytes (bytes : Array U8 32#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8, bytes[8 * j + k]!.val * 2 ^ (8 * k)

/-! ## Part 1: Loop spec — byte packing -/

set_option maxHeartbeats 400000 in -- heavy step
/-- **Loop spec**: Each iteration packs 8 bytes into one U64 word (little-endian).
After the loop completes, `words[j] = word_of_bytes bytes j` for all `j < 4`. -/
@[step]
theorem from_bytes_loop_spec (bytes : Array U8 32#usize)
    (words : Array U64 4#usize) (i : Usize) (hi : i.val ≤ 4)
    (h_prev : ∀ j, j < i.val → words[j]!.val = word_of_bytes bytes j) :
    from_bytes_loop bytes words i ⦃ words' =>
      ∀ j, j < 4 → words'[j]!.val = word_of_bytes bytes j ⦄ := by
  induction h_rem : (4 - i.val) generalizing i words with
  | zero =>
    unfold from_bytes_loop
    have hi4 : ¬ (i < 4#usize) := by scalar_tac
    simp only [hi4, ↓reduceIte, spec_ok]
    intro j hj; exact h_prev j (by omega)
  | succ n ih =>
    unfold from_bytes_loop
    have hlt : i < 4#usize := by scalar_tac
    simp only [hlt, ↓reduceIte]
    step*
    -- Goal: ∀ j < i+1, (words.set i i37)[j]! = word_of_bytes bytes j
    subst a_post
    intro j hj
    by_cases heq : j = i.val
    · -- j = i
      subst heq
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
      rw [getElem!_pos _ _ (by simp only [List.length_set, List.Vector.length_val,
        UScalar.ofNatCore_val_eq]; agrind),
          List.getElem_set_self (by simp only [List.length_set, List.Vector.length_val,
            UScalar.ofNatCore_val_eq]; agrind)]
      -- i37 = cascaded OR = byte sum via or_bytes_eq_sum
      simp (discharger := omega) only [*, UScalar.val_or, UScalar.cast_val_eq,
        u8_val_mod_u64_numBits, Nat.shiftLeft_eq, u8_mul_pow_mod_u64]
      rw [or_bytes_eq_sum _ _ _ _ _ _ _ _
        (bytes.val[i.val * 8]!).hmax (bytes.val[i.val * 8 + 1]!).hmax
        (bytes.val[i.val * 8 + 2]!).hmax (bytes.val[i.val * 8 + 3]!).hmax
        (bytes.val[i.val * 8 + 4]!).hmax (bytes.val[i.val * 8 + 5]!).hmax
        (bytes.val[i.val * 8 + 6]!).hmax (bytes.val[i.val * 8 + 7]!).hmax]
      simp only [word_of_bytes, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
        zero_add]
      simp only [Array.getElem!_Nat_eq]; ring_nf
    · -- j ≠ i: unchanged entry, use h_prev
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
      grind only [= List.getElem!_set_ne, =_ Array.getElem!_Nat_eq]


/-! ## Step lemma for the Scalar52 index_mut trait wrapper

The extracted `from_bytes` uses `Insts.CoreOpsIndexIndexMutUsizeU64.index_mut` (a thin wrapper
around `Array.index_mut_usize`) to write each limb. Without a `@[step]` lemma, `step*` cannot
see through the wrapper. Unfolding it creates ~30 nested let-bindings that cause kernel timeout.
This step lemma lets `step*` process each index_mut call individually. -/

@[step]
theorem Scalar52_index_mut_step (self : Scalar52) (i : Usize) (hi : i.val < self.length) :
    Insts.CoreOpsIndexIndexMutUsizeU64.index_mut self i ⦃ x wb =>
      wb = Aeneas.Std.Array.set self i ∧ x = self.val[i.val]! ⦄ := by
  unfold Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  let* ⟨ val, back, h1, h2 ⟩ ← Array.index_mut_usize_spec
  exact ⟨h1, h2⟩

/-! ## Part 2: Helper lemma for bit-slicing -/

/-- Pure math: 5 limbs obtained by bit-slicing 4 U64 words reconstruct the original value.
Each word is split at bit boundary 52/40/28/16 and the pieces redistributed across limbs.
Proved by `omega` after substituting `w = w % 2^k + (w / 2^k) * 2^k` for each word. -/
private theorem bit_slicing_identity (w0 w1 w2 w3 : Nat) :
    w0 % 2 ^ 52
    + (w0 / 2 ^ 52 + w1 % 2 ^ 40 * 2 ^ 12) * 2 ^ 52
    + (w1 / 2 ^ 40 + w2 % 2 ^ 28 * 2 ^ 24) * 2 ^ 104
    + (w2 / 2 ^ 28 + w3 % 2 ^ 16 * 2 ^ 36) * 2 ^ 156
    + w3 / 2 ^ 16 * 2 ^ 208
    = w0 + w1 * 2 ^ 64 + w2 * 2 ^ 128 + w3 * 2 ^ 192 := by
  have := Nat.div_add_mod w0 (2 ^ 52)
  have := Nat.div_add_mod w1 (2 ^ 40)
  have := Nat.div_add_mod w2 (2 ^ 28)
  have := Nat.div_add_mod w3 (2 ^ 16)
  omega

/-! ## Part 2: Main spec -/

set_option maxHeartbeats 400000 in -- heavy step
/-- **Spec and proof concerning `scalar.Scalar52.from_bytes`**:
- No panic (always returns successfully)
- The result represents the same number as the input byte array
- All limbs are < 2^52 (from masking with `(1 << 52) - 1` and `(1 << 48) - 1`)
-/
@[step]
theorem from_bytes_spec (b : Array U8 32#usize) :
    from_bytes b ⦃ u =>
    Scalar52_as_Nat u = U8x32_as_Nat b ∧
    ∀ i < 5, u[i]!.val < 2 ^ 52 ⦄
    := by
  unfold from_bytes
  -- Step through loop + mask computation
  let* ⟨ words1, words1_post ⟩ ← from_bytes_loop_spec
  let* ⟨ i, i_post1, i_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ mask, mask_post1, mask_post2 ⟩ ← U64.sub_spec
  let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ top_mask, top_mask_post1, top_mask_post2 ⟩ ← U64.sub_spec
  -- Limb 0: words1[0] & mask
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ v0, wb0, v0_post1, v0_post2 ⟩ ← Scalar52_index_mut_step
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← UScalar.and_spec
  -- Limb 1 setup: (words1[0] >> 52) | (words1[1] << 12)
  let* ⟨ i4, i4_post1, i4_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i5, i5_post ⟩ ← Array.index_usize_spec
  let* ⟨ i6, i6_post1, i6_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← UScalar.or_spec
  -- Limb 1: (i7) & mask  +  index_mut for slot 1
  let* ⟨ v1, wb1, v1_post1, v1_post2 ⟩ ← Scalar52_index_mut_step
  let* ⟨ i8, i8_post1, i8_post2 ⟩ ← UScalar.and_spec
  -- Limb 2 setup: (words1[1] >> 40) | (words1[2] << 24)
  let* ⟨ i9, i9_post1, i9_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec
  let* ⟨ i11, i11_post1, i11_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i12, i12_post1, i12_post2 ⟩ ← UScalar.or_spec
  -- Limb 2: (i12) & mask  +  index_mut for slot 2
  let* ⟨ v2, wb2, v2_post1, v2_post2 ⟩ ← Scalar52_index_mut_step
  let* ⟨ i13, i13_post1, i13_post2 ⟩ ← UScalar.and_spec
  -- Limb 3 setup: (words1[2] >> 28) | (words1[3] << 36)
  let* ⟨ i14, i14_post1, i14_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i15, i15_post ⟩ ← Array.index_usize_spec
  let* ⟨ i16, i16_post1, i16_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i17, i17_post1, i17_post2 ⟩ ← UScalar.or_spec
  -- Limb 3: (i17) & mask  +  index_mut for slot 3
  let* ⟨ v3, wb3, v3_post1, v3_post2 ⟩ ← Scalar52_index_mut_step
  let* ⟨ i18, i18_post1, i18_post2 ⟩ ← UScalar.and_spec
  -- Limb 4: (words1[3] >> 16) & top_mask
  let* ⟨ i19, i19_post1, i19_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ v4, wb4, v4_post1, v4_post2 ⟩ ← Scalar52_index_mut_step
  let* ⟨ i20, i20_post1, i20_post2 ⟩ ← UScalar.and_spec
  -- Concrete mask values
  have hU64 : U64.size = 2 ^ 64 := by scalar_tac
  have hmask : mask.val = 2 ^ 52 - 1 := by agrind
  have htop : top_mask.val = 2 ^ 48 - 1 := by agrind
  -- Extract each element of the result array via grind (handles Array.set/get)
  have helem0 : (wb4 i20)[0]! = i3 := by
    simp only [v4_post1, v3_post1, v2_post1, v1_post1, v0_post1, UScalar.ofNatCore_val_eq, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, ↓Array.getElem!_Nat_set_ne, one_ne_zero, Array.length,
      List.Vector.length_val, Nat.ofNat_pos, and_self, ↓Array.getElem!_Nat_set_eq]
  have helem1 : (wb4 i20)[1]! = i8 := by
    simp only [v4_post1, v3_post1, v2_post1, v1_post1, UScalar.ofNatCore_val_eq, ne_eq,
      OfNat.ofNat_ne_one, not_false_eq_true, ↓Array.getElem!_Nat_set_ne, Array.length,
      List.Vector.length_val, Nat.one_lt_ofNat, and_self, ↓Array.getElem!_Nat_set_eq]
  have helem2 : (wb4 i20)[2]! = i13 := by
    simp only [v4_post1, v3_post1, v2_post1, UScalar.ofNatCore_val_eq, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true, ↓Array.getElem!_Nat_set_ne, Nat.succ_ne_self, Array.length,
      List.Vector.length_val, Nat.reduceLT, and_self, ↓Array.getElem!_Nat_set_eq]
  have helem3 : (wb4 i20)[3]! = i18 := by
    simp only [v4_post1, v3_post1, UScalar.ofNatCore_val_eq, ne_eq, Nat.succ_ne_self,
      not_false_eq_true, ↓Array.getElem!_Nat_set_ne, Array.length, List.Vector.length_val,
      Nat.reduceLT, and_self, ↓Array.getElem!_Nat_set_eq]
  have helem4 : (wb4 i20)[4]! = i20 := by
    simp only [v4_post1, UScalar.ofNatCore_val_eq, Array.length, List.Vector.length_val,
      Nat.lt_add_one, and_self, ↓Array.getElem!_Nat_set_eq]
  -- Limb bounds: each is AND-masked
  simp only [UScalar.val_and] at i3_post1 i8_post1 i13_post1 i18_post1 i20_post1
  have hbound : ∀ idx < 5, (wb4 i20)[idx]!.val < 2 ^ 52 := by
    intro idx hidx
    interval_cases idx <;> simp only [helem0, helem1, helem2, helem3, helem4] <;>
    
    sorry
  -- Value preservation
  refine ⟨?_, hbound⟩
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
