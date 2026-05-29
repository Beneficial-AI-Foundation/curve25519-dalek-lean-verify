/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.R
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

/-! # Spec Theorem for `Scalar52::from_bytes_wide`

Converts a 64-byte (512-bit) little-endian integer to a
canonical `Scalar52` reduced modulo L.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs
(lines 97-132)

## Proof structure

1. `from_bytes_wide_loop_helper` / `from_bytes_wide_loop_spec`:
   Loop packs 64 bytes into 8 U64 words.
2. `bit_slicing_wide`: Pure math — 10 limbs (lo + hi) from
   8 words reconstruct the original value at a 2^260 split.
3. Montgomery algebra: `montgomery_mul(lo, R) + montgomery_mul(hi, RR)`
   = N mod L via the identity R = 2^260 mod L.
4. `from_bytes_wide_spec` (`@[step]`): Combines all pieces.
-/

set_option exponentiation.threshold 260

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-- LE value of 8 consecutive bytes at position `8*j`
in a 64-byte array. -/
abbrev word_of_bytes_64
    (bytes : Array U8 64#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8,
    bytes[8 * j + k]!.val * 2 ^ (8 * k)

-- Array.getElem!_Nat_set_eq / Array.getElem!_Nat_set_ne (Aeneas) subsume these.

/-! ## Part 1: Loop spec — byte packing (64 bytes → 8 words) -/

set_option maxHeartbeats 4000000 in -- heavy steps
/-- **Loop spec**: Each iteration packs 8 bytes into one
U64 word. After the loop, `words[j] = word_of_bytes_64 bytes j`
for all `j < 8`. -/
theorem from_bytes_wide_loop_helper
    (bytes : Array U8 64#usize)
    (words : Array U64 8#usize) (i : Usize)
    (hi : i.val ≤ 8)
    (h_prev : ∀ j, j < i.val →
      words[j]!.val = word_of_bytes_64 bytes j)
    (h_zero : ∀ j, i.val ≤ j → j < 8 →
      words[j]!.val = 0) :
    from_bytes_wide_loop bytes words i ⦃ words' =>
      ∀ j, j < 8 →
        words'[j]!.val = word_of_bytes_64 bytes j ⦄ := by
  induction h_rem : (8 - i.val) generalizing i words with
  | zero =>
    unfold from_bytes_wide_loop
    have hi8 : ¬ (i < 8#usize) := by scalar_tac
    simp only [hi8, ↓reduceIte, spec_ok]
    intro j hj; exact h_prev j (by omega)
  | succ n ih =>
    unfold from_bytes_wide_loop
    have hlt : i < 8#usize := by scalar_tac
    simp only [hlt, ↓reduceIte]
    let* ⟨ i1, i1_post ⟩ ← Usize.mul_spec
    let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    let* ⟨ i3, i3_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i4, i4_post1, i4_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i5, i5_post ⟩ ← Array.index_usize_spec
    let* ⟨ i6, i6_post1, i6_post2 ⟩ ← UScalar.or_spec
    let* ⟨ words1, words1_post ⟩ ← Array.update_spec
    let* ⟨ i7, i7_post ⟩ ← Usize.add_spec
    let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
    let* ⟨ i9, i9_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i10, i10_post1, i10_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i11, i11_post ⟩ ← Array.index_usize_spec
    let* ⟨ i12, i12_post1, i12_post2 ⟩ ← UScalar.or_spec
    let* ⟨ words2, words2_post ⟩ ← Array.update_spec
    let* ⟨ i13, i13_post ⟩ ← Usize.add_spec
    let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
    let* ⟨ i15, i15_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i16, i16_post ⟩ ← I32.mul_spec
    let* ⟨ i17, i17_post1, i17_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i18, i18_post ⟩ ← Array.index_usize_spec
    let* ⟨ i19, i19_post1, i19_post2 ⟩ ← UScalar.or_spec
    let* ⟨ words3, words3_post ⟩ ← Array.update_spec
    let* ⟨ i20, i20_post ⟩ ← Usize.add_spec
    let* ⟨ i21, i21_post ⟩ ← Array.index_usize_spec
    let* ⟨ i22, i22_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i23, i23_post ⟩ ← I32.mul_spec
    let* ⟨ i24, i24_post1, i24_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i25, i25_post ⟩ ← Array.index_usize_spec
    let* ⟨ i26, i26_post1, i26_post2 ⟩ ← UScalar.or_spec
    let* ⟨ words4, words4_post ⟩ ← Array.update_spec
    let* ⟨ i27, i27_post ⟩ ← Usize.add_spec
    let* ⟨ i28, i28_post ⟩ ← Array.index_usize_spec
    let* ⟨ i29, i29_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i30, i30_post ⟩ ← I32.mul_spec
    let* ⟨ i31, i31_post1, i31_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i32, i32_post ⟩ ← Array.index_usize_spec
    let* ⟨ i33, i33_post1, i33_post2 ⟩ ← UScalar.or_spec
    let* ⟨ words5, words5_post ⟩ ← Array.update_spec
    let* ⟨ i34, i34_post ⟩ ← Usize.add_spec
    let* ⟨ i35, i35_post ⟩ ← Array.index_usize_spec
    let* ⟨ i36, i36_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i37, i37_post ⟩ ← I32.mul_spec
    let* ⟨ i38, i38_post1, i38_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i39, i39_post ⟩ ← Array.index_usize_spec
    let* ⟨ i40, i40_post1, i40_post2 ⟩ ← UScalar.or_spec
    let* ⟨ words6, words6_post ⟩ ← Array.update_spec
    let* ⟨ i41, i41_post ⟩ ← Usize.add_spec
    let* ⟨ i42, i42_post ⟩ ← Array.index_usize_spec
    let* ⟨ i43, i43_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i44, i44_post ⟩ ← I32.mul_spec
    let* ⟨ i45, i45_post1, i45_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i46, i46_post ⟩ ← Array.index_usize_spec
    let* ⟨ i47, i47_post1, i47_post2 ⟩ ← UScalar.or_spec
    let* ⟨ words7, words7_post ⟩ ← Array.update_spec
    let* ⟨ i48, i48_post ⟩ ← Usize.add_spec
    let* ⟨ i49, i49_post ⟩ ← Array.index_usize_spec
    let* ⟨ i50, i50_post ⟩ ← UScalar.cast.step_spec
    let* ⟨ i51, i51_post ⟩ ← I32.mul_spec
    let* ⟨ i52, i52_post1, i52_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
    let* ⟨ i53, i53_post ⟩ ← Array.index_usize_spec
    let* ⟨ i54, i54_post1, i54_post2 ⟩ ← UScalar.or_spec
    let* ⟨ a, a_post ⟩ ← Array.update_spec
    let* ⟨ i55, i55_post ⟩ ← Usize.add_spec
    let* ⟨ words', words'_post1, words'_post2, words'_post3 ⟩ ← ih
    · subst a_post
      intro j hj
      by_cases heq : j = i.val
      · -- j = i: pack 8 bytes into word
        subst heq
        -- Phase 1: collapse read-modify-write lookups
        have h53 : i53 = i47 := by rw [i53_post, words7_post]; grind
        have h46 : i46 = i40 := by rw [i46_post, words6_post]; simp_lists
        have h39 : i39 = i33 := by rw [i39_post, words5_post]; grind
        have h32 : i32 = i26 := by rw [i32_post, words4_post]; simp_lists
        have h25 : i25 = i19 := by rw [i25_post, words3_post]; simp_lists
        have h18 : i18 = i12 := by rw [i18_post, words2_post]; simp_lists
        have h11 : i11 = i6  := by rw [i11_post, words1_post]; simp_lists
        -- Resolve outermost set
        simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
        rw [getElem!_pos _ _ (by simp only [List.length_set, List.Vector.length_val,
              UScalar.ofNatCore_val_eq]; omega),
            List.getElem_set_self (by simp only [List.length_set, List.Vector.length_val,
              UScalar.ofNatCore_val_eq]; omega)]
        -- Phase 2: expand OR chain
        simp (discharger := omega) only [h53, h46, h39, h32, h25, h18, h11,
          i54_post1, i47_post1, i40_post1, i33_post1, i26_post1, i19_post1,
          i12_post1, i6_post1, UScalar.val_or, UScalar.cast_val_eq,
          i3_post, i9_post, i15_post, i22_post, i29_post, i36_post, i43_post,
          i50_post, i4_post1, i10_post1, i17_post1, i24_post1, i31_post1,
          i38_post1, i45_post1, i52_post1, u8_val_mod_u64_numBits,
          Nat.shiftLeft_eq, u8_mul_pow_mod_u64, i2_post, i1_post, i5_post]
        -- Expand remaining bytes and shift amounts
        simp only [pow_zero, mul_one, i8_post, i7_post,
          i14_post, i13_post, i16_post, Int.reduceMul, Int.reduceToNat, i21_post,
          i20_post, i23_post, i28_post, i27_post, i30_post, i35_post, i34_post, i37_post, i42_post,
          i41_post, i44_post, i49_post, i48_post, i51_post]
        -- Eliminate initial zero: words[i] = 0 (from loop invariant)
        have hzero : (↑(↑words : List.Vector U64 8)[i.val]! : Nat) = 0 := by
          rw [Array.getElem!_Nat_eq]; agrind
        rw [← Array.getElem!_Nat_eq]
        rw [hzero]; simp only [Nat.zero_or]
        -- OR to sum, close with ring
        simp only [i1_post]
        rw [or_bytes_eq_sum _ _ _ _ _ _ _ _
          (bytes.val[i.val * 8]!).hmax (bytes.val[i.val * 8 + 1]!).hmax
          (bytes.val[i.val * 8 + 2]!).hmax (bytes.val[i.val * 8 + 3]!).hmax
          (bytes.val[i.val * 8 + 4]!).hmax (bytes.val[i.val * 8 + 5]!).hmax
          (bytes.val[i.val * 8 + 6]!).hmax (bytes.val[i.val * 8 + 7]!).hmax]
        simp only [word_of_bytes_64, Finset.sum_range_succ, Finset.range_zero,
          Finset.sum_empty, zero_add, Array.getElem!_Nat_eq]; ring_nf
      · -- j ≠ i: all 8 sets at index i, words[j] unchanged
        have h_ji : j < i.val := by omega
        have hne : Nat.not_eq i.val j := by simp [Nat.not_eq]; omega
        simp only [words7_post, words6_post, words5_post, words4_post,
          words3_post, words2_post, words1_post,
          Array.getElem!_Nat_eq, Array.set_val_eq, List.set_set,
          List.getElem!_set_ne _ _ _ _ hne]
        have := h_prev j h_ji
        rw [Array.getElem!_Nat_eq] at this
        exact this
    · -- h_zero for next iteration: a[j] = 0 for j ≥ i+1
      subst a_post; intro j hge hlt
      have hne : j ≠ i.val := by omega
      simp only [words7_post, words6_post, words5_post, words4_post,
        words3_post, words2_post, words1_post,
        Array.getElem!_Nat_eq, Array.set_val_eq, List.set_set]
      grind only [usr ScalarTac.IScalar.bounds,
        = List.getElem!_set_ne, =_ Array.getElem!_Nat_eq]
    · exact words'_post1 words'_post2 words'_post3

/-- Interpret 8 LE U64 words as a natural number. -/
def words_wide_as_Nat
    (words : Array U64 8#usize) : Nat :=
  ∑ j ∈ Finset.range 8,
    words[j]!.val * 2 ^ (64 * j)

/-- One block of 8 bytes shifted by `2^(64*j)` equals 8 flat byte terms. -/
private theorem word_of_bytes_64_shifted
    (b : Array U8 64#usize) (j : Nat) :
    word_of_bytes_64 b j * 2 ^ (64 * j)
      = ∑ k ∈ Finset.range 8, 2 ^ (8 * (8 * j + k)) * b[8 * j + k]!.val := by
  simp only [word_of_bytes_64, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [show 8 * (8 * j + k) = 8 * k + 64 * j from by ring, Nat.pow_add]
  ring

/-- Prefix regrouping: `t` blocks of 8 bytes = `8*t` flat bytes. -/
private theorem words_wide_prefix_eq
    (b : Array U8 64#usize) :
    ∀ t, t ≤ 8 →
      (∑ j ∈ Finset.range t, word_of_bytes_64 b j * 2 ^ (64 * j))
        = ∑ i ∈ Finset.range (8 * t), 2 ^ (8 * i) * b[i]!.val := by
  intro t ht
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega),
        show 8 * (n + 1) = 8 * n + 8 from by ring, Finset.sum_range_add]
    congr 1
    exact word_of_bytes_64_shifted b n

/-- Bridge: `words_wide_as_Nat = U8x64_as_Nat`. -/
theorem words_wide_eq_bytes
    (b : Array U8 64#usize)
    (words : Array U64 8#usize)
    (h : ∀ j, j < 8 →
      words[j]!.val = word_of_bytes_64 b j) :
    words_wide_as_Nat words = U8x64_as_Nat b := by
  simp only [words_wide_as_Nat, U8x64_as_Nat]
  calc ∑ j ∈ Finset.range 8, words[j]!.val * 2 ^ (64 * j)
      = ∑ j ∈ Finset.range 8, word_of_bytes_64 b j * 2 ^ (64 * j) := by
          apply Finset.sum_congr rfl; intro j hj
          rw [h j (Finset.mem_range.mp hj)]
    _ = ∑ i ∈ Finset.range 64, 2 ^ (8 * i) * b[i]!.val :=
          words_wide_prefix_eq b 8 le_rfl

/-- Loop spec with `words_wide_as_Nat` postcondition. -/
@[step]
theorem from_bytes_wide_loop_spec
    (bytes : Array U8 64#usize)
    (words : Array U64 8#usize)
    (i : Usize) (hi : i.val ≤ 8)
    (h_prev : ∀ j, j < i.val →
      words[j]!.val = word_of_bytes_64 bytes j)
    (h_zero : ∀ j, i.val ≤ j → j < 8 →
      words[j]!.val = 0) :
    from_bytes_wide_loop bytes words i ⦃ words' =>
      words_wide_as_Nat words' =
        U8x64_as_Nat bytes ⦄ := by
  apply spec_mono
    (from_bytes_wide_loop_helper bytes words i hi h_prev h_zero)
  intro words' hpost
  exact words_wide_eq_bytes bytes words' hpost

/-! ## Part 2: Bit-slicing identity (8 words → lo + hi)

Generalizes `bit_slicing_of_words` from FromBytes.lean.
Split into lo (5 limbs from words 0-4) and hi (5 limbs from words 4-7).

Proof technique: convert OR→add via `or_mul_pow_two_eq_add`,
simplify shift-left mods and outer mods via `omega`,
then close each half with `Nat.div_add_mod` + `omega`. -/

/-- Pure identity: 5 lo-limbs from words 0–4 reconstruct the low 260 bits. -/
private theorem bit_slicing_wide_lo_identity (w0 w1 w2 w3 w4 : Nat) :
    w0 % 2 ^ 52
    + (w0 / 2 ^ 52 + w1 % 2 ^ 40 * 2 ^ 12) * 2 ^ 52
    + (w1 / 2 ^ 40 + w2 % 2 ^ 28 * 2 ^ 24) * 2 ^ 104
    + (w2 / 2 ^ 28 + w3 % 2 ^ 16 * 2 ^ 36) * 2 ^ 156
    + (w3 / 2 ^ 16 + w4 % 2 ^ 4 * 2 ^ 48) * 2 ^ 208
    = w0 + w1 * 2 ^ 64 + w2 * 2 ^ 128 + w3 * 2 ^ 192
      + w4 % 2 ^ 4 * 2 ^ 256 := by
  have := Nat.div_add_mod w0 (2 ^ 52)
  have := Nat.div_add_mod w1 (2 ^ 40)
  have := Nat.div_add_mod w2 (2 ^ 28)
  have := Nat.div_add_mod w3 (2 ^ 16)
  omega

/-- Pure identity: 5 hi-limbs from words 4–7 reconstruct the high part. -/
private theorem bit_slicing_wide_hi_identity (w4 w5 w6 w7 : Nat) :
    (w4 / 2 ^ 4) % 2 ^ 52
    + (w4 / 2 ^ 56 + w5 % 2 ^ 44 * 2 ^ 8) * 2 ^ 52
    + (w5 / 2 ^ 44 + w6 % 2 ^ 32 * 2 ^ 20) * 2 ^ 104
    + (w6 / 2 ^ 32 + w7 % 2 ^ 20 * 2 ^ 32) * 2 ^ 156
    + w7 / 2 ^ 20 * 2 ^ 208
    = w4 / 2 ^ 4 + w5 * 2 ^ 60 + w6 * 2 ^ 124
      + w7 * 2 ^ 188 := by
  have h_dd : (w4 / 2 ^ 4) / 2 ^ 52 = w4 / 2 ^ 56 := by
    rw [Nat.div_div_eq_div_mul]; norm_num
  have h4 := Nat.div_add_mod (w4 / 2 ^ 4) (2 ^ 52)
  rw [h_dd] at h4
  have := Nat.div_add_mod w5 (2 ^ 44)
  have := Nat.div_add_mod w6 (2 ^ 32)
  have := Nat.div_add_mod w7 (2 ^ 20)
  omega

/-- The 10 limbs extracted via shift/OR/mask from 8 U64 words reconstruct
the same value: `lo + hi * 2^260 = words_wide`. -/
theorem bit_slicing_wide (w0 w1 w2 w3 w4 w5 w6 w7 : U64) :
    -- Lo limbs (5)
    let lo0 := w0.val % 2 ^ 52
    let lo1 := ((w0.val / 2 ^ 52) ||| ((w1.val * 2 ^ 12) % U64.size)) % 2 ^ 52
    let lo2 := ((w1.val / 2 ^ 40) ||| ((w2.val * 2 ^ 24) % U64.size)) % 2 ^ 52
    let lo3 := ((w2.val / 2 ^ 28) ||| ((w3.val * 2 ^ 36) % U64.size)) % 2 ^ 52
    let lo4 := ((w3.val / 2 ^ 16) ||| ((w4.val * 2 ^ 48) % U64.size)) % 2 ^ 52
    -- Hi limbs (5)
    let hi0 := (w4.val / 2 ^ 4) % 2 ^ 52
    let hi1 := ((w4.val / 2 ^ 56) ||| ((w5.val * 2 ^ 8) % U64.size)) % 2 ^ 52
    let hi2 := ((w5.val / 2 ^ 44) ||| ((w6.val * 2 ^ 20) % U64.size)) % 2 ^ 52
    let hi3 := ((w6.val / 2 ^ 32) ||| ((w7.val * 2 ^ 32) % U64.size)) % 2 ^ 52
    let hi4 := w7.val / 2 ^ 20
    -- Identity
    (lo0 + lo1 * 2 ^ 52 + lo2 * 2 ^ 104 + lo3 * 2 ^ 156 + lo4 * 2 ^ 208)
    + (hi0 + hi1 * 2 ^ 52 + hi2 * 2 ^ 104 + hi3 * 2 ^ 156
       + hi4 * 2 ^ 208) * 2 ^ 260
    = w0.val + w1.val * 2 ^ 64 + w2.val * 2 ^ 128 + w3.val * 2 ^ 192
      + w4.val * 2 ^ 256 + w5.val * 2 ^ 320 + w6.val * 2 ^ 384
      + w7.val * 2 ^ 448 := by
  -- Get concrete bounds
  have hU : U64.size = 2 ^ 64 := by scalar_tac
  have hw0 : w0.val < 2 ^ 64 := hU ▸ w0.hmax
  have hw1 : w1.val < 2 ^ 64 := hU ▸ w1.hmax
  have hw2 : w2.val < 2 ^ 64 := hU ▸ w2.hmax
  have hw3 : w3.val < 2 ^ 64 := hU ▸ w3.hmax
  have hw4 : w4.val < 2 ^ 64 := hU ▸ w4.hmax
  have hw5 : w5.val < 2 ^ 64 := hU ▸ w5.hmax
  have hw6 : w6.val < 2 ^ 64 := hU ▸ w6.hmax
  have hw7 : w7.val < 2 ^ 64 := hU ▸ w7.hmax
  -- Simplify shift-left mods: w * 2^k % 2^64 → (w % 2^m) * 2^k
  simp only [hU,
    show w1.val * 2 ^ 12 % 2 ^ 64 = (w1.val % 2 ^ 52) * 2 ^ 12 from by omega,
    show w2.val * 2 ^ 24 % 2 ^ 64 = (w2.val % 2 ^ 40) * 2 ^ 24 from by omega,
    show w3.val * 2 ^ 36 % 2 ^ 64 = (w3.val % 2 ^ 28) * 2 ^ 36 from by omega,
    show w4.val * 2 ^ 48 % 2 ^ 64 = (w4.val % 2 ^ 16) * 2 ^ 48 from by omega,
    show w5.val * 2 ^ 8 % 2 ^ 64 = (w5.val % 2 ^ 56) * 2 ^ 8 from by omega,
    show w6.val * 2 ^ 20 % 2 ^ 64 = (w6.val % 2 ^ 44) * 2 ^ 20 from by omega,
    show w7.val * 2 ^ 32 % 2 ^ 64 = (w7.val % 2 ^ 32) * 2 ^ 32 from by omega]
  -- Convert OR to add (non-overlapping bit ranges)
  rw [or_mul_pow_two_eq_add _ _ 12 (by omega),
      or_mul_pow_two_eq_add _ _ 24 (by omega),
      or_mul_pow_two_eq_add _ _ 36 (by omega),
      or_mul_pow_two_eq_add _ _ 48 (by omega),
      or_mul_pow_two_eq_add _ _ 8 (by omega),
      or_mul_pow_two_eq_add _ _ 20 (by omega),
      or_mul_pow_two_eq_add _ _ 32 (by omega)]
  -- Simplify outer mods (sums fit in 52 bits)
  rw [show (w0.val / 2 ^ 52 + (w1.val % 2 ^ 52) * 2 ^ 12) % 2 ^ 52 =
        w0.val / 2 ^ 52 + (w1.val % 2 ^ 40) * 2 ^ 12 from by omega,
      show (w1.val / 2 ^ 40 + (w2.val % 2 ^ 40) * 2 ^ 24) % 2 ^ 52 =
        w1.val / 2 ^ 40 + (w2.val % 2 ^ 28) * 2 ^ 24 from by omega,
      show (w2.val / 2 ^ 28 + (w3.val % 2 ^ 28) * 2 ^ 36) % 2 ^ 52 =
        w2.val / 2 ^ 28 + (w3.val % 2 ^ 16) * 2 ^ 36 from by omega,
      show (w3.val / 2 ^ 16 + (w4.val % 2 ^ 16) * 2 ^ 48) % 2 ^ 52 =
        w3.val / 2 ^ 16 + (w4.val % 2 ^ 4) * 2 ^ 48 from by omega,
      show (w4.val / 2 ^ 56 + (w5.val % 2 ^ 56) * 2 ^ 8) % 2 ^ 52 =
        w4.val / 2 ^ 56 + (w5.val % 2 ^ 44) * 2 ^ 8 from by omega,
      show (w5.val / 2 ^ 44 + (w6.val % 2 ^ 44) * 2 ^ 20) % 2 ^ 52 =
        w5.val / 2 ^ 44 + (w6.val % 2 ^ 32) * 2 ^ 20 from by omega,
      show (w6.val / 2 ^ 32 + (w7.val % 2 ^ 32) * 2 ^ 32) % 2 ^ 52 =
        w6.val / 2 ^ 32 + (w7.val % 2 ^ 20) * 2 ^ 32 from by omega]
  -- Apply pure identities and combine
  rw [bit_slicing_wide_lo_identity w0.val w1.val w2.val w3.val w4.val,
      bit_slicing_wide_hi_identity w4.val w5.val w6.val w7.val]
  have := Nat.div_add_mod w4.val (2 ^ 4)
  omega

/-! ## Part 3: Stage decomposition

The body of `from_bytes_wide` has ~70 monadic bindings. Threading a single `step*` through
all of them hits the elaboration regression in the new Aeneas `do` elaborator. We split the
body into named stage `def`s — one per 52-bit limb extraction — modelled on the pattern used
in `Pow2K.lean`. Each stage wraps a small contiguous block of bindings, has its own
`@[step]` spec, and is "folded into" the body via a small `rfl`-style equality lemma.
-/

/-- Stage `lo0`: read `words1[0]` and obtain the position-0 setter for `ZERO`. -/
def from_bytes_wide_lo0 (words1 : Array U64 8#usize) :
    Result (U64 × (U64 → Scalar52)) := do
  let i1 ← Array.index_usize words1 0#usize
  let pair ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut ZERO 0#usize
  ok (i1, pair.2)

theorem fold_from_bytes_wide_lo0 {α : Type} (words1 : Array U64 8#usize)
    (f : U64 → (U64 → Scalar52) → Result α) :
    (do let i1 ← Array.index_usize words1 0#usize
        let (_, index_mut_back) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut ZERO 0#usize
        f i1 index_mut_back) =
    (do let r ← from_bytes_wide_lo0 words1; f r.1 r.2) := by
  simp only [from_bytes_wide_lo0, bind_assoc_eq, bind_tc_ok]

@[step]
theorem from_bytes_wide_lo0_spec (words1 : Array U64 8#usize) :
    from_bytes_wide_lo0 words1 ⦃ i1 set_back =>
      i1 = words1.val[0]! ∧ set_back = Std.Array.set ZERO 0#usize ⦄ := by
  unfold from_bytes_wide_lo0
  dsimp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize,
              bind_assoc_eq, bind_tc_ok]
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  exact i1_post

/-- Merged stage `lo12` (= old `lo1 + lo2`): extract `lo`'s limbs 0 and 1, prepare the
merged U64 `i11` for limb 2, and obtain the position-2 setter for `lo`. Returns the
internal `i4, i6` values so they remain available to the bit-slicing identity in the
main spec. -/
def from_bytes_wide_lo12 (words1 : Array U64 8#usize) (mask i1 : U64)
    (index_mut_back : U64 → Scalar52) :
    Result (U64 × U64 × U64 × U64 × (U64 → Scalar52)) := do
  -- lo1 body
  let i2 ← lift (i1 &&& mask)
  let i3 ← i1 >>> 52#i32
  let i4 ← Array.index_usize words1 1#usize
  let i5 ← i4 <<< 12#i32
  let i6 ← lift (i3 ||| i5)
  let lo := index_mut_back i2
  let pair1 ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo 1#usize
  -- lo2 body
  let i7 ← lift (i6 &&& mask)
  let i8 ← i4 >>> 40#i32
  let i9 ← Array.index_usize words1 2#usize
  let i10 ← i9 <<< 24#i32
  let i11 ← lift (i8 ||| i10)
  let lo1 := pair1.2 i7
  let pair2 ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo1 2#usize
  ok (i4, i6, i9, i11, pair2.2)

theorem fold_from_bytes_wide_lo12 {α : Type} (words1 : Array U64 8#usize) (mask i1 : U64)
    (index_mut_back : U64 → Scalar52)
    (f : U64 → U64 → U64 → U64 → (U64 → Scalar52) → Result α) :
    (do let i2 ← lift (i1 &&& mask)
        let i3 ← i1 >>> 52#i32
        let i4 ← Array.index_usize words1 1#usize
        let i5 ← i4 <<< 12#i32
        let i6 ← lift (i3 ||| i5)
        let lo := index_mut_back i2
        let (_, index_mut_back1) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo 1#usize
        let i7 ← lift (i6 &&& mask)
        let i8 ← i4 >>> 40#i32
        let i9 ← Array.index_usize words1 2#usize
        let i10 ← i9 <<< 24#i32
        let i11 ← lift (i8 ||| i10)
        let lo1 := index_mut_back1 i7
        let (_, index_mut_back2) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo1 2#usize
        f i4 i6 i9 i11 index_mut_back2) =
    (do let r ← from_bytes_wide_lo12 words1 mask i1 index_mut_back
        f r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
  simp only [from_bytes_wide_lo12, bind_assoc_eq, bind_tc_ok]

@[step]
theorem from_bytes_wide_lo12_spec
    (words1 : Array U64 8#usize) (mask i1 : U64) (index_mut_back : U64 → Scalar52) :
    from_bytes_wide_lo12 words1 mask i1 index_mut_back ⦃ i4 i6 i9 i11 set_back =>
      i4 = words1.val[1]! ∧
      i6.val = (i1.val >>> 52) ||| ((i4.val <<< 12) % U64.size) ∧
      i9 = words1.val[2]! ∧
      i11.val = (i4.val >>> 40) ||| ((i9.val <<< 24) % U64.size) ∧
      set_back = Std.Array.set
        (Std.Array.set (index_mut_back (i1 &&& mask)) 1#usize (i6 &&& mask)) 2#usize ⦄ := by
  unfold from_bytes_wide_lo12
  dsimp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize,
              bind_assoc_eq, bind_tc_ok]
  let* ⟨ i2, i2_post1, i2_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post1, i5_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i6, i6_post1, i6_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x1, x1_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i8, i8_post1, i8_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i9, i9_post ⟩ ← Array.index_usize_spec
  let* ⟨ i10, i10_post1, i10_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i11, i11_post1, i11_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x2, x2_post ⟩ ← Array.index_usize_spec
  refine ⟨i4_post, ?_, i9_post, ?_, ?_⟩
  · rw [i6_post1, UScalar.val_or, i3_post1, i5_post1]
  · rw [i11_post1, UScalar.val_or, i8_post1, i10_post1]
  · have h2 : i2 = i1 &&& mask := by
      apply U64.bv_eq_imp_eq; simp [i2_post2]
    have h7 : i7 = i6 &&& mask := by
      apply U64.bv_eq_imp_eq; simp [i7_post2]
    rw [h2, h7]

/-- Merged stage `lo34` (= old `lo3 + lo4`): extract `lo`'s limbs 2 and 3, prepare the
merged U64 `i21` for limb 4, and obtain the position-4 setter for `lo`. Returns the
internal `i14, i16` values for the bit-slicing identity. -/
def from_bytes_wide_lo34 (words1 : Array U64 8#usize) (mask i9 i11 : U64)
    (index_mut_back2 : U64 → Scalar52) :
    Result (U64 × U64 × U64 × U64 × (U64 → Scalar52)) := do
  -- lo3 body
  let i12 ← lift (i11 &&& mask)
  let i13 ← i9 >>> 28#i32
  let i14 ← Array.index_usize words1 3#usize
  let i15 ← i14 <<< 36#i32
  let i16 ← lift (i13 ||| i15)
  let lo2 := index_mut_back2 i12
  let pair3 ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo2 3#usize
  -- lo4 body
  let i17 ← lift (i16 &&& mask)
  let i18 ← i14 >>> 16#i32
  let i19 ← Array.index_usize words1 4#usize
  let i20 ← i19 <<< 48#i32
  let i21 ← lift (i18 ||| i20)
  let lo3 := pair3.2 i17
  let pair4 ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo3 4#usize
  ok (i14, i16, i19, i21, pair4.2)

theorem fold_from_bytes_wide_lo34 {α : Type} (words1 : Array U64 8#usize) (mask i9 i11 : U64)
    (index_mut_back2 : U64 → Scalar52)
    (f : U64 → U64 → U64 → U64 → (U64 → Scalar52) → Result α) :
    (do let i12 ← lift (i11 &&& mask)
        let i13 ← i9 >>> 28#i32
        let i14 ← Array.index_usize words1 3#usize
        let i15 ← i14 <<< 36#i32
        let i16 ← lift (i13 ||| i15)
        let lo2 := index_mut_back2 i12
        let (_, index_mut_back3) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo2 3#usize
        let i17 ← lift (i16 &&& mask)
        let i18 ← i14 >>> 16#i32
        let i19 ← Array.index_usize words1 4#usize
        let i20 ← i19 <<< 48#i32
        let i21 ← lift (i18 ||| i20)
        let lo3 := index_mut_back3 i17
        let (_, index_mut_back4) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut lo3 4#usize
        f i14 i16 i19 i21 index_mut_back4) =
    (do let r ← from_bytes_wide_lo34 words1 mask i9 i11 index_mut_back2
        f r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
  simp only [from_bytes_wide_lo34, bind_assoc_eq, bind_tc_ok]

@[step]
theorem from_bytes_wide_lo34_spec
    (words1 : Array U64 8#usize) (mask i9 i11 : U64) (index_mut_back2 : U64 → Scalar52) :
    from_bytes_wide_lo34 words1 mask i9 i11 index_mut_back2 ⦃ i14 i16 i19 i21 set_back =>
      i14 = words1.val[3]! ∧
      i16.val = (i9.val >>> 28) ||| ((i14.val <<< 36) % U64.size) ∧
      i19 = words1.val[4]! ∧
      i21.val = (i14.val >>> 16) ||| ((i19.val <<< 48) % U64.size) ∧
      set_back = Std.Array.set
        (Std.Array.set (index_mut_back2 (i11 &&& mask)) 3#usize (i16 &&& mask)) 4#usize ⦄ := by
  unfold from_bytes_wide_lo34
  dsimp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize,
              bind_assoc_eq, bind_tc_ok]
  let* ⟨ i12, i12_post1, i12_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i13, i13_post1, i13_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
  let* ⟨ i15, i15_post1, i15_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i16, i16_post1, i16_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x1, x1_post ⟩ ← Array.index_usize_spec
  let* ⟨ i17, i17_post1, i17_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i18, i18_post1, i18_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i19, i19_post ⟩ ← Array.index_usize_spec
  let* ⟨ i20, i20_post1, i20_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i21, i21_post1, i21_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x2, x2_post ⟩ ← Array.index_usize_spec
  refine ⟨i14_post, ?_, i19_post, ?_, ?_⟩
  · rw [i16_post1, UScalar.val_or, i13_post1, i15_post1]
  · rw [i21_post1, UScalar.val_or, i18_post1, i20_post1]
  · have h12 : i12 = i11 &&& mask := by
      apply U64.bv_eq_imp_eq; simp [i12_post2]
    have h17 : i17 = i16 &&& mask := by
      apply U64.bv_eq_imp_eq; simp [i17_post2]
    rw [h12, h17]

/-- Stage `hi0_xfer`: extract `lo`'s limb 4 value `i22 = i21 &&& mask` (kept for the final
`index_mut_back4 i22` outside), then start the `hi` side: limb 0 (`i24`), merged U64 for
limb 1 (`i28`), and the position-1 setter for `hi`. Uses the original `index_mut_back`
(the `ZERO[0]` setter from `lo0`) to construct `hi`. -/
def from_bytes_wide_hi0_xfer (words1 : Array U64 8#usize) (mask i19 i21 : U64)
    (index_mut_back : U64 → Scalar52) :
    Result (U64 × U64 × U64 × U64 × (U64 → Scalar52)) := do
  let i22 ← lift (i21 &&& mask)
  let i23 ← i19 >>> 4#i32
  let i24 ← lift (i23 &&& mask)
  let i25 ← i19 >>> 56#i32
  let i26 ← Array.index_usize words1 5#usize
  let i27 ← i26 <<< 8#i32
  let i28 ← lift (i25 ||| i27)
  let hi := index_mut_back i24
  let pair ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi 1#usize
  ok (i22, i24, i26, i28, pair.2)

theorem fold_from_bytes_wide_hi0_xfer {α : Type} (words1 : Array U64 8#usize)
    (mask i19 i21 : U64) (index_mut_back : U64 → Scalar52)
    (f : U64 → U64 → U64 → U64 → (U64 → Scalar52) → Result α) :
    (do let i22 ← lift (i21 &&& mask)
        let i23 ← i19 >>> 4#i32
        let i24 ← lift (i23 &&& mask)
        let i25 ← i19 >>> 56#i32
        let i26 ← Array.index_usize words1 5#usize
        let i27 ← i26 <<< 8#i32
        let i28 ← lift (i25 ||| i27)
        let hi := index_mut_back i24
        let (_, index_mut_back5) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi 1#usize
        f i22 i24 i26 i28 index_mut_back5) =
    (do let r ← from_bytes_wide_hi0_xfer words1 mask i19 i21 index_mut_back
        f r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
  simp only [from_bytes_wide_hi0_xfer, bind_assoc_eq, bind_tc_ok]

@[step]
theorem from_bytes_wide_hi0_xfer_spec
    (words1 : Array U64 8#usize) (mask i19 i21 : U64)
    (index_mut_back : U64 → Scalar52) :
    from_bytes_wide_hi0_xfer words1 mask i19 i21 index_mut_back
      ⦃ i22 i24 i26 i28 set_back =>
        i22 = i21 &&& mask ∧
        i24.val = (i19.val >>> 4) &&& mask.val ∧
        i26 = words1.val[5]! ∧
        i28.val = (i19.val >>> 56) ||| ((i26.val <<< 8) % U64.size) ∧
        set_back = Std.Array.set (index_mut_back i24) 1#usize ⦄ := by
  unfold from_bytes_wide_hi0_xfer
  dsimp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize,
              bind_assoc_eq, bind_tc_ok]
  let* ⟨ i22, i22_post1, i22_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i23, i23_post1, i23_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i24, i24_post1, i24_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i25, i25_post1, i25_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i26, i26_post ⟩ ← Array.index_usize_spec
  let* ⟨ i27, i27_post1, i27_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i28, i28_post1, i28_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply U64.bv_eq_imp_eq; simp [i22_post2]
  · rw [i24_post1, UScalar.val_and, i23_post1]
  · exact i26_post
  · rw [i28_post1, UScalar.val_or, i25_post1, i27_post1]

/-- Merged stage `hi12` (= old `hi1 + hi2`): extract `hi`'s limbs 1 and 2, prepare the
merged U64 `i38` for limb 3, and obtain the position-3 setter for `hi`. Returns the
internal `i31, i33` values for the bit-slicing identity. -/
def from_bytes_wide_hi12 (words1 : Array U64 8#usize) (mask i26 i28 : U64)
    (index_mut_back5 : U64 → Scalar52) :
    Result (U64 × U64 × U64 × U64 × (U64 → Scalar52)) := do
  -- hi1 body
  let i29 ← lift (i28 &&& mask)
  let i30 ← i26 >>> 44#i32
  let i31 ← Array.index_usize words1 6#usize
  let i32 ← i31 <<< 20#i32
  let i33 ← lift (i30 ||| i32)
  let hi1 := index_mut_back5 i29
  let pair2 ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi1 2#usize
  -- hi2 body
  let i34 ← lift (i33 &&& mask)
  let i35 ← i31 >>> 32#i32
  let i36 ← Array.index_usize words1 7#usize
  let i37 ← i36 <<< 32#i32
  let i38 ← lift (i35 ||| i37)
  let hi2 := pair2.2 i34
  let pair3 ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi2 3#usize
  ok (i31, i33, i36, i38, pair3.2)

theorem fold_from_bytes_wide_hi12 {α : Type} (words1 : Array U64 8#usize) (mask i26 i28 : U64)
    (index_mut_back5 : U64 → Scalar52)
    (f : U64 → U64 → U64 → U64 → (U64 → Scalar52) → Result α) :
    (do let i29 ← lift (i28 &&& mask)
        let i30 ← i26 >>> 44#i32
        let i31 ← Array.index_usize words1 6#usize
        let i32 ← i31 <<< 20#i32
        let i33 ← lift (i30 ||| i32)
        let hi1 := index_mut_back5 i29
        let (_, index_mut_back6) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi1 2#usize
        let i34 ← lift (i33 &&& mask)
        let i35 ← i31 >>> 32#i32
        let i36 ← Array.index_usize words1 7#usize
        let i37 ← i36 <<< 32#i32
        let i38 ← lift (i35 ||| i37)
        let hi2 := index_mut_back6 i34
        let (_, index_mut_back7) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi2 3#usize
        f i31 i33 i36 i38 index_mut_back7) =
    (do let r ← from_bytes_wide_hi12 words1 mask i26 i28 index_mut_back5
        f r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) := by
  simp only [from_bytes_wide_hi12, bind_assoc_eq, bind_tc_ok]

@[step]
theorem from_bytes_wide_hi12_spec
    (words1 : Array U64 8#usize) (mask i26 i28 : U64) (index_mut_back5 : U64 → Scalar52) :
    from_bytes_wide_hi12 words1 mask i26 i28 index_mut_back5 ⦃ i31 i33 i36 i38 set_back =>
      i31 = words1.val[6]! ∧
      i33.val = (i26.val >>> 44) ||| ((i31.val <<< 20) % U64.size) ∧
      i36 = words1.val[7]! ∧
      i38.val = (i31.val >>> 32) ||| ((i36.val <<< 32) % U64.size) ∧
      set_back = Std.Array.set
        (Std.Array.set (index_mut_back5 (i28 &&& mask)) 2#usize (i33 &&& mask)) 3#usize ⦄ := by
  unfold from_bytes_wide_hi12
  dsimp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize,
              bind_assoc_eq, bind_tc_ok]
  let* ⟨ i29, i29_post1, i29_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i30, i30_post1, i30_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i31, i31_post ⟩ ← Array.index_usize_spec
  let* ⟨ i32, i32_post1, i32_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i33, i33_post1, i33_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x1, x1_post ⟩ ← Array.index_usize_spec
  let* ⟨ i34, i34_post1, i34_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i35, i35_post1, i35_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i36, i36_post ⟩ ← Array.index_usize_spec
  let* ⟨ i37, i37_post1, i37_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i38, i38_post1, i38_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x2, x2_post ⟩ ← Array.index_usize_spec
  refine ⟨i31_post, ?_, i36_post, ?_, ?_⟩
  · rw [i33_post1, UScalar.val_or, i30_post1, i32_post1]
  · rw [i38_post1, UScalar.val_or, i35_post1, i37_post1]
  · have h29 : i29 = i28 &&& mask := by
      apply U64.bv_eq_imp_eq; simp [i29_post2]
    have h34 : i34 = i33 &&& mask := by
      apply U64.bv_eq_imp_eq; simp [i34_post2]
    rw [h29, h34]

/-- Stage `hi3`: extract `hi`'s limb 3 (= `i39`), handle the `massert(20 < 64)`, get
position-4 setter. The top limb extraction `i41 = i36 >>> 20` is kept inline in the main
spec since it doesn't fit naturally into a sibling chain. -/
def from_bytes_wide_hi3 (mask i38 : U64) (index_mut_back7 : U64 → Scalar52) :
    Result (U64 × (U64 → Scalar52)) := do
  let i39 ← lift (i38 &&& mask)
  let i40 ← lift (IScalar.hcast .U32 20#i32)
  massert (i40 < 64#u32)
  let hi3 := index_mut_back7 i39
  let pair ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi3 4#usize
  ok (i39, pair.2)

theorem fold_from_bytes_wide_hi3 {α : Type} (mask i38 : U64)
    (index_mut_back7 : U64 → Scalar52) (f : U64 → (U64 → Scalar52) → Result α) :
    (do let i39 ← lift (i38 &&& mask)
        let i40 ← lift (IScalar.hcast .U32 20#i32)
        massert (i40 < 64#u32)
        let hi3 := index_mut_back7 i39
        let (_, index_mut_back8) ←
          Insts.CoreOpsIndexIndexMutUsizeU64.index_mut hi3 4#usize
        f i39 index_mut_back8) =
    (do let r ← from_bytes_wide_hi3 mask i38 index_mut_back7; f r.1 r.2) := by
  simp only [from_bytes_wide_hi3, bind_assoc_eq, bind_tc_ok]

@[step]
theorem from_bytes_wide_hi3_spec
    (mask i38 : U64) (index_mut_back7 : U64 → Scalar52) :
    from_bytes_wide_hi3 mask i38 index_mut_back7 ⦃ i39 set_back =>
      i39 = i38 &&& mask ∧
      set_back = Std.Array.set (index_mut_back7 (i38 &&& mask)) 4#usize ⦄ := by
  unfold from_bytes_wide_hi3
  dsimp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize,
              bind_assoc_eq, bind_tc_ok]
  let* ⟨ i39, i39_post1, i39_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i40, i40_post ⟩ ← IScalar.hcast.step_spec
  let* ⟨ ⟩ ← massert_spec
  · rw [i40_post]; decide
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  have h39 : i39 = i38 &&& mask := by
    apply U64.bv_eq_imp_eq
    simp [i39_post2]
  refine ⟨h39, ?_⟩
  rw [h39]

/-! ## Part 4: Main spec -/

/-- Equates `from_bytes_wide b` to the staged form, replacing the raw 70-binder do-block
    with 6 named stage calls. Proved by unfolding all stages and normalising binds. -/
theorem from_bytes_wide_eq (b : Array U8 64#usize) :
    from_bytes_wide b = (do
      let words := Array.repeat 8#usize 0#u64
      let words1 ← from_bytes_wide_loop b words 0#usize
      let i ← 1#u64 <<< 52#i32
      let mask ← i - 1#u64
      let r0 ← from_bytes_wide_lo0 words1
      let r12 ← from_bytes_wide_lo12 words1 mask r0.1 r0.2
      let r34 ← from_bytes_wide_lo34 words1 mask r12.2.2.1 r12.2.2.2.1 r12.2.2.2.2
      let r5  ← from_bytes_wide_hi0_xfer words1 mask r34.2.2.1 r34.2.2.2.1 r0.2
      let r67 ← from_bytes_wide_hi12 words1 mask r5.2.2.1 r5.2.2.2.1 r5.2.2.2.2
      let r8  ← from_bytes_wide_hi3 mask r67.2.2.2.1 r67.2.2.2.2
      let i41 ← r67.2.2.1 >>> 20#i32
      let lo5 ← (r34.2.2.2.2 r5.1).montgomery_mul constants.R
      let hi5 ← (r8.2 i41).montgomery_mul constants.RR
      hi5.add lo5) := by
  simp only [from_bytes_wide, from_bytes_wide_lo0, from_bytes_wide_lo12, from_bytes_wide_lo34,
             from_bytes_wide_hi0_xfer, from_bytes_wide_hi12, from_bytes_wide_hi3,
             bind_assoc_eq, bind_tc_ok]
  rfl

set_option maxHeartbeats 4000000 in -- heavy staged proof
/-- **Spec for `Scalar52::from_bytes_wide`**:
- No panic
- Result = input mod L (canonical form)
- All limbs < 2^52 -/
@[step]
theorem from_bytes_wide_spec
    (b : Array U8 64#usize) :
    from_bytes_wide b ⦃ (u : Scalar52) =>
      Scalar52_as_Nat u = U8x64_as_Nat b % L ∧
      Scalar52_as_Nat u < L ∧
      ∀ i < 5, u[i]!.val < 2 ^ 52 ⦄ := by
  rw [from_bytes_wide_eq]
  -- Step through loop + mask computation
  let* ⟨ words1, words1_post ⟩ ← from_bytes_wide_loop_spec
  · intro j h hj;
    simp only [Array.getElem!_Nat_eq, Array.repeat_val, UScalar.ofNatCore_val_eq,
      List.reduceReplicate]
    agrind
  let* ⟨ i, i_post1, i_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ mask, mask_post1, mask_post2 ⟩ ← U64.sub_spec
  -- Step through each merged stage (6 stages total)
  step as ⟨ i1, index_mut_back, i1_post, set0_eq ⟩
  step as ⟨ i4, i6, i9, i11, index_mut_back2,
            i4_post, i6_post, i9_post, i11_post, set12_eq ⟩
  step as ⟨ i14, i16, i19, i21, index_mut_back4,
            i14_post, i16_post, i19_post, i21_post, set34_eq ⟩
  step as ⟨ i22, i24, i26, i28, index_mut_back5, i22_eq, i24_val, i26_post, i28_post ⟩
  step as ⟨ i31, i33, i36, i38, index_mut_back7,
            i31_post, i33_post, i36_post, i38_post, set67_eq ⟩
  step as ⟨ i39, index_mut_back8, i39_eq, set8_eq ⟩
  -- Top limb of hi: i41 = i36 >>> 20
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  -- Setup: mask value + handy facts
  have hmask : mask.val = 2 ^ 52 - 1 := by scalar_tac
  -- lo and hi as explicit Std.Array.set chains over ZERO
  set lo := (((((Std.Array.set ZERO 0#usize (i1 &&& mask)).set 1#usize (i6 &&& mask)).set 2#usize
    (i11 &&& mask)).set 3#usize (i16 &&& mask)).set 4#usize i22) with lo_def
  set hi := (((((Std.Array.set ZERO 0#usize i24).set 1#usize (i28 &&& mask)).set 2#usize
    (i33 &&& mask)).set 3#usize (i38 &&& mask)).set 4#usize i41) with hi_def
  -- lo limb bounds (each < 2^52)
  -- limb4 = i22 = i21 &&& mask, so we need i22_eq to rewrite it
  have hi22_bound : i22.val < 2 ^ 52 := by
    rw [i22_eq, UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod]; omega
  have hlo52 : ∀ j < 5, lo[j]!.val < 2 ^ 52 := by
    simp only [lo_def]
    intro j hj
    interval_cases j <;>
      simp only [↓Array.getElem!_Nat_set_ne, ↓Array.getElem!_Nat_set_eq,
        UScalar.ofNatCore_val_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        OfNat.ofNat_ne_zero, one_ne_zero, Nat.succ_ne_self, Array.length,
        List.Vector.length_val, Nat.ofNat_pos, and_self, Nat.reduceLT, Nat.lt_add_one,
        UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod, hi22_bound] <;> omega
  -- hi limb bounds (each < 2^52)
  -- limb0 = i24.val < 2^52 (masked), limb4 = i41.val = i36.val >>> 20 < 2^44 < 2^52
  have hi24_bound : i24.val < 2 ^ 52 := by
    rw [i24_val, hmask, land_pow_two_sub_one_eq_mod]; omega
  have hi41_bound : i41.val < 2 ^ 52 := by
    rw [i41_post1, Nat.shiftRight_eq_div_pow]
    have : i36.val < 2 ^ 64 := by scalar_tac
    omega
  have hhi52 : ∀ j < 5, hi[j]!.val < 2 ^ 52 := by
    simp only [hi_def]
    intro j hj
    interval_cases j <;>
      simp only [↓Array.getElem!_Nat_set_ne, ↓Array.getElem!_Nat_set_eq,
        UScalar.ofNatCore_val_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        OfNat.ofNat_ne_zero, one_ne_zero, Nat.succ_ne_self, Array.length,
        List.Vector.length_val, Nat.ofNat_pos, and_self, Nat.reduceLT, Nat.lt_add_one,
        UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod, hi24_bound, hi41_bound] <;> omega
  -- Identify index_mut_back4 i22 = lo and index_mut_back8 i41 = hi
  have hlo_eq : index_mut_back4 i22 = lo := by
    simp only [set34_eq, set12_eq, set0_eq]; exact lo_def.symm
  have hhi_eq : index_mut_back8 i41 = hi := by
    have set5_eq := ‹index_mut_back5 = Std.Array.set (index_mut_back i24) 1#usize›
    simp only [set8_eq, set67_eq, set5_eq, set0_eq]; exact hi_def.symm
  rw [hlo_eq, hhi_eq]
  -- Step: montgomery_mul lo constants.R → lo5
  let* ⟨ lo5, lo5_post1, lo5_post2, lo5_post3 ⟩ ← montgomery_mul_spec
  · intro j hj
    have h_Rj_bounds : constants.R[j]!.val < 2 ^ 52 := constants.R_limbs_lt j hj
    have := hlo52 j hj; omega
  · exact mul_lt_mul' (le_of_lt (Scalar52_as_Nat_bounded _ hlo52))
      constants.R_value_lt_L (Nat.zero_le _) (by norm_num [show R = 2^260 from rfl])
  -- Step: montgomery_mul hi constants.RR → hi5
  let* ⟨ hi5, hi5_post1, hi5_post2, hi5_post3 ⟩ ← montgomery_mul_spec
  · intro j hj
    have h_RRj_bounds : constants.RR[j]!.val < 2 ^ 52 := constants.RR_limbs_lt j hj
    have := hhi52 j hj; omega
  · exact mul_lt_mul' (le_of_lt (Scalar52_as_Nat_bounded _ hhi52))
      constants.RR_value_lt_L (Nat.zero_le _) (by norm_num [show R = 2^260 from rfl])
  -- Step: add hi5 lo5 → u
  let* ⟨ u, u_post1, u_post2, u_post3 ⟩ ← add_spec
  refine ⟨?_, u_post2, u_post3⟩
  -- Bit-slicing: lo + hi * R = words_wide_as_Nat words1 = U8x64_as_Nat b
  have hslice : Scalar52_as_Nat lo + Scalar52_as_Nat hi * R = U8x64_as_Nat b := by
    rw [← words1_post, lo_def, hi_def]
    unfold Scalar52_as_Nat words_wide_as_Nat
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    simp only [↓Array.getElem!_Nat_set_eq, ↓Array.getElem!_Nat_set_ne,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, OfNat.ofNat_ne_zero, one_ne_zero,
      Nat.succ_ne_self, Array.length, List.Vector.length_val, Nat.ofNat_pos, and_self,
      Nat.reduceLT, Nat.lt_add_one, UScalar.ofNatCore_val_eq,
      UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      i22_eq, i24_val, i41_post1,
      i6_post, i11_post, i16_post, i21_post,
      i28_post, i33_post, i38_post,
      i1_post, i4_post, i9_post, i14_post, i19_post,
      i26_post, i31_post, i36_post,
      ← Array.getElem!_Nat_eq]
    simp only [Nat.reduceMul, pow_zero, one_mul, show R = 2 ^ 260 from rfl]
    have := bit_slicing_wide words1[0]! words1[1]! words1[2]! words1[3]!
      words1[4]! words1[5]! words1[6]! words1[7]!
    omega
  -- Montgomery cancellation chain: u ≡ U8x64_as_Nat b [MOD L]
  have hcoprime : L.gcd R = 1 :=
    Nat.Coprime.pow_right 260 (by decide : Nat.Coprime L 2)
  have hR : Scalar52_as_Nat constants.R ≡ R [MOD L] := by
    rw [Nat.ModEq]; exact constants.R_spec
  have hRR : Scalar52_as_Nat constants.RR ≡ R ^ 2 [MOD L] := by
    rw [Nat.ModEq]; exact constants.RR_spec
  have hloR : Scalar52_as_Nat lo * R ≡ Scalar52_as_Nat lo5 * R [MOD L] :=
    (Nat.ModEq.mul_left _ hR).symm.trans lo5_post1
  have hlo  : Scalar52_as_Nat lo ≡ Scalar52_as_Nat lo5 [MOD L] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime hloR
  have hhiR2 : Scalar52_as_Nat hi * R ^ 2 ≡ Scalar52_as_Nat hi5 * R [MOD L] :=
    (Nat.ModEq.mul_left _ hRR).symm.trans hi5_post1
  have hhiR : Scalar52_as_Nat hi * R ≡ Scalar52_as_Nat hi5 [MOD L] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime
      (show Scalar52_as_Nat hi * R * R ≡ Scalar52_as_Nat hi5 * R [MOD L] by
        rwa [show Scalar52_as_Nat hi * R * R = Scalar52_as_Nat hi * R ^ 2 from by ring])
  have hu_congr : Scalar52_as_Nat u ≡ U8x64_as_Nat b [MOD L] :=
    calc Scalar52_as_Nat u
        ≡ Scalar52_as_Nat hi5 + Scalar52_as_Nat lo5 [MOD L] := u_post1
      _ ≡ Scalar52_as_Nat hi * R + Scalar52_as_Nat lo [MOD L] :=
            Nat.ModEq.add hhiR.symm hlo.symm
      _ = Scalar52_as_Nat lo + Scalar52_as_Nat hi * R := by omega
      _ = U8x64_as_Nat b := hslice
  rwa [Nat.ModEq, Nat.mod_eq_of_lt u_post2] at hu_congr

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
