/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
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

set_option linter.style.whitespace false

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-- LE value of 8 consecutive bytes at position `8*j`
in a 64-byte array. -/
abbrev word_of_bytes_64
    (bytes : Array U8 64#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8,
    bytes[8 * j + k]!.val * 2 ^ (8 * k)

-- TODO: move to Aux.lean if not already present there
/-- Setting index `j` then looking up index `j` via `getElem!` returns the set value. -/
private theorem set_getElem!_self {n : Usize} (a : Std.Array U64 n)
    (j : Usize) (v : U64) (hj : j.val < n.val) :
    (a.set j v)[j.val]! = v := by
  simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
  rw [getElem!_pos _ _ (by simp only [List.length_set, List.Vector.length_val]; omega),
      List.getElem_set_self (by simp only [List.length_set, List.Vector.length_val]; omega)]

/-- Looking up index `k ≠ j` after setting index `j` returns the original value. -/
private theorem set_getElem!_ne {n : Usize} (a : Std.Array U64 n)
    (j : Usize) (v : U64) (k : Nat) (hk : k < n.val) (hne : k ≠ j.val) :
    (a.set j v)[k]! = a[k]! := by
  simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
  rw [getElem!_pos _ _ (by simp only [List.length_set, List.Vector.length_val]; omega),
      getElem!_pos _ _ (by simp only [List.Vector.length_val]; omega)]
  exact List.getElem_set_ne hne.symm (by simp [List.length_set, List.Vector.length_val]; omega)

/-! ## Part 1: Loop spec — byte packing (64 bytes → 8 words) -/

set_option maxHeartbeats 800000 in -- heavy steps
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
        have h53 : i53 = i47 := by rw [i53_post, words7_post]; agrind
        have h46 : i46 = i40 := by rw [i46_post, words6_post]; agrind
        have h39 : i39 = i33 := by rw [i39_post, words5_post]; agrind
        have h32 : i32 = i26 := by rw [i32_post, words4_post]; agrind
        have h25 : i25 = i19 := by rw [i25_post, words3_post]; agrind
        have h18 : i18 = i12 := by rw [i18_post, words2_post]; agrind
        have h11 : i11 = i6  := by rw [i11_post, words1_post]; agrind
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
        simp only [words7_post, words6_post, words5_post, words4_post,
          words3_post, words2_post, words1_post,
          Array.getElem!_Nat_eq, Array.set_val_eq, List.set_set]
        have h_ji : j < i.val := by omega
        grind only [usr ScalarTac.IScalar.bounds,
          = List.getElem!_set_ne, =_ Array.getElem!_Nat_eq]
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

/-! ## Part 3: Main spec -/

set_option maxHeartbeats 800000 in -- heavy steps
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
  unfold from_bytes_wide
  -- Step through loop + mask computation
  let* ⟨ words1, words1_post ⟩ ← from_bytes_wide_loop_spec
  · intro j h hj;
    simp only [Array.getElem!_Nat_eq, Array.repeat_val, UScalar.ofNatCore_val_eq,
      List.reduceReplicate]
    agrind
  let* ⟨ i, i_post1, i_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ mask, mask_post1, mask_post2 ⟩ ← U64.sub_spec
  -- Eliminate index_mut wrappers (10 calls for lo + hi)
  simp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize, bind_assoc_eq,
    bind_tc_ok]
  -- Step through all remaining fast operations
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i2, i2_post1, i2_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post1, i5_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i6, i6_post1, i6_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i8, i8_post1, i8_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i9, i9_post ⟩ ← Array.index_usize_spec
  let* ⟨ i10, i10_post1, i10_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i11, i11_post1, i11_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i12, i12_post1, i12_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i13, i13_post1, i13_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
  let* ⟨ i15, i15_post1, i15_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i16, i16_post1, i16_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i17, i17_post1, i17_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i18, i18_post1, i18_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i19, i19_post ⟩ ← Array.index_usize_spec
  let* ⟨ i20, i20_post1, i20_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i21, i21_post1, i21_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i22, i22_post1, i22_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i23, i23_post1, i23_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i24, i24_post1, i24_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i25, i25_post1, i25_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i26, i26_post ⟩ ← Array.index_usize_spec
  let* ⟨ i27, i27_post1, i27_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i28, i28_post1, i28_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i29, i29_post1, i29_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i30, i30_post1, i30_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i31, i31_post ⟩ ← Array.index_usize_spec
  let* ⟨ i32, i32_post1, i32_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i33, i33_post1, i33_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i34, i34_post1, i34_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i35, i35_post1, i35_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i36, i36_post ⟩ ← Array.index_usize_spec
  let* ⟨ i37, i37_post1, i37_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i38, i38_post1, i38_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i39, i39_post1, i39_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i40, i40_post ⟩ ← IScalar.hcast.step_spec
  let* ⟨ ⟩ ← massert_spec
  · rw [i40_post]; decide
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ←
    U64.ShiftRight_IScalar_spec
  -- Shared mask computation
  have hmask : mask.val = 2 ^ 52 - 1 := by scalar_tac
  -- Element extraction simp set (reused below)
  -- lo limbs < 2^52 (needed for montgomery_mul + final)
  have hlo52 : ∀ j < 5,
      (((((Std.Array.set ZERO 0#usize i2).set 1#usize i7).set 2#usize i12).set 3#usize i17).set
        4#usize i22)[j]!.val < 2 ^ 52 := by
    simp only [UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod]
      at i2_post1 i7_post1 i12_post1 i17_post1 i22_post1
    intro j hj; interval_cases j <;>
      simp only [↓Array.getElem!_Nat_set_ne, ↓Array.getElem!_Nat_set_eq,
        UScalar.ofNatCore_val_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true, OfNat.ofNat_ne_zero,
        one_ne_zero, Nat.succ_ne_self, Array.length, List.Vector.length_val, Nat.ofNat_pos,
        and_self, Nat.reduceLT, Nat.lt_add_one] <;> omega
  -- hi limbs < 2^52
  have hhi52 : ∀ j < 5, (((((Std.Array.set ZERO 0#usize i24).set 1#usize i29).set 2#usize i34).set
    3#usize i39).set 4#usize i41)[j]!.val < 2 ^ 52 := by
    simp only [UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod]
        at i24_post1 i29_post1 i34_post1 i39_post1
    simp only [Nat.shiftRight_eq_div_pow] at i41_post1
    intro j hj; interval_cases j <;>
      simp only [↓Array.getElem!_Nat_set_ne, ↓Array.getElem!_Nat_set_eq, UScalar.ofNatCore_val_eq,
        ne_eq, Nat.reduceEqDiff, not_false_eq_true, OfNat.ofNat_ne_zero, one_ne_zero,
        Nat.succ_ne_self, Array.length, List.Vector.length_val, Nat.ofNat_pos, and_self,
        Nat.reduceLT, Nat.lt_add_one] <;> agrind
  let* ⟨ lo5, lo5_post1, lo5_post2, lo5_post3 ⟩ ← montgomery_mul_spec
  · intro j hj
    have h_Rj_bounds : constants.R[j]!.val < 2 ^ 52 := by exact constants.R_limbs_lt j hj
    omega
  · exact mul_lt_mul' (le_of_lt (Scalar52_as_Nat_bounded _ hlo52))
      constants.R_value_lt_L (Nat.zero_le _) (by unfold R; positivity)
  let* ⟨ hi5, hi5_post1, hi5_post2, hi5_post3 ⟩ ← montgomery_mul_spec
  · intro j hj
    have h_RRj_bounds : constants.RR[j]!.val < 2 ^ 52 := by exact constants.RR_limbs_lt j hj
    omega
  · exact mul_lt_mul' (le_of_lt (Scalar52_as_Nat_bounded _ hhi52))
      constants.RR_value_lt_L (Nat.zero_le _) (by unfold R; positivity)
  let* ⟨ u, u_post1, u_post2, u_post3 ⟩ ← add_spec
  -- Final postcondition
  refine ⟨?_, u_post2, u_post3⟩
  -- Need: Scalar52_as_Nat u = U8x64_as_Nat b % L
  -- Chain: u ≡ hi5 + lo5 [MOD L]  (u_post1)
  --   lo5 ≡ lo [MOD L]            (from lo5_post1 + R_spec)
  --   hi5 ≡ hi * R [MOD L]        (from hi5_post1 + RR_spec)
  --   hi*R + lo = N                (bit-slicing identity)
  --   N = U8x64_as_Nat b          (words1_post)
  sorry


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
