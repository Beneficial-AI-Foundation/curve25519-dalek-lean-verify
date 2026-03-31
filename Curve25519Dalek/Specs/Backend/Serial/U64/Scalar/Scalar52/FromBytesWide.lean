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

/-! ## Part 1a: One-iteration byte-packing helper -/

set_option maxHeartbeats 400000 in -- heavy simps
/-- One iteration of the inner loop packs 8 bytes into a U64 word.
After 8 read-shift-OR-update steps all writing to the same index `i`,
the final value at that index equals `word_of_bytes_64 bytes i`. -/
private theorem pack_word_eq_word_of_bytes_64
    (bytes : Array U8 64#usize)
    (words : Array U64 8#usize) (i : Usize)
    (hlt : i.val < 8)
    (hzero : words[i.val]!.val = 0)
    -- byte 0
    (i1 : Usize) (i1_post : i1.val = i.val * 8)
    (i2 : U8) (i2_post : i2 = (↑bytes)[i1.val]!)
    (i3 : U64) (i3_post : i3 = UScalar.cast .U64 i2)
    (i4 : U64) (i4_post1 : i4.val = i3.val <<< 0 % U64.size)
    (i5 : U64) (i5_post : i5 = (↑words)[i.val]!)
    (i6 : U64) (i6_post1 : i6.val = (i5 ||| i4).val)
    -- byte 1
    (i9 : U64) (i9_post : i9 = UScalar.cast .U64 (↑bytes)[i1.val + 1]!)
    (i10 : U64) (i10_post1 : i10.val = i9.val <<< 8 % U64.size)
    (i11 : U64) (i11_post : i11 = (↑(words.set i i6))[i.val]!)
    (i12 : U64) (i12_post1 : i12.val = (i11 ||| i10).val)
    -- byte 2
    (i15 : U64) (i15_post : i15 = UScalar.cast .U64 (↑bytes)[i1.val + 2]!)
    (i17 : U64) (i17_post1 : i17.val = i15.val <<< 16 % U64.size)
    (i18 : U64) (i18_post : i18 = (↑((words.set i i6).set i i12))[i.val]!)
    (i19 : U64) (i19_post1 : i19.val = (i18 ||| i17).val)
    -- byte 3
    (i22 : U64) (i22_post : i22 = UScalar.cast .U64 (↑bytes)[i1.val + 3]!)
    (i24 : U64) (i24_post1 : i24.val = i22.val <<< 24 % U64.size)
    (i25 : U64) (i25_post : i25 = (↑(((words.set i i6).set i i12).set i i19))[i.val]!)
    (i26 : U64) (i26_post1 : i26.val = (i25 ||| i24).val)
    -- byte 4
    (i29 : U64) (i29_post : i29 = UScalar.cast .U64 (↑bytes)[i1.val + 4]!)
    (i31 : U64) (i31_post1 : i31.val = i29.val <<< 32 % U64.size)
    (i32 : U64) (i32_post : i32 = (↑((((words.set i i6).set i i12).set i i19).set i i26))[i.val]!)
    (i33 : U64) (i33_post1 : i33.val = (i32 ||| i31).val)
    -- byte 5
    (i36 : U64) (i36_post : i36 = UScalar.cast .U64 (↑bytes)[i1.val + 5]!)
    (i38 : U64) (i38_post1 : i38.val = i36.val <<< 40 % U64.size)
    (i39 : U64) (i39_post : i39 = (↑(((((words.set i i6).set i i12).set i i19).set i i26).set i i33))[i.val]!)
    (i40 : U64) (i40_post1 : i40.val = (i39 ||| i38).val)
    -- byte 6
    (i43 : U64) (i43_post : i43 = UScalar.cast .U64 (↑bytes)[i1.val + 6]!)
    (i45 : U64) (i45_post1 : i45.val = i43.val <<< 48 % U64.size)
    (i46 : U64) (i46_post : i46 = (↑((((((words.set i i6).set i i12).set i i19).set i i26).set i i33).set i i40))[i.val]!)
    (i47 : U64) (i47_post1 : i47.val = (i46 ||| i45).val)
    -- byte 7
    (i50 : U64) (i50_post : i50 = UScalar.cast .U64 (↑bytes)[i1.val + 7]!)
    (i52 : U64) (i52_post1 : i52.val = i50.val <<< 56 % U64.size)
    (i53 : U64) (i53_post : i53 = (↑(((((((words.set i i6).set i i12).set i i19).set i i26).set i i33).set i i40).set i i47))[i.val]!)
    (i54 : U64) (i54_post1 : i54.val = (i53 ||| i52).val) :
    i54.val = word_of_bytes_64 bytes i.val := by
  -- Phase 1: collapse read-modify-write lookups via set_getElem!_self
  have h53 : i53 = i47 := by rw [i53_post]; exact set_getElem!_self _ _ _ (by agrind)
  have h46 : i46 = i40 := by rw [i46_post]; exact set_getElem!_self _ _ _ (by agrind)
  have h39 : i39 = i33 := by rw [i39_post]; exact set_getElem!_self _ _ _ (by agrind)
  have h32 : i32 = i26 := by rw [i32_post]; exact set_getElem!_self _ _ _ (by agrind)
  have h25 : i25 = i19 := by rw [i25_post]; exact set_getElem!_self _ _ _ (by agrind)
  have h18 : i18 = i12 := by rw [i18_post]; exact set_getElem!_self _ _ _ (by agrind)
  have h11 : i11 = i6  := by rw [i11_post]; exact set_getElem!_self _ _ _ (by agrind)
  -- Phase 2: expand OR chain to Nat arithmetic
  simp (discharger := omega) only [h53, h46, h39, h32, h25, h18, h11,
    i54_post1, i47_post1, i40_post1, i33_post1, i26_post1, i19_post1, i12_post1,
    i6_post1, UScalar.val_or, UScalar.cast_val_eq, i3_post, i9_post, i15_post,
    i22_post, i29_post, i36_post, i43_post, i50_post,
    i4_post1, i10_post1, i17_post1, i24_post1, i31_post1, i38_post1, i45_post1,
    i52_post1, u8_val_mod_u64_numBits, Nat.shiftLeft_eq, u8_mul_pow_mod_u64,
    i2_post, i1_post, i5_post]
  -- Eliminate initial zero: words[i] = 0, so 0 ||| x = x
  rw [show (↑(↑words : List.Vector U64 8)[i.val]! : Nat) = 0 from by
    rw [Array.getElem!_Nat_eq]; agrind]
  simp only [Array.getElem!_Nat_eq, pow_zero, mul_one, Nat.zero_or]
  -- Phase 3: OR to sum, expand word_of_bytes_64, close with ring
  rw [or_bytes_eq_sum _ _ _ _ _ _ _ _
    (bytes.val[i.val * 8]!).hmax (bytes.val[i.val * 8 + 1]!).hmax
    (bytes.val[i.val * 8 + 2]!).hmax (bytes.val[i.val * 8 + 3]!).hmax
    (bytes.val[i.val * 8 + 4]!).hmax (bytes.val[i.val * 8 + 5]!).hmax
    (bytes.val[i.val * 8 + 6]!).hmax (bytes.val[i.val * 8 + 7]!).hmax]
  simp only [word_of_bytes_64, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add, Array.getElem!_Nat_eq]
  ring_nf

/-! ## Part 1b: Loop spec — byte packing (64 bytes → 8 words) -/

set_option maxHeartbeats 1000000 in -- heavy steps
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

/-- Bridge: `words_wide_as_Nat = U8x64_as_Nat`. -/
theorem words_wide_eq_bytes
    (b : Array U8 64#usize)
    (words : Array U64 8#usize)
    (h : ∀ j, j < 8 →
      words[j]!.val = word_of_bytes_64 b j) :
    words_wide_as_Nat words = U8x64_as_Nat b := by
  simp only [words_wide_as_Nat, U8x64_as_Nat, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
      h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]
  simp only [word_of_bytes_64, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]

  sorry

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

/-! ## Part 2: Bit-slicing identity (8 words → lo + hi) -/

-- TODO: Define 10 limb abbreviations and prove the
-- splitting identity:
--   Scalar52_as_Nat lo + Scalar52_as_Nat hi * 2^260
--     = words_wide_as_Nat words
-- This generalizes bit_slicing_of_words from FromBytes.lean.

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
