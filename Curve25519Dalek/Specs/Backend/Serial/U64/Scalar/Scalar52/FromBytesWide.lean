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

/-! ## Part 1: Loop spec — byte packing (64 bytes → 8 words) -/

/-- LE value of 8 consecutive bytes at position `8*j`
in a 64-byte array. -/
abbrev word_of_bytes_64
    (bytes : Array U8 64#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8,
    bytes[8 * j + k]!.val * 2 ^ (8 * k)

set_option maxHeartbeats 400000 in -- heavy steps
/-- **Loop spec**: Each iteration packs 8 bytes into one
U64 word. After the loop, `words[j] = word_of_bytes_64 bytes j`
for all `j < 8`. -/
theorem from_bytes_wide_loop_helper
    (bytes : Array U8 64#usize)
    (words : Array U64 8#usize) (i : Usize)
    (hi : i.val ≤ 8)
    (h_prev : ∀ j, j < i.val →
      words[j]!.val = word_of_bytes_64 bytes j) :
    from_bytes_wide_loop bytes words i ⦃ words' =>
      ∀ j, j < 8 →
        words'[j]!.val = word_of_bytes_64 bytes j ⦄ := by
  sorry

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
  sorry

/-- Loop spec with `words_wide_as_Nat` postcondition. -/
@[step]
theorem from_bytes_wide_loop_spec
    (bytes : Array U8 64#usize)
    (words : Array U64 8#usize)
    (i : Usize) (hi : i.val ≤ 8)
    (h_prev : ∀ j, j < i.val →
      words[j]!.val = word_of_bytes_64 bytes j) :
    from_bytes_wide_loop bytes words i ⦃ words' =>
      words_wide_as_Nat words' =
        U8x64_as_Nat bytes ⦄ := by
  apply spec_mono
    (from_bytes_wide_loop_helper bytes words i hi h_prev)
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
