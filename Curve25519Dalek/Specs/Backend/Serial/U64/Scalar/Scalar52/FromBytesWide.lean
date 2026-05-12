/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
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
2. `bit_slicing_wide`: the 5+5 half-limbs (extracted via shift/OR/mask)
   reconstruct the same 512-bit value. Proved by a single OR-split
   primitive `or_split_at` applied 7 times, plus `omega`.
3. Main spec combines lo + hi via Montgomery reduction modulo L,
   using `R = 2^260 mod L` and `RR = R^2 mod L`.
-/

set_option exponentiation.threshold 260

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-! ## Part 1: Loop spec — byte packing (64 bytes → 8 words) -/

/-- LE value of 8 consecutive bytes at position `8*j` in a 64-byte array. -/
abbrev word_of_bytes_64 (bytes : Array U8 64#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8, bytes[8 * j + k]!.val * 2 ^ (8 * k)

set_option maxHeartbeats 1500000 in -- heavy step
/-- **Loop spec**: Each iteration packs 8 bytes into one U64 word.
After the loop, `words[j] = word_of_bytes_64 bytes j` for all `j < 8`. -/
theorem from_bytes_wide_loop_helper
    (bytes : Array U8 64#usize) (words : Array U64 8#usize) (i : Usize) (hi : i.val ≤ 8)
    (h_prev : ∀ j, j < i.val → words[j]!.val = word_of_bytes_64 bytes j)
    (h_zero : ∀ j, i.val ≤ j → j < 8 → words[j]!.val = 0) :
    from_bytes_wide_loop bytes words i ⦃ words' =>
      ∀ j, j < 8 → words'[j]!.val = word_of_bytes_64 bytes j ⦄ := by
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
    step*
    · -- h_prev for next iteration: index i is freshly written
      subst a_post; intro j hj
      by_cases heq : j = i.val
      · subst heq
        simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
        rw [getElem!_pos _ _ (by simp only [List.length_set, List.Vector.length_val,
              UScalar.ofNatCore_val_eq]; omega),
            List.getElem_set_self (by simp only [List.length_set, List.Vector.length_val,
              UScalar.ofNatCore_val_eq]; omega)]
        -- Collapse the read-modify-write lookups to the OR-chain over u8s
        have h53 : i53 = i47 := by rw [i53_post, words7_post]; agrind
        have h46 : i46 = i40 := by rw [i46_post, words6_post]; agrind
        have h39 : i39 = i33 := by rw [i39_post, words5_post]; agrind
        have h32 : i32 = i26 := by rw [i32_post, words4_post]; agrind
        have h25 : i25 = i19 := by rw [i25_post, words3_post]; agrind
        have h18 : i18 = i12 := by rw [i18_post, words2_post]; agrind
        have h11 : i11 = i6  := by rw [i11_post, words1_post]; agrind
        simp (discharger := omega) only [h53, h46, h39, h32, h25, h18, h11,
          i54_post1, i47_post1, i40_post1, i33_post1, i26_post1, i19_post1, i12_post1, i6_post1,
          UScalar.val_or, UScalar.cast_val_eq, u8_val_mod_u64_numBits, Nat.shiftLeft_eq,
          u8_mul_pow_mod_u64, i3_post, i9_post, i15_post, i22_post, i29_post, i36_post, i43_post,
          i50_post, i4_post1, i10_post1, i17_post1, i24_post1, i31_post1, i38_post1, i45_post1,
          i52_post1, i2_post, i1_post, i5_post]
        simp only [pow_zero, mul_one, Int.reduceMul, Int.reduceToNat,
          i8_post, i7_post, i14_post, i13_post, i16_post, i21_post, i20_post, i23_post, i28_post,
          i27_post, i30_post, i35_post, i34_post, i37_post, i42_post, i41_post, i44_post, i49_post,
          i48_post, i51_post]
        have hzero : (↑(↑words : List.Vector U64 8)[i.val]! : Nat) = 0 := by
          rw [Array.getElem!_Nat_eq]; agrind
        rw [← Array.getElem!_Nat_eq, hzero]; simp only [Nat.zero_or, i1_post]
        rw [or_bytes_eq_sum _ _ _ _ _ _ _ _
          (bytes.val[i.val * 8]!).hmax (bytes.val[i.val * 8 + 1]!).hmax
          (bytes.val[i.val * 8 + 2]!).hmax (bytes.val[i.val * 8 + 3]!).hmax
          (bytes.val[i.val * 8 + 4]!).hmax (bytes.val[i.val * 8 + 5]!).hmax
          (bytes.val[i.val * 8 + 6]!).hmax (bytes.val[i.val * 8 + 7]!).hmax]
        simp only [word_of_bytes_64, Finset.sum_range_succ, Finset.range_zero,
          Finset.sum_empty, zero_add, Array.getElem!_Nat_eq]; ring_nf
      · simp only [words7_post, words6_post, words5_post, words4_post, words3_post,
          words2_post, words1_post, Array.getElem!_Nat_eq, Array.set_val_eq, List.set_set]
        grind only [usr ScalarTac.IScalar.bounds, = List.getElem!_set_ne, =_ Array.getElem!_Nat_eq]
    · -- h_zero for next iteration
      subst a_post; intro j hge hlt
      have hne : j ≠ i.val := by omega
      simp only [words7_post, words6_post, words5_post, words4_post, words3_post,
        words2_post, words1_post, Array.getElem!_Nat_eq, Array.set_val_eq, List.set_set]
      grind only [usr ScalarTac.IScalar.bounds, = List.getElem!_set_ne, =_ Array.getElem!_Nat_eq]

/-- Interpret 8 LE U64 words as a natural number. -/
def words_wide_as_Nat (words : Array U64 8#usize) : Nat :=
  ∑ j ∈ Finset.range 8, words[j]!.val * 2 ^ (64 * j)

/-- Bridge: `words_wide_as_Nat = U8x64_as_Nat`. Each U64 word is a sum of 8 bytes,
so a sum of 8 words is a flat sum of 64 bytes (by re-indexing). -/
theorem words_wide_eq_bytes
    (b : Array U8 64#usize)
    (words : Array U64 8#usize)
    (h : ∀ j, j < 8 → words[j]!.val = word_of_bytes_64 b j) :
    words_wide_as_Nat words = U8x64_as_Nat b := by
  -- First rewrite via `h` and unfold both sides.
  have hsum : ∀ t, t ≤ 8 →
      (∑ j ∈ Finset.range t, word_of_bytes_64 b j * 2 ^ (64 * j))
        = ∑ i ∈ Finset.range (8 * t), 2 ^ (8 * i) * b[i]!.val := by
    intro t _; induction t with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih (by omega),
          show 8 * (n + 1) = 8 * n + 8 from by ring, Finset.sum_range_add]
      refine congrArg _ ?_
      simp only [word_of_bytes_64, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show 8 * (8 * n + k) = 8 * k + 64 * n from by ring, Nat.pow_add]; ring
  simp only [words_wide_as_Nat, U8x64_as_Nat]
  calc ∑ j ∈ Finset.range 8, words[j]!.val * 2 ^ (64 * j)
      = ∑ j ∈ Finset.range 8, word_of_bytes_64 b j * 2 ^ (64 * j) :=
        Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]
    _ = ∑ i ∈ Finset.range 64, 2 ^ (8 * i) * b[i]!.val := hsum 8 le_rfl

/-- Loop spec with `words_wide_as_Nat` postcondition. -/
@[step]
theorem from_bytes_wide_loop_spec
    (bytes : Array U8 64#usize) (words : Array U64 8#usize) (i : Usize) (hi : i.val ≤ 8)
    (h_prev : ∀ j, j < i.val → words[j]!.val = word_of_bytes_64 bytes j)
    (h_zero : ∀ j, i.val ≤ j → j < 8 → words[j]!.val = 0) :
    from_bytes_wide_loop bytes words i ⦃ words' =>
      words_wide_as_Nat words' = U8x64_as_Nat bytes ⦄ :=
  spec_mono (from_bytes_wide_loop_helper bytes words i hi h_prev h_zero)
    (fun _ hpost => words_wide_eq_bytes _ _ hpost)

/-! ## Part 2: Bit-slicing identities via small primitives

A single "complementary shift OR" primitive `or_split_at` handles every
`(a / 2^p) ||| (b * 2^(64-p) % U64.size)` pattern; the combined identity
`bit_slicing_wide` follows by `omega`. -/

/-- Combined identity: `lo + hi * 2^260 = words_wide`. Each `lo_k` / `hi_k`
limb expression collapses to a small div/mod sum via `or_split_at`, and the
whole equation is linear after that. -/
theorem bit_slicing_wide (w0 w1 w2 w3 w4 w5 w6 w7 : U64) :
    (w0.val % 2 ^ 52
     + (((w0.val / 2 ^ 52) ||| ((w1.val * 2 ^ 12) % U64.size)) % 2 ^ 52) * 2 ^ 52
     + (((w1.val / 2 ^ 40) ||| ((w2.val * 2 ^ 24) % U64.size)) % 2 ^ 52) * 2 ^ 104
     + (((w2.val / 2 ^ 28) ||| ((w3.val * 2 ^ 36) % U64.size)) % 2 ^ 52) * 2 ^ 156
     + (((w3.val / 2 ^ 16) ||| ((w4.val * 2 ^ 48) % U64.size)) % 2 ^ 52) * 2 ^ 208)
    + ((w4.val / 2 ^ 4) % 2 ^ 52
       + (((w4.val / 2 ^ 56) ||| ((w5.val * 2 ^ 8) % U64.size)) % 2 ^ 52) * 2 ^ 52
       + (((w5.val / 2 ^ 44) ||| ((w6.val * 2 ^ 20) % U64.size)) % 2 ^ 52) * 2 ^ 104
       + (((w6.val / 2 ^ 32) ||| ((w7.val * 2 ^ 32) % U64.size)) % 2 ^ 52) * 2 ^ 156
       + (w7.val / 2 ^ 20) * 2 ^ 208) * 2 ^ 260
    = w0.val + w1.val * 2 ^ 64 + w2.val * 2 ^ 128 + w3.val * 2 ^ 192
      + w4.val * 2 ^ 256 + w5.val * 2 ^ 320 + w6.val * 2 ^ 384
      + w7.val * 2 ^ 448 := by
  rw [or_split_at w0 w1 52 (by omega), or_split_at w1 w2 40 (by omega),
      or_split_at w2 w3 28 (by omega), or_split_at w3 w4 16 (by omega),
      or_split_at w4 w5 56 (by omega), or_split_at w5 w6 44 (by omega),
      or_split_at w6 w7 32 (by omega)]
  have hU : U64.size = 2 ^ 64 := by scalar_tac
  have b0 := hU ▸ w0.hmax; have b1 := hU ▸ w1.hmax
  have b2 := hU ▸ w2.hmax; have b3 := hU ▸ w3.hmax
  have b4 := hU ▸ w4.hmax; have b5 := hU ▸ w5.hmax
  have b6 := hU ▸ w6.hmax; have b7 := hU ▸ w7.hmax
  have d0 := Nat.div_add_mod w0.val (2 ^ 52)
  have d1 := Nat.div_add_mod w1.val (2 ^ 40)
  have d2 := Nat.div_add_mod w2.val (2 ^ 28)
  have d3 := Nat.div_add_mod w3.val (2 ^ 16)
  have d4 := Nat.div_add_mod w4.val (2 ^ 4)
  have d5 := Nat.div_add_mod w5.val (2 ^ 56)
  have d6 := Nat.div_add_mod w6.val (2 ^ 44)
  have d7 := Nat.div_add_mod w7.val (2 ^ 32)
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
  let* ⟨ words1, words1_post ⟩ ← from_bytes_wide_loop_spec
  · intro j h hj;
    simp only [Array.getElem!_Nat_eq, Array.repeat_val, UScalar.ofNatCore_val_eq,
      List.reduceReplicate]
    agrind
  let* ⟨ i, i_post1, i_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ mask, mask_post1, mask_post2 ⟩ ← U64.sub_spec
  simp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize, bind_assoc_eq,
    bind_tc_ok]
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
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  have hmask : mask.val = 2 ^ 52 - 1 := by scalar_tac
  -- lo limbs < 2^52
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
  · intro j hj; have := constants.R_limbs_lt j hj; omega
  · exact mul_lt_mul' (Scalar52_as_Nat_bounded _ hlo52).le
      constants.R_value_lt_L (Nat.zero_le _) (by unfold R; positivity)
  let* ⟨ hi5, hi5_post1, hi5_post2, hi5_post3 ⟩ ← montgomery_mul_spec
  · intro j hj; have := constants.RR_limbs_lt j hj; omega
  · exact mul_lt_mul' (Scalar52_as_Nat_bounded _ hhi52).le
      constants.RR_value_lt_L (Nat.zero_le _) (by unfold R; positivity)
  let* ⟨ u, u_post1, u_post2, u_post3 ⟩ ← add_spec
  refine ⟨?_, u_post2, u_post3⟩
  set lo := (((((Std.Array.set ZERO 0#usize i2).set 1#usize i7).set 2#usize i12).set
    3#usize i17).set 4#usize i22) with lo_def
  set hi := (((((Std.Array.set ZERO 0#usize i24).set 1#usize i29).set 2#usize i34).set
    3#usize i39).set 4#usize i41) with hi_def
  -- Bit-slicing identity: lo + hi * R = words_wide = U8x64_as_Nat b
  have hslice : Scalar52_as_Nat lo + Scalar52_as_Nat hi * R = U8x64_as_Nat b := by
    rw [← words1_post, lo_def, hi_def]
    unfold Scalar52_as_Nat words_wide_as_Nat
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    simp only [↓Array.getElem!_Nat_set_eq, ↓Array.getElem!_Nat_set_ne, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true, OfNat.ofNat_ne_zero, one_ne_zero, Nat.succ_ne_self, Array.length,
      List.Vector.length_val, Nat.ofNat_pos, and_self, Nat.reduceLT, Nat.lt_add_one,
      UScalar.ofNatCore_val_eq, UScalar.val_and, UScalar.val_or, hmask,
      land_pow_two_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      i2_post1, i7_post1, i12_post1, i17_post1, i22_post1, i24_post1, i29_post1, i34_post1,
      i39_post1, i6_post1, i11_post1, i16_post1, i21_post1, i28_post1, i33_post1, i38_post1,
      i3_post1, i8_post1, i13_post1, i18_post1, i23_post1, i25_post1, i30_post1, i35_post1,
      i5_post1, i10_post1, i15_post1, i20_post1, i27_post1, i32_post1, i37_post1, i41_post1,
      i1_post, i4_post, i9_post, i14_post, i19_post, i26_post, i31_post, i36_post,
      ← Array.getElem!_Nat_eq]
    simp only [Nat.reduceMul, pow_zero, one_mul, show R = 2 ^ 260 from rfl]
    have := bit_slicing_wide words1[0]! words1[1]! words1[2]! words1[3]!
      words1[4]! words1[5]! words1[6]! words1[7]!
    omega
  -- Congruence chain: u ≡ hi5 + lo5 ≡ hi * R + lo ≡ lo + hi * R ≡ U8x64_as_Nat b [MOD L]
  have hcoprime : L.gcd R = 1 :=
    Nat.Coprime.pow_right 260 (by decide : Nat.Coprime L 2)
  have hlo : Scalar52_as_Nat lo ≡ Scalar52_as_Nat lo5 [MOD L] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime
      ((Nat.ModEq.mul_left _ constants.R_spec).symm.trans lo5_post1)
  have hhiR : Scalar52_as_Nat hi * R ≡ Scalar52_as_Nat hi5 [MOD L] :=
    Nat.ModEq.cancel_right_of_coprime hcoprime <| by
      rw [show Scalar52_as_Nat hi * R * R = Scalar52_as_Nat hi * R ^ 2 from by ring]
      exact (Nat.ModEq.mul_left _ constants.RR_spec).symm.trans hi5_post1
  have hu_congr : Scalar52_as_Nat u ≡ U8x64_as_Nat b [MOD L] :=
    calc Scalar52_as_Nat u
        ≡ Scalar52_as_Nat hi5 + Scalar52_as_Nat lo5 [MOD L] := u_post1
      _ ≡ Scalar52_as_Nat hi * R + Scalar52_as_Nat lo [MOD L] :=
          Nat.ModEq.add hhiR.symm hlo.symm
      _ = U8x64_as_Nat b := by rw [← hslice]; ring
  rwa [Nat.ModEq, Nat.mod_eq_of_lt u_post2] at hu_congr


end curve25519_dalek.backend.serial.u64.scalar.Scalar52
