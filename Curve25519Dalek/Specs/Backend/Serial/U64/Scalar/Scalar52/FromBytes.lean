/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
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

1. `from_bytes_loop_helper` / `from_bytes_loop_spec` (`@[step]`):
   Loop packs 32 bytes into 4 U64 words; postcondition:
   `words_as_Nat words = U8x32_as_Nat bytes`.
2. `bit_slicing_of_words`: Pure math — 5 limbs extracted via
   shift/OR/mask from 4 words reconstruct the same value.
3. `slice_state4` / `slice_state4_value`: Bridge predicate
   relating the 5-limb array to `words_as_Nat`.
4. `from_bytes_spec` (`@[step]`): Unfolds `index_mut` wrappers
   via `simp` to avoid CPU explosion from function-typed
   callbacks, then steps through arithmetic and closes via
   `slice_state4_value`.
-/

set_option linter.style.whitespace false

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-- The little-endian value of 8 consecutive bytes starting at position `8*j` in a 32-byte array. -/
abbrev word_of_bytes (bytes : Array U8 32#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8, bytes[8 * j + k]!.val * 2 ^ (8 * k)

/-! ## Part 1: Loop spec — byte packing -/

set_option maxHeartbeats 300000 in -- heavy step
/-- **Loop spec**: Each iteration packs 8 bytes into one U64 word (little-endian).
After the loop completes, `words[j] = word_of_bytes bytes j` for all `j < 4`. -/
theorem from_bytes_loop_helper (bytes : Array U8 32#usize)
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

/-- Interpret 4 little-endian U64 words as a natural number. -/
def words_as_Nat (words : Array U64 4#usize) : Nat :=
  ∑ j ∈ Finset.range 4, words[j]!.val * 2 ^ (64 * j)

/-- The loop output satisfies `words_as_Nat words1 = U8x32_as_Nat b`.
Derived from `from_bytes_loop_helper` by expanding both sides. -/
theorem words_eq_bytes (b : Array U8 32#usize) (words : Array U64 4#usize)
    (h : ∀ j, j < 4 → words[j]!.val = word_of_bytes b j) :
    words_as_Nat words = U8x32_as_Nat b := by
  simp only [words_as_Nat, U8x32_as_Nat, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]
  simp only [word_of_bytes, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  ring

/-- Loop spec with `words_as_Nat` postcondition (used by
`from_bytes_spec`). Derived from `from_bytes_loop_helper`
+ `words_eq_bytes`. -/
@[step]
theorem from_bytes_loop_spec (bytes : Array U8 32#usize)
    (words : Array U64 4#usize) (i : Usize) (hi : i.val ≤ 4)
    (h_prev : ∀ j, j < i.val → words[j]!.val = word_of_bytes bytes j) :
    from_bytes_loop bytes words i ⦃ words' =>
      words_as_Nat words' = U8x32_as_Nat bytes ⦄ := by
  apply spec_mono (from_bytes_loop_helper bytes words i hi h_prev)
  intro words' hpost
  exact words_eq_bytes bytes words' hpost

/-- Pure theorem: the 5 limbs extracted via shift/OR/mask from 4 U64 words
reconstruct the same value as the 4 words. No monadic code.

Each limb is: `(shifted_or_result) &&& mask`, which equals
`(shifted_or_result) % 2^52` via `land_pow_two_sub_one_eq_mod`.
The OR of non-overlapping shifted values equals their sum via `or_mul_pow_two_eq_add`.
After these conversions, `bit_slicing_identity` closes the goal. -/
theorem bit_slicing_of_words (w0 w1 w2 w3 : U64) :
    -- The 5 limbs
    let l0 := w0.val % 2 ^ 52
    let l1 := ((w0.val / 2 ^ 52) ||| ((w1.val * 2 ^ 12) % U64.size)) % 2 ^ 52
    let l2 := ((w1.val / 2 ^ 40) ||| ((w2.val * 2 ^ 24) % U64.size)) % 2 ^ 52
    let l3 := ((w2.val / 2 ^ 28) ||| ((w3.val * 2 ^ 36) % U64.size)) % 2 ^ 52
    let l4 := (w3.val / 2 ^ 16) % 2 ^ 48
    -- Reconstruct value
    l0 + l1 * 2 ^ 52 + l2 * 2 ^ 104 + l3 * 2 ^ 156 + l4 * 2 ^ 208
    = w0.val + w1.val * 2 ^ 64 + w2.val * 2 ^ 128 + w3.val * 2 ^ 192 := by
  -- Get concrete bounds for omega
  have hU : U64.size = 2 ^ 64 := by scalar_tac
  have hw0 : w0.val < 2 ^ 64 := hU ▸ w0.hmax
  have hw1 : w1.val < 2 ^ 64 := hU ▸ w1.hmax
  have hw2 : w2.val < 2 ^ 64 := hU ▸ w2.hmax
  have hw3 : w3.val < 2 ^ 64 := hU ▸ w3.hmax
  -- Simplify shift-left mods: w * 2^k % 2^64 → (w%2^m) * 2^k
  simp only [hU,
    show w1.val * 2 ^ 12 % 2 ^ 64 = (w1.val % 2 ^ 52) * 2 ^ 12 from by omega,
    show w2.val * 2 ^ 24 % 2 ^ 64 = (w2.val % 2 ^ 40) * 2 ^ 24 from by omega,
    show w3.val * 2 ^ 36 % 2 ^ 64 = (w3.val % 2 ^ 28) * 2 ^ 36 from by omega]
  -- Convert OR to add (non-overlapping bit ranges)
  rw [or_mul_pow_two_eq_add _ _ 12 (by omega),
      or_mul_pow_two_eq_add _ _ 24 (by omega),
      or_mul_pow_two_eq_add _ _ 36 (by omega)]
  -- Simplify the outer mods (sums fit in 52/48 bits, so mod is identity)
  -- omega handles each: (a + b + c*2^52) % 2^52 = a + b when a+b < 2^52
  rw [show (w0.val / 2 ^ 52 + (w1.val % 2 ^ 52) * 2 ^ 12) % 2 ^ 52 =
      w0.val / 2 ^ 52 + (w1.val % 2 ^ 40) * 2 ^ 12 from by omega,
    show (w1.val / 2 ^ 40 + (w2.val % 2 ^ 40) * 2 ^ 24) % 2 ^ 52 =
      w1.val / 2 ^ 40 + (w2.val % 2 ^ 28) * 2 ^ 24 from by omega,
    show (w2.val / 2 ^ 28 + (w3.val % 2 ^ 28) * 2 ^ 36) % 2 ^ 52 =
      w2.val / 2 ^ 28 + (w3.val % 2 ^ 16) * 2 ^ 36 from by omega,
    show w3.val / 2 ^ 16 % 2 ^ 48 = w3.val / 2 ^ 16 from by omega]
  exact bit_slicing_identity w0.val w1.val w2.val w3.val

/-- The first 52-bit limb. -/
abbrev limb0_nat (words1 : Array U64 4#usize) : Nat :=
  words1[0]!.val % 2 ^ 52

/-- The second 52-bit limb. -/
abbrev limb1_nat (words1 : Array U64 4#usize) : Nat :=
  ((words1[0]!.val / 2 ^ 52)
    ||| ((words1[1]!.val * 2 ^ 12) % U64.size)) % 2 ^ 52

/-- The third 52-bit limb. -/
abbrev limb2_nat (words1 : Array U64 4#usize) : Nat :=
  ((words1[1]!.val / 2 ^ 40)
    ||| ((words1[2]!.val * 2 ^ 24) % U64.size)) % 2 ^ 52

/-- The fourth 52-bit limb. -/
abbrev limb3_nat (words1 : Array U64 4#usize) : Nat :=
  ((words1[2]!.val / 2 ^ 28)
    ||| ((words1[3]!.val * 2 ^ 36) % U64.size)) % 2 ^ 52

/-- The fifth limb (48-bit, top of the scalar). -/
abbrev limb4_nat (words1 : Array U64 4#usize) : Nat :=
  (words1[3]!.val / 2 ^ 16) % 2 ^ 48

/-- All 5 limbs correctly placed in the output array. -/
def slice_state4 (words1 : Array U64 4#usize)
    (s : Scalar52) : Prop :=
  s[0]!.val = limb0_nat words1 ∧
  s[1]!.val = limb1_nat words1 ∧
  s[2]!.val = limb2_nat words1 ∧
  s[3]!.val = limb3_nat words1 ∧
  s[4]!.val = limb4_nat words1

/-- A scalar satisfying `slice_state4` has the same value
as the packed 4-word input. -/
private theorem slice_state4_value (words1 : Array U64 4#usize) (s : Scalar52)
    (hs : slice_state4 words1 s) :
    Scalar52_as_Nat s = words_as_Nat words1 := by
  obtain ⟨hs0, hs1, hs2, hs3, hs4⟩ := hs
  have hscalar :
      Scalar52_as_Nat s =
        s[0]!.val + s[1]!.val * 2 ^ 52 + s[2]!.val * 2 ^ 104 + s[3]!.val * 2 ^ 156 +
          s[4]!.val * 2 ^ 208 := by
    simp only [Scalar52_as_Nat, Nat.mul_comm, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_mul, pow_zero,
      List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
      Option.getD_some, one_mul, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
      Nat.lt_add_one, getElem!_pos]
  have hwords :
      words_as_Nat words1 =
        words1[0]!.val + words1[1]!.val * 2 ^ 64 + words1[2]!.val * 2 ^ 128 +
          words1[3]!.val * 2 ^ 192 := by
    simp only [words_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.mul_comm,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_mul, pow_zero,
      List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
      Option.getD_some, one_mul, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
      Nat.lt_add_one, getElem!_pos]
  calc
    Scalar52_as_Nat s
        = s[0]!.val + s[1]!.val * 2 ^ 52 + s[2]!.val * 2 ^ 104 + s[3]!.val * 2 ^ 156 +
            s[4]!.val * 2 ^ 208 := hscalar
    _ = limb0_nat words1 + limb1_nat words1 * 2 ^ 52 + limb2_nat words1 * 2 ^ 104 +
          limb3_nat words1 * 2 ^ 156 + limb4_nat words1 * 2 ^ 208 := by
          rw [hs0, hs1, hs2, hs3, hs4]
    _ = words1[0]!.val + words1[1]!.val * 2 ^ 64 + words1[2]!.val * 2 ^ 128 +
          words1[3]!.val * 2 ^ 192 := by
          simpa [limb0_nat, limb1_nat, limb2_nat, limb3_nat, limb4_nat] using
            bit_slicing_of_words words1[0]! words1[1]! words1[2]! words1[3]!
    _ = words_as_Nat words1 := hwords.symm

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
  let* ⟨ words1, words1_post ⟩ ← from_bytes_loop_spec
  let* ⟨ i, i_post1, i_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ mask, mask_post1, mask_post2 ⟩ ← U64.sub_spec
  let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ top_mask, top_mask_post1, top_mask_post2 ⟩ ← U64.sub_spec
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  -- Eliminate index_mut wrappers: converts opaque __discr.2 callbacks to concrete Array.set
  simp only [Insts.CoreOpsIndexIndexMutUsizeU64.index_mut, Array.index_mut_usize,
             bind_assoc_eq, bind_tc_ok]
  -- All remaining ops are fast (no callbacks): index_usize, shift, AND, OR
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i4, i4_post1, i4_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i5, i5_post ⟩ ← Array.index_usize_spec
  let* ⟨ i6, i6_post1, i6_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i8, i8_post1, i8_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i9, i9_post1, i9_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec
  let* ⟨ i11, i11_post1, i11_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i12, i12_post1, i12_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i13, i13_post1, i13_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i14, i14_post1, i14_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ i15, i15_post ⟩ ← Array.index_usize_spec
  let* ⟨ i16, i16_post1, i16_post2 ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ i17, i17_post1, i17_post2 ⟩ ← UScalar.or_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i18, i18_post1, i18_post2 ⟩ ← UScalar.and_spec
  let* ⟨ i19, i19_post1, i19_post2 ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ x, x_post ⟩ ← Array.index_usize_spec
  let* ⟨ i20, i20_post1, i20_post2 ⟩ ← UScalar.and_spec
  -- Compute mask values
  have hmask : mask.val = 2 ^ 52 - 1 := by scalar_tac
  have htop : top_mask.val = 2 ^ 48 - 1 := by scalar_tac
  -- Convert AND → mod for limb postconditions
  simp only [UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod] at i3_post1 i8_post1 i13_post1 i18_post1
  simp only [UScalar.val_and, htop, land_pow_two_sub_one_eq_mod] at i20_post1
  refine ⟨?_, ?_⟩
  · -- Value: Scalar52_as_Nat = U8x32_as_Nat b
    refine (slice_state4_value words1 _ ?_).trans
      words1_post
    unfold slice_state4
    unfold limb0_nat limb1_nat limb2_nat limb3_nat limb4_nat
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [↓Array.getElem!_Nat_set_ne, ↓Array.getElem!_Nat_set_eq, UScalar.ofNatCore_val_eq,
        ne_eq, Nat.reduceEqDiff, not_false_eq_true, OfNat.ofNat_ne_zero, one_ne_zero,
        Nat.succ_ne_self, Array.length, List.Vector.length_val, Nat.ofNat_pos, and_self,
        Nat.reduceLT, Nat.lt_add_one, i3_post1, i8_post1, i13_post1, i18_post1, i20_post1,
        i7_post1, i12_post1, i17_post1, i4_post1, i9_post1, i14_post1, i19_post1, i6_post1,
        i11_post1, i16_post1, i2_post, i5_post, i10_post, i15_post, UScalar.val_or,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Array.getElem!_Nat_eq]
  · -- Bounds: ∀ i < 5, result[i]! < 2^52
    intro idx hidx
    interval_cases idx <;>
      simp only [↓Array.getElem!_Nat_set_ne, ↓Array.getElem!_Nat_set_eq, UScalar.ofNatCore_val_eq,
        ne_eq, Nat.reduceEqDiff, not_false_eq_true, OfNat.ofNat_ne_zero, one_ne_zero,
        Nat.succ_ne_self, Array.length, List.Vector.length_val, Nat.ofNat_pos, and_self,
        Nat.reduceLT, Nat.lt_add_one] <;>
      omega

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
