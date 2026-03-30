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

1. `from_bytes_loop_helper`: Per-word loop invariant (each word = 8 little-endian bytes).
2. `from_bytes_loop_spec` (`@[step]`): Wraps the helper to give `words_as_Nat = U8x32_as_Nat`.
3. `bit_slicing_of_words`: Pure math — 5 limbs extracted via shift/OR/mask from 4 U64 words
   reconstruct the same value. Uses `or_mul_pow_two_eq_add` and `bit_slicing_identity`.
4. `from_bytes_spec` (`@[step]`): Combines loop spec + bit-slicing to prove the full spec.
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

/-- Alternative loop spec with `words_as_Nat` postcondition. The completed loop packs all
32 bytes into 4 words such that `words_as_Nat words = U8x32_as_Nat bytes`.
Derived from `from_bytes_loop_helper` + `words_eq_bytes`. -/
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

/-- The first 52-bit limb extracted from the packed 4-word representation. -/
abbrev limb0_nat (words1 : Array U64 4#usize) : Nat :=
  words1[0]!.val % 2 ^ 52

/-- State after storing only limb 0 into `ZERO`. -/
def slice_state0 (words1 : Array U64 4#usize) (s : Scalar52) : Prop :=
  s[0]!.val = limb0_nat words1 ∧
  s[1]!.val = 0 ∧
  s[2]!.val = 0 ∧
  s[3]!.val = 0 ∧
  s[4]!.val = 0

/-- The first store in the bit-slicing phase: write limb 0 into slot 0 of `ZERO`. -/
private theorem slice0_step (words1 : Array U64 4#usize) (mask : U64)
    (hmask : mask.val = 2 ^ 52 - 1) :
    (do
      let i2 ← Array.index_usize words1 0#usize
      let (_, index_mut_back) ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut ZERO 0#usize
      let i3 ← lift (i2 &&& mask)
      ok (index_mut_back i3)) ⦃ s =>
      slice_state0 words1 s ∧
      ∀ i < 5, s[i]!.val < 2 ^ 52 ⦄ := by
  unfold Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  step as ⟨ i2, i2_post ⟩
  step as ⟨ _, index_mut_back, hset0, _ ⟩
  step as ⟨ i3, i3_post1, i3_post2 ⟩
  have hi3_mod : i3.val = i2.val % 2 ^ 52 := by
    simp only [i3_post1, UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod]
  have hi3_bound : i3.val < 2 ^ 52 := by
    rw [hi3_mod]
    exact Nat.mod_lt _ (by omega)
  rw [hset0]
  refine ⟨?_, ?_⟩
  · unfold slice_state0 limb0_nat
    repeat' constructor
    · rw [Array.set_of_eq ZERO i3 0 (by simp [ZERO])]
      simpa [i2_post, Array.getElem!_Nat_eq] using hi3_mod
    · rw [Array.set_of_ne_getElem! ZERO i3 1 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
      simp [ZERO]
    · rw [Array.set_of_ne_getElem! ZERO i3 2 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
      simp [ZERO]
    · rw [Array.set_of_ne_getElem! ZERO i3 3 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
      simp [ZERO]
    · rw [Array.set_of_ne_getElem! ZERO i3 4 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
      simp [ZERO]
  · intro idx hidx
    interval_cases idx
    · simpa [Array.set_of_eq ZERO i3 0 (by simp [ZERO])] using hi3_bound
    · simpa [Array.set_of_ne_getElem! ZERO i3 1 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
        using (show ZERO[1]!.val < 2 ^ 52 by simp [ZERO])
    · simpa [Array.set_of_ne_getElem! ZERO i3 2 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
        using (show ZERO[2]!.val < 2 ^ 52 by simp [ZERO])
    · simpa [Array.set_of_ne_getElem! ZERO i3 3 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
        using (show ZERO[3]!.val < 2 ^ 52 by simp [ZERO])
    · simpa [Array.set_of_ne_getElem! ZERO i3 4 0 (by simp [ZERO]) (by simp [ZERO]) (by decide)]
        using (show ZERO[4]!.val < 2 ^ 52 by simp [ZERO])

/-- The second 52-bit limb extracted from the packed 4-word representation. -/
abbrev limb1_nat (words1 : Array U64 4#usize) : Nat :=
  ((words1[0]!.val / 2 ^ 52) ||| ((words1[1]!.val * 2 ^ 12) % U64.size)) % 2 ^ 52

/-- State after storing limbs 0 and 1. -/
def slice_state1 (words1 : Array U64 4#usize) (s : Scalar52) : Prop :=
  s[0]!.val = limb0_nat words1 ∧
  s[1]!.val = limb1_nat words1 ∧
  s[2]!.val = 0 ∧
  s[3]!.val = 0 ∧
  s[4]!.val = 0

/-- The second store in the bit-slicing phase: write limb 1 into slot 1. -/
private theorem slice1_step (words1 : Array U64 4#usize) (s0 : Scalar52) (mask : U64)
    (hs0 : slice_state0 words1 s0) (hmask : mask.val = 2 ^ 52 - 1) :
    (do
      let w0 ← Array.index_usize words1 0#usize
      let hi ← w0 >>> 52#i32
      let w1 ← Array.index_usize words1 1#usize
      let lo ← w1 <<< 12#i32
      let comb ← lift (hi ||| lo)
      let (_, back1) ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut s0 1#usize
      let l1 ← lift (comb &&& mask)
      ok (back1 l1)) ⦃ s =>
      slice_state1 words1 s ∧
      ∀ i < 5, s[i]!.val < 2 ^ 52 ⦄ := by
  obtain ⟨hs0_0, hs0_1, hs0_2, hs0_3, hs0_4⟩ := hs0
  step as ⟨ w0, w0_post ⟩
  step as ⟨ hi, hi_post1, hi_post2 ⟩
  step as ⟨ w1, w1_post ⟩
  step as ⟨ lo, lo_post1, lo_post2 ⟩
  step as ⟨ comb, comb_post1, comb_post2 ⟩
  unfold Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  step as ⟨ _, back1, hset1, _ ⟩
  step as ⟨ l1, l1_post1, l1_post2 ⟩
  have hs0_bound0 : s0[0]!.val < 2 ^ 52 := by
    rw [hs0_0, limb0_nat]
    exact Nat.mod_lt _ (by omega)
  have hl1_mod :
      l1.val = ((w0.val / 2 ^ 52) ||| ((w1.val * 2 ^ 12) % U64.size)) % 2 ^ 52 := by
    simp only [l1_post1, comb_post1, hi_post1, lo_post1, UScalar.val_and, UScalar.val_or, hmask,
      land_pow_two_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hl1_bound : l1.val < 2 ^ 52 := by
    rw [hl1_mod]
    exact Nat.mod_lt _ (by omega)
  have hs0_bound2 : s0[2]!.val < 2 ^ 52 := by
    rw [hs0_2]
    norm_num
  have hs0_bound3 : s0[3]!.val < 2 ^ 52 := by
    rw [hs0_3]
    norm_num
  have hs0_bound4 : s0[4]!.val < 2 ^ 52 := by
    rw [hs0_4]
    norm_num
  rw [hset1]
  refine ⟨?_, ?_⟩
  · unfold slice_state1 limb0_nat limb1_nat
    repeat' constructor
    · rw [Array.set_of_ne_getElem! s0 l1 0 1 (by simp) (by simp) (by decide)]
      exact hs0_0
    · rw [Array.set_of_eq s0 l1 1 (by simp)]
      simpa [w0_post, w1_post] using hl1_mod
    · rw [Array.set_of_ne_getElem! s0 l1 2 1 (by simp) (by simp) (by decide)]
      exact hs0_2
    · rw [Array.set_of_ne_getElem! s0 l1 3 1 (by simp) (by simp) (by decide)]
      exact hs0_3
    · rw [Array.set_of_ne_getElem! s0 l1 4 1 (by simp) (by simp) (by decide)]
      exact hs0_4
  · intro idx hidx
    interval_cases idx
    · simpa [Array.set_of_ne_getElem! s0 l1 0 1 (by simp) (by simp) (by decide)] using hs0_bound0
    · simpa [Array.set_of_eq s0 l1 1 (by simp)] using hl1_bound
    · simpa [Array.set_of_ne_getElem! s0 l1 2 1 (by simp) (by simp) (by decide)] using hs0_bound2
    · simpa [Array.set_of_ne_getElem! s0 l1 3 1 (by simp) (by simp) (by decide)] using hs0_bound3
    · simpa [Array.set_of_ne_getElem! s0 l1 4 1 (by simp) (by simp) (by decide)] using hs0_bound4

/-- The third 52-bit limb extracted from the packed 4-word representation. -/
abbrev limb2_nat (words1 : Array U64 4#usize) : Nat :=
  ((words1[1]!.val / 2 ^ 40) ||| ((words1[2]!.val * 2 ^ 24) % U64.size)) % 2 ^ 52

/-- State after storing limbs 0, 1, and 2. -/
def slice_state2 (words1 : Array U64 4#usize) (s : Scalar52) : Prop :=
  s[0]!.val = limb0_nat words1 ∧
  s[1]!.val = limb1_nat words1 ∧
  s[2]!.val = limb2_nat words1 ∧
  s[3]!.val = 0 ∧
  s[4]!.val = 0

/-- The third store in the bit-slicing phase: write limb 2 into slot 2. -/
private theorem slice2_step (words1 : Array U64 4#usize) (s1 : Scalar52) (mask : U64)
    (hs1 : slice_state1 words1 s1) (hmask : mask.val = 2 ^ 52 - 1) :
    (do
      let w1 ← Array.index_usize words1 1#usize
      let hi ← w1 >>> 40#i32
      let w2 ← Array.index_usize words1 2#usize
      let lo ← w2 <<< 24#i32
      let comb ← lift (hi ||| lo)
      let (_, back2) ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut s1 2#usize
      let l2 ← lift (comb &&& mask)
      ok (back2 l2)) ⦃ s =>
      slice_state2 words1 s ∧
      ∀ i < 5, s[i]!.val < 2 ^ 52 ⦄ := by
  obtain ⟨hs1_0, hs1_1, hs1_2, hs1_3, hs1_4⟩ := hs1
  step as ⟨ w1, w1_post ⟩
  step as ⟨ hi, hi_post1, hi_post2 ⟩
  step as ⟨ w2, w2_post ⟩
  step as ⟨ lo, lo_post1, lo_post2 ⟩
  step as ⟨ comb, comb_post1, comb_post2 ⟩
  unfold Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  step as ⟨ _, back2, hset2, _ ⟩
  step as ⟨ l2, l2_post1, l2_post2 ⟩
  have hs1_bound0 : s1[0]!.val < 2 ^ 52 := by
    rw [hs1_0, limb0_nat]
    exact Nat.mod_lt _ (by omega)
  have hs1_bound1 : s1[1]!.val < 2 ^ 52 := by
    rw [hs1_1, limb1_nat]
    exact Nat.mod_lt _ (by omega)
  have hl2_mod :
      l2.val = ((w1.val / 2 ^ 40) ||| ((w2.val * 2 ^ 24) % U64.size)) % 2 ^ 52 := by
    simp only [l2_post1, comb_post1, hi_post1, lo_post1, UScalar.val_and, UScalar.val_or, hmask,
      land_pow_two_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hl2_bound : l2.val < 2 ^ 52 := by
    rw [hl2_mod]
    exact Nat.mod_lt _ (by omega)
  have hs1_bound3 : s1[3]!.val < 2 ^ 52 := by
    rw [hs1_3]
    norm_num
  have hs1_bound4 : s1[4]!.val < 2 ^ 52 := by
    rw [hs1_4]
    norm_num
  rw [hset2]
  refine ⟨?_, ?_⟩
  · unfold slice_state2 limb0_nat limb1_nat limb2_nat
    repeat' constructor
    · rw [Array.set_of_ne_getElem! s1 l2 0 2 (by simp) (by simp) (by decide)]
      exact hs1_0
    · rw [Array.set_of_ne_getElem! s1 l2 1 2 (by simp) (by simp) (by decide)]
      exact hs1_1
    · rw [Array.set_of_eq s1 l2 2 (by simp)]
      simpa [w1_post, w2_post] using hl2_mod
    · rw [Array.set_of_ne_getElem! s1 l2 3 2 (by simp) (by simp) (by decide)]
      exact hs1_3
    · rw [Array.set_of_ne_getElem! s1 l2 4 2 (by simp) (by simp) (by decide)]
      exact hs1_4
  · intro idx hidx
    interval_cases idx
    · simpa [Array.set_of_ne_getElem! s1 l2 0 2 (by simp) (by simp) (by decide)] using hs1_bound0
    · simpa [Array.set_of_ne_getElem! s1 l2 1 2 (by simp) (by simp) (by decide)] using hs1_bound1
    · simpa [Array.set_of_eq s1 l2 2 (by simp)] using hl2_bound
    · simpa [Array.set_of_ne_getElem! s1 l2 3 2 (by simp) (by simp) (by decide)] using hs1_bound3
    · simpa [Array.set_of_ne_getElem! s1 l2 4 2 (by simp) (by simp) (by decide)] using hs1_bound4

/-- The fourth 52-bit limb extracted from the packed 4-word representation. -/
abbrev limb3_nat (words1 : Array U64 4#usize) : Nat :=
  ((words1[2]!.val / 2 ^ 28) ||| ((words1[3]!.val * 2 ^ 36) % U64.size)) % 2 ^ 52

/-- State after storing limbs 0, 1, 2, and 3. -/
def slice_state3 (words1 : Array U64 4#usize) (s : Scalar52) : Prop :=
  s[0]!.val = limb0_nat words1 ∧
  s[1]!.val = limb1_nat words1 ∧
  s[2]!.val = limb2_nat words1 ∧
  s[3]!.val = limb3_nat words1 ∧
  s[4]!.val = 0

/-- The fourth store in the bit-slicing phase: write limb 3 into slot 3. -/
private theorem slice3_step (words1 : Array U64 4#usize) (s2 : Scalar52) (mask : U64)
    (hs2 : slice_state2 words1 s2) (hmask : mask.val = 2 ^ 52 - 1) :
    (do
      let w2 ← Array.index_usize words1 2#usize
      let hi ← w2 >>> 28#i32
      let w3 ← Array.index_usize words1 3#usize
      let lo ← w3 <<< 36#i32
      let comb ← lift (hi ||| lo)
      let (_, back3) ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut s2 3#usize
      let l3 ← lift (comb &&& mask)
      ok (back3 l3)) ⦃ s =>
      slice_state3 words1 s ∧
      ∀ i < 5, s[i]!.val < 2 ^ 52 ⦄ := by
  obtain ⟨hs2_0, hs2_1, hs2_2, hs2_3, hs2_4⟩ := hs2
  step as ⟨ w2, w2_post ⟩
  step as ⟨ hi, hi_post1, hi_post2 ⟩
  step as ⟨ w3, w3_post ⟩
  step as ⟨ lo, lo_post1, lo_post2 ⟩
  step as ⟨ comb, comb_post1, comb_post2 ⟩
  unfold Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  step as ⟨ _, back3, hset3, _ ⟩
  step as ⟨ l3, l3_post1, l3_post2 ⟩
  have hs2_bound0 : s2[0]!.val < 2 ^ 52 := by
    rw [hs2_0, limb0_nat]
    exact Nat.mod_lt _ (by omega)
  have hs2_bound1 : s2[1]!.val < 2 ^ 52 := by
    rw [hs2_1, limb1_nat]
    exact Nat.mod_lt _ (by omega)
  have hs2_bound2 : s2[2]!.val < 2 ^ 52 := by
    rw [hs2_2, limb2_nat]
    exact Nat.mod_lt _ (by omega)
  have hl3_mod :
      l3.val = ((w2.val / 2 ^ 28) ||| ((w3.val * 2 ^ 36) % U64.size)) % 2 ^ 52 := by
    simp only [l3_post1, comb_post1, hi_post1, lo_post1, UScalar.val_and, UScalar.val_or, hmask,
      land_pow_two_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hl3_bound : l3.val < 2 ^ 52 := by
    rw [hl3_mod]
    exact Nat.mod_lt _ (by omega)
  have hs2_bound4 : s2[4]!.val < 2 ^ 52 := by
    rw [hs2_4]
    norm_num
  rw [hset3]
  refine ⟨?_, ?_⟩
  · unfold slice_state3 limb0_nat limb1_nat limb2_nat limb3_nat
    repeat' constructor
    · rw [Array.set_of_ne_getElem! s2 l3 0 3 (by simp) (by simp) (by decide)]
      exact hs2_0
    · rw [Array.set_of_ne_getElem! s2 l3 1 3 (by simp) (by simp) (by decide)]
      exact hs2_1
    · rw [Array.set_of_ne_getElem! s2 l3 2 3 (by simp) (by simp) (by decide)]
      exact hs2_2
    · rw [Array.set_of_eq s2 l3 3 (by simp)]
      simpa [w2_post, w3_post] using hl3_mod
    · rw [Array.set_of_ne_getElem! s2 l3 4 3 (by simp) (by simp) (by decide)]
      exact hs2_4
  · intro idx hidx
    interval_cases idx
    · simpa [Array.set_of_ne_getElem! s2 l3 0 3 (by simp) (by simp) (by decide)] using hs2_bound0
    · simpa [Array.set_of_ne_getElem! s2 l3 1 3 (by simp) (by simp) (by decide)] using hs2_bound1
    · simpa [Array.set_of_ne_getElem! s2 l3 2 3 (by simp) (by simp) (by decide)] using hs2_bound2
    · simpa [Array.set_of_eq s2 l3 3 (by simp)] using hl3_bound
    · simpa [Array.set_of_ne_getElem! s2 l3 4 3 (by simp) (by simp) (by decide)] using hs2_bound4

/-- The fifth limb extracted from the packed 4-word representation. -/
abbrev limb4_nat (words1 : Array U64 4#usize) : Nat :=
  (words1[3]!.val / 2 ^ 16) % 2 ^ 48

/-- State after storing all 5 limbs. -/
def slice_state4 (words1 : Array U64 4#usize) (s : Scalar52) : Prop :=
  s[0]!.val = limb0_nat words1 ∧
  s[1]!.val = limb1_nat words1 ∧
  s[2]!.val = limb2_nat words1 ∧
  s[3]!.val = limb3_nat words1 ∧
  s[4]!.val = limb4_nat words1

/-- The fifth store in the bit-slicing phase: write limb 4 into slot 4. -/
private theorem slice4_step (words1 : Array U64 4#usize) (s3 : Scalar52) (top_mask : U64)
    (hs3 : slice_state3 words1 s3) (htop : top_mask.val = 2 ^ 48 - 1) :
    (do
      let w3 ← Array.index_usize words1 3#usize
      let hi ← w3 >>> 16#i32
      let (_, back4) ← Insts.CoreOpsIndexIndexMutUsizeU64.index_mut s3 4#usize
      let l4 ← lift (hi &&& top_mask)
      ok (back4 l4)) ⦃ s =>
      slice_state4 words1 s ∧
      ∀ i < 5, s[i]!.val < 2 ^ 52 ⦄ := by
  obtain ⟨hs3_0, hs3_1, hs3_2, hs3_3, hs3_4⟩ := hs3
  step as ⟨ w3, w3_post ⟩
  step as ⟨ hi, hi_post1, hi_post2 ⟩
  unfold Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  step as ⟨ _, back4, hset4, _ ⟩
  step as ⟨ l4, l4_post1, l4_post2 ⟩
  have hs3_bound0 : s3[0]!.val < 2 ^ 52 := by
    rw [hs3_0, limb0_nat]
    exact Nat.mod_lt _ (by omega)
  have hs3_bound1 : s3[1]!.val < 2 ^ 52 := by
    rw [hs3_1, limb1_nat]
    exact Nat.mod_lt _ (by omega)
  have hs3_bound2 : s3[2]!.val < 2 ^ 52 := by
    rw [hs3_2, limb2_nat]
    exact Nat.mod_lt _ (by omega)
  have hs3_bound3 : s3[3]!.val < 2 ^ 52 := by
    rw [hs3_3, limb3_nat]
    exact Nat.mod_lt _ (by omega)
  have hl4_mod : l4.val = (w3.val / 2 ^ 16) % 2 ^ 48 := by
    simp only [l4_post1, hi_post1, UScalar.val_and, htop, land_pow_two_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow]
  have hl4_bound : l4.val < 2 ^ 52 := by
    rw [hl4_mod]
    have h48 : (w3.val / 2 ^ 16) % 2 ^ 48 < 2 ^ 48 := Nat.mod_lt _ (by omega)
    omega
  rw [hset4]
  refine ⟨?_, ?_⟩
  · unfold slice_state4 limb0_nat limb1_nat limb2_nat limb3_nat limb4_nat
    repeat' constructor
    · rw [Array.set_of_ne_getElem! s3 l4 0 4 (by simp) (by simp) (by decide)]
      exact hs3_0
    · rw [Array.set_of_ne_getElem! s3 l4 1 4 (by simp) (by simp) (by decide)]
      exact hs3_1
    · rw [Array.set_of_ne_getElem! s3 l4 2 4 (by simp) (by simp) (by decide)]
      exact hs3_2
    · rw [Array.set_of_ne_getElem! s3 l4 3 4 (by simp) (by simp) (by decide)]
      exact hs3_3
    · rw [Array.set_of_eq s3 l4 4 (by simp)]
      simpa [w3_post, Array.getElem!_Nat_eq] using hl4_mod
  · intro idx hidx
    interval_cases idx
    · simpa [Array.set_of_ne_getElem! s3 l4 0 4 (by simp) (by simp) (by decide)] using hs3_bound0
    · simpa [Array.set_of_ne_getElem! s3 l4 1 4 (by simp) (by simp) (by decide)] using hs3_bound1
    · simpa [Array.set_of_ne_getElem! s3 l4 2 4 (by simp) (by simp) (by decide)] using hs3_bound2
    · simpa [Array.set_of_ne_getElem! s3 l4 3 4 (by simp) (by simp) (by decide)] using hs3_bound3
    · simpa [Array.set_of_eq s3 l4 4 (by simp)] using hl4_bound

/-- A scalar satisfying `slice_state4` has the same value as the packed 4-word input. -/
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
