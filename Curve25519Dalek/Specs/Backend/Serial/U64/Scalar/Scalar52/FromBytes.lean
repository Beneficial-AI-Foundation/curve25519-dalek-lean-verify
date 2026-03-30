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


/-! ## Part 2: Main spec -/

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
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
