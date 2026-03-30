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

The proof decomposes into three pieces matching the Rust code:

1. `from_bytes_loop_spec`: The byte-packing loop correctly assembles 8 consecutive
   bytes into each U64 word as a little-endian integer.

2. `words_eq_bytes`: The 4 packed words represent the same value as `U8x32_as_Nat`:
   `∑ j < 4, words[j] * 2^(64*j) = U8x32_as_Nat bytes`

3. `from_bytes_spec`: The bit-slicing phase extracts 5 limbs from 4 words,
   preserving the value and producing limbs < 2^52.
-/

set_option linter.style.whitespace false

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-! ## Helper definitions -/

/-- The little-endian value of 8 consecutive bytes starting at position `8*j`. -/
def word_as_nat (bytes : Array U8 32#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8, bytes[8 * j + k]!.val * 2 ^ (8 * k)

/-! ## Part 1: Loop spec — byte packing -/

/-- **Loop spec**: Each iteration packs 8 bytes into one U64 word (little-endian).
After the loop completes, `words[j] = word_as_nat bytes j` for all `j < 4`. -/
@[step]
theorem from_bytes_loop_spec (bytes : Array U8 32#usize)
    (words : Array U64 4#usize) (i : Usize) (hi : i.val ≤ 4)
    (h_prev : ∀ j, j < i.val → words[j]!.val = word_as_nat bytes j) :
    from_bytes_loop bytes words i ⦃ words' =>
      ∀ j, j < 4 → words'[j]!.val = word_as_nat bytes j ⦄ := by
  sorry

/-! ## Part 2: Words-to-bytes equivalence -/

/-- The 4 packed words represent the same value as the 32-byte little-endian interpretation. -/
theorem words_eq_bytes (bytes : Array U8 32#usize) (words : Array U64 4#usize)
    (h : ∀ j, j < 4 → words[j]!.val = word_as_nat bytes j) :
    ∑ j ∈ Finset.range 4, words[j]!.val * 2 ^ (64 * j) = U8x32_as_Nat bytes := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]
  unfold word_as_nat U8x32_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  ring

/-! ## Part 3: Main spec -/

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
