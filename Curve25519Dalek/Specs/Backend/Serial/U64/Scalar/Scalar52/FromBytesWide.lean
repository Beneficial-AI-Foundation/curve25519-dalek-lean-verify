/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorem for `Scalar52::from_bytes_wide`

Specification and proof for `Scalar52::from_bytes_wide`.

This function constructs an unpacked scalar from a wide byte array.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes a 64-byte array b as input and returns an unpacked scalar u that
      represents the 512-bit integer value reduced modulo L, redistributed into five limbs.

natural language specs:

    • scalar_to_nat(u) = u8x64_to_nat(b) % L
-/

/-- The natural number value of the j-th 8-byte little-endian chunk of a 64-byte array.
    That is, bytes[j*8], bytes[j*8+1], ..., bytes[j*8+7] assembled into a u64. -/
def word_j_from_bytes (bytes : Array U8 64#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8, 2 ^ (8 * k) * (bytes[j * 8 + k]!).val

/-- **Spec for `backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop`**:
- Starting from index `i` with byte array `bytes` and word array `words`
- Assembles 8-byte little-endian chunks into u64 words
- Loop invariant:
  - Already-processed words (j < i) hold the correct assembled value
  - Not-yet-processed words (j ≥ i) are still zero
- On termination, every word holds its assembled 8-byte chunk -/
@[progress]
theorem from_bytes_wide_loop_spec
    -- inputs to the loop
    (bytes : Array U8 64#usize) (words : Array U64 8#usize) (i : Usize)
    -- bounds for the inputs
    (hi : i.val ≤ 8)
    (hbytes : ∀ j < 64, ∀ k < 8, (bytes[j]!).val < 2 ^ 8)
    (hwords: ∀ j < 8, (words[j]!).val < 2 ^ 64)
    -- Precondtion 1: already processed words hold the correct assembled value
    (hpre1 : ∀ j < 8, j < i.val → (words[j]!).val = word_j_from_bytes bytes j)
    -- Preconditon 2: not-yet-processed words are zero
    (hpre2 : ∀ j < 8, i.val ≤ j → (words[j]!).val = 0) :
    -- Postcondition:
    -- Sum of all words equals the sum of already-processed words plus the
    --newly processed word at index i
    from_bytes_wide_loop bytes words i ⦃ words' =>
    ∑ j ∈ Finset.range 8, (words'[j]!).val
      = ∑ j ∈ Finset.range 8, (words[j]!).val + word_j_from_bytes bytes i ⦄ := by
  sorry

/-- **Spec and proof concerning `scalar.Scalar52.from_bytes_wide`**:
- No panic (always returns successfully)
- The result represents the input byte array reduced modulo L (canonical form) -/
@[externally_verified, progress] -- proven in Verus
theorem from_bytes_wide_spec ( b : Array U8 64#usize ) :
    from_bytes_wide b ⦃ ( u : Scalar52 ) =>
    Scalar52_as_Nat u = U8x64_as_Nat b % L ⦄ := by
  unfold from_bytes_wide Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  progress*
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
