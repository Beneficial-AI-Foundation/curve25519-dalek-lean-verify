/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.R
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

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

/-- The natural number value of an array of 8 u64 words, interpreted as a little-endian
512-bit integer. -/
def words_as_Nat (words : Array U64 8#usize) : Nat :=
  ∑ j ∈ Finset.range 8, (words[j]!).val * 2 ^ (64 * j)

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
    (hi : i.val < 8)
    -- Precondtion 1: already processed words hold the correct assembled value
    (hpre1 : ∀ j < 8, j < i.val → (words[j]!).val = word_j_from_bytes bytes j)
    -- Preconditon 2: not-yet-processed words are zero
    (hpre2 : ∀ j < 8, i.val ≤ j → (words[j]!).val = 0) :
    -- Postcondition:
    -- Sum of all words equals the sum of already-processed words plus the
    --newly processed word at index i
    from_bytes_wide_loop bytes words i ⦃ words' =>
    words_as_Nat words' =
      words_as_Nat words + word_j_from_bytes bytes i * 2 ^ (64 * i.val) ⦄ := by
  sorry

set_option maxHeartbeats 1000000 in
/-- **Spec and proof concerning `scalar.Scalar52.from_bytes_wide`**:
- No panic (always returns successfully)
- The result represents the input byte array reduced modulo L (canonical form) -/
@[externally_verified, progress] -- proven in Verus
theorem from_bytes_wide_spec ( b : Array U8 64#usize ) :
    from_bytes_wide b ⦃ ( u : Scalar52 ) =>
    Scalar52_as_Nat u = U8x64_as_Nat b % L ⦄ := by
  unfold from_bytes_wide Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  progress*
  -- Rough sketch of the proof steps:
  -- 1. To prove U8x64_as_Nat b = ∑ words
  -- 2. To prove lo + hi * R = ∑ words
  -- 3. To prove lo + hi * R % L = ∑ words % L
  -- 4. To prove Scalar52_as_Nat u = U8x64_as_Nat b % L

  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
