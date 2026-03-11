/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorem for `Scalar52::from_bytes`

Specification and proof for `Scalar52::from_bytes`.

This function constructs an unpacked scalar from a byte array.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes a 32-byte array b as input and returns an unpacked scalar u that
      represents the same 256-bit integer value, redistributed into five limbs.

natural language specs:

    • scalar_to_nat(u) = u32x8_to_nat(b)
-/

/-- The natural number value of the j-th 8-byte little-endian chunk of a 32-byte array.
    That is, bytes[j*8], bytes[j*8+1], ..., bytes[j*8+7] assembled into a u64. -/
def word_j_from_bytes (bytes : Array U8 32#usize) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range 8, 2 ^ (8 * k) * (bytes[j * 8 + k]!).val

/-- The natural number value of an array of 4 u64 words, interpreted as a little-endian
256-bit integer. -/
def words_as_Nat (words : Array U64 4#usize) : Nat :=
  ∑ j ∈ Finset.range 4, (words[j]!).val * 2 ^ (64 * j)

/-- **Spec for `backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop`**:
- Starting from index `i` of word array `words`, assembles 8-byte little-endian chunks
- from byte array `bytes` into u64 words -/
@[progress]
theorem from_bytes_loop_spec
    -- inputs to the loop
    (bytes : Array U8 32#usize) (words : Array U64 4#usize) (i : Usize)
    -- bounds for the inputs
    (hi : i.val < 4)
    -- Preconditon: not-yet-processed words are zero
    (hpre: ∀ j < 4, i.val ≤ j → (words[j]!).val = 0) :
    -- Postcondition:
    -- Sum of all words equals the sum of already-processed words plus the
    --newly processed word at index i
    from_bytes_loop bytes words i ⦃ words' =>
    words_as_Nat words' = words_as_Nat words
      + ∑ j ∈ Finset.Ico i.val 4, word_j_from_bytes bytes j * 2 ^ (8 * j) ⦄ := by
  -- We can use the BitList to help us with this proof.
  sorry

/-- **Spec and proof concerning `scalar.Scalar52.from_bytes`**:
- No panic (always returns successfully)
- The result represents the same number as the input byte array
-/
@[externally_verified, progress] -- proven in Verus
theorem from_bytes_spec (b : Array U8 32#usize) :
    from_bytes b ⦃ u =>
    Scalar52_as_Nat u = U8x32_as_Nat b ∧
    ∀ i < 5, u[i]!.val < 2 ^ 52 ⦄
    := by

  -- Rough sketch of the proof steps:

  -- 1. To prove U8x32_as_Nat b = words_as_Nat words1
  --    - From from_bytes_loop_spec, we know that
  --      words_as_Nat words1 = words_as_Nat words
  --        + ∑ j ∈ Finset.Ico i.val 4, word_j_from_bytes bytes j * 2 ^ (8 * j)
  --    - Since i.val = 0, the RHS = U8x32_as_Nat b.
  --    - Thus, we have U8x32_as_Nat b = words_as_Nat words1.

  -- 2. To prove Scalar52_as_Nat u = words_as_Nat words1
  --    - u[0] = words[0] & mask = words[0][0:52]
  --    - u[1] = ((words[0] >> 52) | (words[1] << 12)) & mask
  --           = (words[0][52:64] ++ words[1][0:52]) & mask
  --           = words[0][52:64] ++ words[1][0:40]
  --    - u[2] = ((words[1] >> 40) | (words[2] << 24)) & mask
  --           = (words[1][40:64] ++ words[2][0:40]) & mask
  --           = words[1][40:64] ++ words[2][0:28]
  --    - u[3] = ((words[2] >> 28) | (words[3] << 36)) & mask
  --           = (words[2][28:64] ++ words[3][0:28]) & mask
  --           = words[2][28:64] ++ words[3][0:16]
  --    - u[4] = words[3] >> 16 & top_mask
  --           = words[3][16:64] & top_mask
  --           = words[3][16:64]
  --    - Since the arrangement of bits in u exhausts all bits in words1,
  --      we have Scalar52_as_Nat u = words_as_Nat words1.
  --    - Note: The proof of this step would most probably require BitList and some lemmas about it.

  -- 3. To prove Scalar52_as_Nat u = U8x32_as_Nat b
  --    - This is trivial since words_as_Nat words1 = U8x32_as_Nat b.

    sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
