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
- Starting from index `i` of word array `words`, assembles 8-byte little-endian chunks
- from byte array `bytes` into u64 words -/
@[progress]
theorem from_bytes_wide_loop_spec
    -- inputs to the loop
    (bytes : Array U8 64#usize) (words : Array U64 8#usize) (i : Usize)
    -- bounds for the inputs
    (hi : i.val < 8)
    -- Preconditon: not-yet-processed words are zero
    (hpre: ∀ j < 8, i.val ≤ j → (words[j]!).val = 0) :
    -- Postcondition:
    -- Sum of all words equals the sum of already-processed words plus the
    --newly processed word at index i
    from_bytes_wide_loop bytes words i ⦃ words' =>
    words_as_Nat words' = words_as_Nat words
      + ∑ j ∈ Finset.Ico i.val 8, word_j_from_bytes bytes j * 2 ^ (64 * j) ⦄ := by
  -- We can use the BitList to help us with this proof.
  sorry

set_option maxHeartbeats 1000000 in
/-- **Spec and proof concerning `scalar.Scalar52.from_bytes_wide`**:
- No panic (always returns successfully)
- The result represents the input byte array reduced modulo L (canonical form) -/
@[externally_verified, progress] -- proven in Verus
theorem from_bytes_wide_spec ( b : Array U8 64#usize ) :
    from_bytes_wide b ⦃ ( u : Scalar52 ) =>
    Scalar52_as_Nat u = U8x64_as_Nat b % L ⦄ := by
  -- Rough sketch of the proof steps:

  -- 1. To prove U8x64_as_Nat b = words_as_Nat words1
  --    - From from_bytes_wide_loop_spec, we know that
  --      words_as_Nat words1 = words_as_Nat words
  --        + ∑ j ∈ Finset.Ico i.val 8, word_j_from_bytes bytes j * 2 ^ (64 * j)
  --    - Since i.val = 0, the RHS = U8x64_as_Nat b.
  --    - Thus, we have U8x64_as_Nat b = words_as_Nat words1.

  -- 2. To prove Scalar52_as_Nat lo + Scalar52_as_Nat hi * R = words_as_Nat words1
  --    - lo[0] = words[0] & mask = words[0][0:52]
  --    - lo[1] = ((words[0] >> 52) | (words[1] << 12)) & mask
  --            = (words[0][52:64] ++ words[1][0:52]) & mask
  --            = words[0][52:64] ++ words[1][0:40]
  --    - lo[2] = ((words[1] >> 40) | (words[2] << 24)) & mask
  --            = (words[1][40:64] ++ words[2][0:40]) & mask
  --            = words[1][40:64] ++ words[2][0:28]
  --    - lo[3] = ((words[2] >> 28) | (words[3] << 36)) & mask
  --            = (words[2][28:64] ++ words[3][0:28]) & mask
  --            = words[2][28:64] ++ words[3][0:16]
  --    - lo[4] = ((words[3] >> 16) | (words[4] << 48)) & mask
  --            = (words[3][16:64] ++ words[4][0:16]) & mask
  --            = words[3][16:64] ++ words[4][0:4]
  --    - hi[0] = (words[4] >> 4) & mask = words[4][4:56]
  --    - hi[1] = (words[4] >> 56) | (words[5] << 8) & mask
  --            = (words[4][56:64] ++ words[5][0:56]) & mask
  --            = words[4][56:64] ++ words[5][0:44]
  --    - hi[2] = (words[5] >> 44) | (words[6] << 20) & mask
  --            = (words[5][44:64] ++ words[6][0:44]) & mask
  --            = words[5][44:64] ++ words[6][0:32]
  --    - hi[3] = (words[6] >> 32) | (words[7] << 32) & mask
  --            = (words[6][32:64] ++ words[7][0:32]) & mask
  --            = words[6][32:64] ++ words[7][0:20]
  --    - hi[4] = (words[7] >> 20) = words[7][20:64]
  --    - Since the arrangement of bits in lo and hi exhausts all bits in words1,
  --      we have Scalar52_as_Nat lo + Scalar52_as_Nat hi * R = words_as_Nat words1.
  --    - Note: The proof of this step would most probably require BitList and some lemmas about it.

  -- 3. To prove Scalar52_as_Nat lo + Scalar52_as_Nat hi * R % L = words_as_Nat words1 % L
  --    - This should be trivial from the previous hypethesis and properties of modular arithmetic.

  -- 4. To prove Scalar52_as_Nat lo' = Scalar52_as_Nat lo % L where lo' = montgomery_mul(lo, R).
  --    - lo' = montgomery_mul(lo, R)
  --      => Scalar52_as_Nat lo * Scalar52_as_Nat R % L = Scalar52_as_Nat lo' * R % L
  --      => Scalar52_as_Nat lo % L = Scalar52_as_Nat lo' % L
  --    - Note: The proof of this step would require the montgomery_mul_spec theorem

  -- 5. To prove Scalar52_as_Nat hi' = Scalar52_as_Nat hi * R % L where hi' = montgomery_mul(hi, RR)
  --    - hi' = montgomery_mul(hi, RR)
  --      => Scalar52_as_Nat hi * Scalar52_as_Nat RR % L = Scalar52_as_Nat hi' * R % L
  --      => Scalar52_as_Nat hi * R % L = Scalar52_as_Nat hi' % L since Scalar52_as_Nat RR = R^2 % L
  --    - Note: The proof of this step would require the montgomery_mul_spec theorem.

  -- 6. To prove Scalar52_as_Nat lo' + Scalar52_as_Nat hi' = words_as_Nat words1 % L
  --    - From steps 4 and 5, we have Scalar52_as_Nat lo' + Scalar52_as_Nat hi'
  --      = Scalar52_as_Nat lo % L + Scalar52_as_Nat hi * R % L

  -- 7. To prove Scalar52_as_Nat u = U8x64_as_Nat b % L
  --    - This is trivial since Scalar_as_Nat u = Scalar52_as_Nat lo' + Scalar52_as_Nat hi' and
  --      words_as_Nat words1 % L = U8x64_as_Nat b % L.
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
