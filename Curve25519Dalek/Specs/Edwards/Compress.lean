/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `AffinePoint::compress`

Specification and proof for `edwards.affine.AffinePoint.compress`.

This function converts an Edwards affine point (x, y) into its 32-byte
CompressedEdwardsY representation by serializing y in little-endian and
storing the sign bit of x in the most significant bit of the last byte.

**Source**: curve25519-dalek/src/edwards/affine.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.affine.AffinePoint

/-
Natural language description:

    • Takes an affine Edwards point with coordinates (x, y)
    • Serializes y to a 32-byte little-endian array
    • Computes the sign (parity) bit of x as a subtle.Choice
    • Sets the MSB (bit 7) of byte 31 of the serialized y to this sign bit (via XOR)
    • Returns the resulting 32-byte array as CompressedEdwardsY

Natural language specs:

    • The function always succeeds (no panic)
    • On success, returns a CompressedEdwardsY (U8x32) where:
      - Bytes 0–30 and the low 7 bits of byte 31 encode the y-coordinate in little-endian
      - The high bit of byte 31 encodes the sign (parity) of the x-coordinate
-/

/-- **Spec and proof concerning `edwards.affine.AffinePoint.compress`**:
- No panic (always returns successfully)
- On success, returns a CompressedEdwardsY (U8x32) where:
  - Bytes 0–30 and the low 7 bits of byte 31 encode the affine y-coordinate in little-endian
  - The high bit of byte 31 encodes the sign (parity) of the affine x-coordinate
  - Numerically, interpreting the 32-byte string as an integer in [0, 2^256),
    it equals (y + (sign_x ? 2^255 : 0)) modulo p
-/
@[progress]
theorem compress_spec (a : edwards.affine.AffinePoint) :
    ∃ (cey : edwards.CompressedEdwardsY) (x_sign : subtle.Choice),
    edwards.affine.AffinePoint.compress a = ok cey ∧
    field.FieldElement51.is_negative a.x = ok x_sign ∧
    U8x32_as_Nat cey % p = (Field51_as_Nat a.y + (if cey[31].val.testBit 7 then 2^255 else 0)) % p ∧
    (cey[31].val.testBit 7 ↔ x_sign.val = 1#u8) := by
  /-
  Proof idea (sketch):
  • By unfolding `edwards.affine.AffinePoint.compress` (see Funs.lean), we get:
      s ← to_bytes a.y; c ← is_negative a.x; bit ← unwrap_u8 c; s[31] ^= bit<<7
    hence the returned array is exactly y's encoding with MSB of last byte XOR'ed
    with the sign bit of x.
  • The last-bit equivalence follows from this construction.
  • The numeric statement follows because the low 255 bits are y's canonical
    little-endian representation and the MSB contributes 2^255 iff set.
  -/
  sorry

end curve25519_dalek.edwards.affine.AffinePoint
