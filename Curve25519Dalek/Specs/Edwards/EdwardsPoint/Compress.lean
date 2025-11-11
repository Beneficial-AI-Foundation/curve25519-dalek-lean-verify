/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `EdwardsPoint::compress`

Specification and proof for `EdwardsPoint::compress`.

Converts an EdwardsPoint in extended twisted Edwards coordinates to a compressed
32-byte representation by first converting to affine coordinates (x,y), then encoding
the y-coordinate and the sign bit of the x-coordinate. Note that the y-coordinate
and the sign of the x coordinate are sufficient to reconstruct the full point (x,y)
given the defining equation $ax^2 + y^2 = 1 + dx^2y^2$ of the Edwards curve which is quadratic in x.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
Natural language description:

    • Compresses an EdwardsPoint from extended twisted Edwards coordinates to a U8x32 byte array
    • First converts the point from projective (X:Y:Z:T) to affine (x,y) coordinates by computing
      x = X/Z and y = Y/Z
    • Then encodes the y-coordinate as a U8x32 byte array and stores
      the sign of x in the high bit of the last byte (which is unused and not required to store y)

Natural language specs:

    • The function always succeeds if Z is invertible / not zero (no panic)
    • On success, returns a CompressedEdwardsY (U8x32 byte array) where:
      - Bytes 0-30 and the low 7 bits of byte 31 encode the y-coordinate in little-endian
      - The high bit of byte 31 encodes the sign (parity) of the x-coordinate
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.compress`**:
- No panic when Z is invertible / not zero (always returns successfully)
- On success, returns a CompressedEdwardsY (U8x32 byte array) where:
  - Bytes 0-30 and the low 7 bits of byte 31 encode the affine y-coordinate in little-endian
  - The high bit of byte 31 encodes the sign (parity) of the affine x-coordinate
-/
@[progress]
theorem compress_spec (e : EdwardsPoint) (h_Z_nonzero : ∃ recip, field.FieldElement51.invert e.Z = ok recip) :
    ∃ (cey : CompressedEdwardsY) (ae : edwards.affine.AffinePoint) (x_sign : subtle.Choice),
      compress e = ok cey ∧
      to_affine e = ok ae ∧
      field.FieldElement51.is_negative ae.x = ok x_sign ∧
      U8x32_as_Nat cey % p = (Field51_as_Nat ae.y + (if cey[31].val.testBit 7 then 2^255 else 0)) % p ∧
      (cey[31].val.testBit 7 ↔ x_sign.val = 1#u8)
      := by
  sorry



end curve25519_dalek.edwards.EdwardsPoint
