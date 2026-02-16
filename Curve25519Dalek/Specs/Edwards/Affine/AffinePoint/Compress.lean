/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `AffinePoint::compress`

Specification and proof for `edwards.affine.AffinePoint.compress`.

This function converts an Edwards affine point (x, y) into its 32-byte
CompressedEdwardsY representation by serializing y in little-endian and
storing the sign bit of x in the most significant bit of the last byte.

**Source**: curve25519-dalek/src/edwards/affine.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result Aeneas.Std.WP
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
- Requires: `y`-coordinate of the AffinePoint, when converted to 32 bytes, has leading bit zero
- Returns a CompressedEdwardsY equal to the input AffinePoint
-/
@[progress]
theorem compress_spec (self : AffinePoint) -- (hself : self.IsValid)
    (h : Field51_as_Nat self.y < 2 ^ 255) :
    spec (compress self) (fun result =>
    True -- result.IsValid ∧ result.toPoint = self.toPoint
    ) := by
  sorry

-- To do: update this when relevant definitions have been added.

end curve25519_dalek.edwards.affine.AffinePoint
