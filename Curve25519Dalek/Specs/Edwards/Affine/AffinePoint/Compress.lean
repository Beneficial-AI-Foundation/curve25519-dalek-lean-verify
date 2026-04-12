/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorem for `AffinePoint::compress`

Specification and proof for `edwards.affine.AffinePoint.compress`.

This function converts an Edwards affine point (x, y) into its 32-byte
CompressedEdwardsY representation by serializing y in little-endian and
storing the sign bit of x in the most significant bit of the last byte.

**Source**: curve25519-dalek/src/edwards/affine.rs

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.math
namespace curve25519_dalek.edwards.affine.AffinePoint

/-
Natural language description:

    * Takes an affine Edwards point with coordinates (x, y)
    * Serializes y to a 32-byte little-endian array
    * Computes the sign (parity) bit of x as a subtle.Choice
    * Sets the MSB (bit 7) of byte 31 of the serialized y to this sign bit (via XOR)
    * Returns the resulting 32-byte array as CompressedEdwardsY

Natural language specs:

    * The function always succeeds (no panic) when the AffinePoint is valid
    * On success, the byte encoding equals compress_edwards_pure(self.toPoint),
      i.e. the canonical y-coordinate in the lower 255 bits with the x parity
      in bit 255
-/

/-- **Spec and proof concerning `edwards.affine.AffinePoint.compress`**:
- Requires: the AffinePoint is valid (limbs < 2^54, on curve)
- Ensures: the compressed bytes equal the pure mathematical compression of the point
-/
@[externally_verified, step] -- proven in Verus
theorem compress_spec (self : AffinePoint) (hself : self.IsValid) :
    compress self ⦃ result =>
    U8x32_as_Nat result = compress_edwards_pure (self.toPoint) ⦄ := by
  sorry

end curve25519_dalek.edwards.affine.AffinePoint
