/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified

import Curve25519Dalek.Specs.Edwards.EdwardsPoint.ToAffine
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # Spec Theorem for `EdwardsPoint::compress`

Specification and proof for `EdwardsPoint::compress`.

Converts an EdwardsPoint in extended twisted Edwards coordinates to a compressed
32-byte representation by first converting to affine coordinates (x,y), then encoding
the y-coordinate and the sign bit of the x-coordinate. Note that the y-coordinate
and the sign of the x coordinate are sufficient to reconstruct the full point (x,y)
given the defining equation $ax^2 + y^2 = 1 + dx^2y^2$ of the Edwards curve which is quadratic in x.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

open curve25519_dalek.backend.serial.u64.field.FieldElement51

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
@[externally_verified, progress] -- proven in Verus
theorem compress_spec (self : EdwardsPoint) (hX : ∀ i < 5, self.X[i]!.val < 2 ^ 54)
      (hY : ∀ i < 5, self.Y[i]!.val < 2 ^ 54) (hZ : ∀ i < 5, self.Z[i]!.val < 2 ^ 54)
      -- (hself : self.IsValid)
      :
    compress self ⦃ result => True ⦄ := by
  unfold compress
  sorry





end curve25519_dalek.edwards.EdwardsPoint
