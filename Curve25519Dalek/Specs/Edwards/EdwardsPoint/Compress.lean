/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.ToAffine
import Curve25519Dalek.Specs.Edwards.Affine.AffinePoint.Compress

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::compress`

Converts an EdwardsPoint in extended twisted Edwards coordinates to a compressed
32-byte representation. The implementation first converts to affine (x, y) = (X/Z, Y/Z),
then serializes y in little-endian and stores the sign (parity) of x in the MSB of
byte 31 (via XOR). The y-coordinate and the x parity are sufficient to reconstruct
the full point given the defining equation -x² + y² = 1 + dx²y² of the Edwards curve,
which is quadratic in x.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.math
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::compress`**
• The function always succeeds (no panic) when `self.IsValid`
• The byte encoding of the result equals the pure mathematical compression of the
  corresponding abstract point: `U8x32_as_Nat result = compress_edwards_pure self.toPoint`
-/
@[step]
theorem compress_spec (self : EdwardsPoint) (hself : self.IsValid) :
    compress self ⦃ (result : CompressedEdwardsY) =>
      U8x32_as_Nat result = compress_edwards_pure self.toPoint ⦄ := by
  unfold compress
  let* ⟨ap, h_valid, h_point⟩ ← to_affine_spec _ hself
  let* ⟨res, h_res⟩ ← affine.AffinePoint.compress_spec _ h_valid
  rw [h_res, h_point]

end curve25519_dalek.edwards.EdwardsPoint
