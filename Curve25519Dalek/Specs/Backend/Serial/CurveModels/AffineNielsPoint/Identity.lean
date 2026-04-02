/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
/-!
# Spec theorem for `AffineNielsPoint::identity`

Specification and proof for `AffineNielsPoint::identity`.

This function returns the identity element of the Edwards curve in AffineNiels coordinates
(y_plus_x, y_minus_x, xy2d). The identity element on the Edwards curve is the affine point
(x, y) = (0, 1), which in AffineNiels representation gives:
- y_plus_x  = y + x = 1 + 0 = 1
- y_minus_x = y − x = 1 − 0 = 1
- xy2d      = 2·d·x·y = 2·d·0·1 = 0

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace Curve25519_dalekTraitsIdentity

/-- **Spec theorem for
`curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::identity`**
- No panic (always returns successfully)
- The resulting AffineNielsPoint is the identity element with coordinates:
  y_plus_x = 1, y_minus_x = 1, xy2d = 0 -/
@[step]
theorem identity_spec :
    identity ⦃ (q : AffineNielsPoint) =>
      Field51_as_Nat q.y_plus_x = 1 ∧
      Field51_as_Nat q.y_minus_x = 1 ∧
      Field51_as_Nat q.xy2d = 0 ⦄ := by
  unfold identity
  step*

end Curve25519_dalekTraitsIdentity
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
