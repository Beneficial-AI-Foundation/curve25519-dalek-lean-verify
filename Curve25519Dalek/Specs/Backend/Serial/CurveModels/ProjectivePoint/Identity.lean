/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
/-!
# Spec theorem for `ProjectivePoint::identity`

This function returns the identity element of the Edwards curve in projective coordinates
(X=0, Y=1, Z=1), representing the affine point (0, 1).

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs:L231-L237"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.IdentityCurveModelsProjectivePoint

/-- **Spec theorem for
`curve25519_dalek.IdentityCurveModelsProjectivePoint.identity`**

Returns the identity element of the Edwards curve in projective coordinates:
- No panic (always returns successfully)
- The resulting ProjectivePoint is the identity element with coordinates (X=0, Y=1, Z=1) -/
@[step]
theorem identity_spec :
    identity ⦃ (result : backend.serial.curve_models.ProjectivePoint) =>
      Field51_as_Nat result.X = 0 ∧
      Field51_as_Nat result.Y = 1 ∧
      Field51_as_Nat result.Z = 1 ⦄ := by
  unfold identity
  step*

end curve25519_dalek.IdentityCurveModelsProjectivePoint
