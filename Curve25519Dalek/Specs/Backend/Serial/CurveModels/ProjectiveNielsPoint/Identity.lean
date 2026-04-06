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
# Spec theorem for `ProjectiveNielsPoint::identity`

This function returns the identity element of the Edwards curve in ProjectiveNiels
coordinates (Y_plus_X=1, Y_minus_X=1, Z=1, T2d=0), representing the affine point (0, 1).

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity

/-- **Spec theorem for
`backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity`**

Returns the identity element of the Edwards curve in ProjectiveNiels coordinates:
- No panic (always returns successfully)
- The resulting ProjectiveNielsPoint is the identity element with coordinates
  (Y_plus_X=1, Y_minus_X=1, Z=1, T2d=0) -/
@[step]
theorem identity_spec :
    identity ⦃ (result : ProjectiveNielsPoint) =>
      Field51_as_Nat result.Y_plus_X = 1 ∧
      Field51_as_Nat result.Y_minus_X = 1 ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T2d = 0 ⦄ := by
  unfold identity
  step*

end curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity
