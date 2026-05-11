/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
/-!
# Spec theorem for `ProjectiveNielsPoint::identity`

This function returns the identity element of the Edwards curve in ProjectiveNiels
coordinates (Y_plus_X=1, Y_minus_X=1, Z=1, T2d=0), representing the affine point (0, 1).

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
open backend.serial.u64.field.FieldElement51
open backend.serial.curve_models

namespace curve25519_dalek
namespace backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity

/-- **Spec theorem for
`backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity`**

Returns the identity element of the Edwards curve in ProjectiveNiels coordinates:
- No panic (always returns successfully)
- The resulting ProjectiveNielsPoint is the identity element with coordinates
  (Y_plus_X=1, Y_minus_X=1, Z=1, T2d=0)
- The result is a valid `ProjectiveNielsPoint`.
- It represents the Edwards curve identity `0 = (0, 1)` (the affine neutral element). -/
@[step]
theorem identity_spec :
    identity ⦃ (result : ProjectiveNielsPoint) =>
      Field51_as_Nat result.Y_plus_X = 1 ∧
      Field51_as_Nat result.Y_minus_X = 1 ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T2d = 0 ∧
      result.IsValid ∧
      result.toPoint = 0 ⦄ := by
  unfold identity ONE ZERO
  step*
  have h1 : Field51_as_Nat fe = 1 := by rw [fe_post2]; decide
  have h0 : Field51_as_Nat fe1 = 0 := by rw [fe1_post2]; decide
  have hv :
      ({ Y_plus_X := fe, Y_minus_X := fe, Z := fe, T2d := fe1 }
        : ProjectiveNielsPoint).IsValid := by
    rw [fe_post1, fe1_post1]; decide
  refine ⟨h1, h1, h1, h0, hv, ?_⟩
  have ⟨hpx, hpy⟩ := ProjectiveNielsPoint.toPoint_of_isValid hv
  ext
  all_goals simp [hpx, hpy, toField, h1]

end backend.serial.curve_models.ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity
end curve25519_dalek
