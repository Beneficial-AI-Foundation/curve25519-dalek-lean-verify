/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

/-!
# Spec theorem for `curve25519_dalek::montgomery::ProjectivePoint::identity`

Returns the identity element (point at infinity) of the Montgomery curve in projective
coordinates (U, W). The Montgomery curve has the form B·v² = u³ + A·u² + u; in projective
coordinates (U : W), the affine coordinate is u = U/W, and W = 0 represents the point at
infinity, which serves as the identity element of the group.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.IdentityMontgomeryProjectivePoint

/-- **Spec theorem for `curve25519_dalek::montgomery::ProjectivePoint::identity`**
• The function always succeeds (no panic)
• The resulting ProjectivePoint has U-coordinate with `Field51_as_Nat q.U = 1`
• The resulting ProjectivePoint has W-coordinate with `Field51_as_Nat q.W = 0`
-/
@[step]
theorem identity_spec :
    identity ⦃ (q : montgomery.ProjectivePoint) =>
      Field51_as_Nat q.U = 1 ∧
      Field51_as_Nat q.W = 0 ⦄ := by
  unfold identity
  step*

end curve25519_dalek.IdentityMontgomeryProjectivePoint
