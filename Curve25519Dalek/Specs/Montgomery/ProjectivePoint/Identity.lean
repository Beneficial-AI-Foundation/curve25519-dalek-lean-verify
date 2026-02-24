/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE


/-! # identity

Specification and proof for `montgomery::ProjectivePoint::identity`.

This function returns the identity element of the Montgomery curve in projective coordinates.

**Source**: curve25519-dalek/src/montgomery.rs:L296-L301
-/

open Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.IdentityMontgomeryProjectivePoint

/-
natural language description:

• Returns the identity element (point at infinity) of the Montgomery curve in projective
  coordinates (U, W)

natural language specs:

• The function always succeeds (no panic)
• The resulting ProjectivePoint is the identity element with coordinates:
  - U = 1
  - W = 0
• In projective coordinates on Montgomery curve, this represents the point at infinity
• The Montgomery curve uses the form: B*v² = u³ + A*u² + u
• In projective coordinates (U:W), the affine coordinate is u = U/W
• When W = 0, this represents the point at infinity (identity element)
-/

/-- **Spec and proof concerning `montgomery.IdentityProjectivePoint.identity`**:
- No panic (always returns successfully)
- The resulting ProjectivePoint is the identity element with coordinates (U=1, W=0)
-/
@[progress]
theorem identity_spec :
    spec identity (fun q =>
    q.U = ONE ∧ q.W = ZERO) := by
  unfold identity
  simp

end curve25519_dalek.IdentityMontgomeryProjectivePoint
