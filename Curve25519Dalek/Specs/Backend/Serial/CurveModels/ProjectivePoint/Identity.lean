/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE


/-! # identity

Specification and proof for `ProjectivePoint::identity`.

This function returns the identity element of the Edwards curve in projective coordinates.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs:L231-L237
-/

open Aeneas.Std Result curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.backend.serial.curve_models.IdentityProjectivePoint

/-
natural language description:

• Returns the identity element of the Edwards curve in projective coordinates (X, Y, Z)

natural language specs:

• The function always succeeds (no panic)
• The resulting ProjectivePoint is the identity element with coordinates (X=0, Y=1, Z=1)
• In projective coordinates, this represents the affine point (X/Z, Y/Z) = (0, 1), which is
  the identity element on the Edwards curve
-/

/-- **Spec and proof concerning `backend.serial.curve_models.IdentityProjectivePoint.identity`**:
- No panic (always returns successfully)
- The resulting ProjectivePoint is the identity element with coordinates (X=0, Y=1, Z=1)
-/
@[progress]
theorem identity_spec :
    ∃ q, identity = ok q ∧
    q.X = ZERO ∧ q.Y = ONE ∧ q.Z = ONE := by
  unfold identity
  simp

end curve25519_dalek.backend.serial.curve_models.IdentityProjectivePoint
