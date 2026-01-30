/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE


/-! # identity

Specification and proof for `ProjectiveNielsPoint::identity`.

This function returns the identity element of the Edwards curve in ProjectiveNiels coordinates.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs:L241-L248
-/

open Aeneas.Std Result curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.backend.serial.curve_models.IdentityProjectiveNielsPoint

/-
natural language description:

• Returns the identity element of the Edwards curve in ProjectiveNiels coordinates
  (Y_plus_X, Y_minus_X, Z, T2d)

natural language specs:

• The function always succeeds (no panic)
• The resulting ProjectiveNielsPoint is the identity element with coordinates:
  - Y_plus_X = 1
  - Y_minus_X = 1
  - Z = 1
  - T2d = 0
• This represents the affine point:
  - x = (Y_plus_X - Y_minus_X)/(2*Z) = (1-1)/(2*1) = 0
  - y = (Y_plus_X + Y_minus_X)/(2*Z) = (1+1)/(2*1) = 1
  which is the identity element (0, 1) on the Edwards curve
-/

/-- **Spec and proof concerning `backend.serial.curve_models.IdentityProjectiveNielsPoint.identity`**:
- No panic (always returns successfully)
- The resulting ProjectiveNielsPoint is the identity element with coordinates
  (Y_plus_X=1, Y_minus_X=1, Z=1, T2d=0)
-/
@[progress]
theorem identity_spec :
    ∃ q, identity = ok q ∧
    q.Y_plus_X = ONE ∧ q.Y_minus_X = ONE ∧ q.Z = ONE ∧ q.T2d = ZERO := by
  unfold identity
  simp

end curve25519_dalek.backend.serial.curve_models.IdentityProjectiveNielsPoint
