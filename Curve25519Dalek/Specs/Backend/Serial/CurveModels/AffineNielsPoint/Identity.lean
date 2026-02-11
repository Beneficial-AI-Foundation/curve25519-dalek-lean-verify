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

Specification and proof for `AffineNielsPoint::identity`.

This function returns the identity element of the Edwards curve in AffineNiels coordinates.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs:L258-L264
-/

open Aeneas.Std Result curve25519_dalek
open backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.backend.serial.curve_models.IdentityAffineNielsPoint

/-
natural language description:

• Returns the identity element of the Edwards curve in AffineNiels coordinates
  (y_plus_x, y_minus_x, xy2d)

natural language specs:

• The function always succeeds (no panic)
• The resulting AffineNielsPoint is the identity element with coordinates:
  - y_plus_x = 1
  - y_minus_x = 1
  - xy2d = 0
• This represents the affine point:
  - x = (y_plus_x - y_minus_x)/2 = (1-1)/2 = 0
  - y = (y_plus_x + y_minus_x)/2 = (1+1)/2 = 1
  which is the identity element (0, 1) on the Edwards curve
• Note: xy2d = 2*d*x*y = 2*d*0*1 = 0
-/

/-- **Spec and proof concerning `backend.serial.curve_models.IdentityAffineNielsPoint.identity`**:
- No panic (always returns successfully)
- The resulting AffineNielsPoint is the identity element with coordinates
  (y_plus_x=1, y_minus_x=1, xy2d=0)
-/
@[progress]
theorem identity_spec :
    ∃ q, identity = ok q ∧
    q.y_plus_x = ONE ∧ q.y_minus_x = ONE ∧ q.xy2d = ZERO := by
  unfold identity
  simp

end curve25519_dalek.backend.serial.curve_models.IdentityAffineNielsPoint
