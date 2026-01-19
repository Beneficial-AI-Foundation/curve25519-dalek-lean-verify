/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EDWARDS_D

/-! # Spec Theorem for `ProjectivePoint::is_valid`

Specification and proof for `ProjectivePoint::is_valid`.

This function checks whether a projective point (X:Y:Z) satisfies the twisted Edwards
curve equation for Ed25519. The curve equation in projective coordinates is:
  a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y²

where a = -1 for Ed25519. This can be rewritten as:
  (Y² - X²)*Z² = Z⁴ + d*X²*Y²

The function computes both sides of this equation and checks equality.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.curve_models.ValidityCheckProjectivePoint

open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.u64.constants

/-
Natural language description:

  • Takes a ProjectivePoint with coordinates (X, Y, Z) and checks if it satisfies
    the twisted Edwards curve equation in projective form.

  • This checks the Edwards curve equation: a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y²
    which simplifies to (Y² - X²)*Z² = Z⁴ + d*X²*Y² when a = -1.

-/

/-- **Spec and proof concerning `backend.serial.curve_models.ValidityCheckProjectivePoint.is_valid`**:
- No panic (always returns successfully)
- Returns true iff the projective point (X:Y:Z) satisfies the twisted Edwards curve equation:
    (Y² - X²)*Z² ≡ Z⁴ + d*X²*Y² (mod p)
  where p = 2^255 - 19 and d is the Ed25519 curve parameter.

-/
@[progress]
theorem is_valid_spec (self : backend.serial.curve_models.ProjectivePoint)
    (h_X_valid : self.X.IsValid)
    (h_Y_valid : self.Y.IsValid)
    (h_Z_valid : self.Z.IsValid) :
    ∃ result, is_valid self = ok result ∧
    (result = true ↔
      let X := Field51_as_Nat self.X
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      ((Y^2 - X^2) * Z^2) % p = (Z^4 + d * X^2 * Y^2) % p) := by
  sorry

end curve25519_dalek.backend.serial.curve_models.ValidityCheckProjectivePoint
