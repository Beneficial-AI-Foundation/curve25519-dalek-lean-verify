/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Defs.Edwards.Curve
import Curve25519Dalek.Defs.Edwards.Representation
import Mathlib.Data.ZMod.Basic

set_option linter.hashCommand false
#setup_aeneas_simps

/-! # Spec Theorem for `ProjectivePoint::double`

Specification and proof for `ProjectivePoint::double`.

This function implements point doubling on the Curve25519 elliptic curve using projective
coordinates. Given a point P = (X:Y:Z), it computes 2P (the point added to itself via
elliptic curve addition).

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result

open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51
open curve25519_dalek.backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51

namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/-
natural language description:

• Takes a ProjectivePoint with coordinates (X, Y, Z) and returns a CompletedPoint that results
from adding the input point to itself via elliptic curve point addition. Arithmetics are
performed in the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given input point (X, Y, Z), the output CompletedPoint (X', Y', Z', T') satisfies:
- X' ≡ 2XY (mod p)
- Y' ≡ Y² + X² (mod p)
- Z' ≡ Y² - X² (mod p)
- T' ≡ 2Z² - Y² + X² (mod p)
-/

set_option maxHeartbeats 1000000 in
-- simp_all is heavy
/-- **Spec and proof concerning `backend.serial.curve_models.ProjectivePoint.double`**:
- No panic (always returns successfully)
- Given input ProjectivePoint with coordinates (X, Y, Z), the output CompletedPoint (X', Y', Z', T')
satisfies the point doubling formulas modulo p:
- X' ≡ 2XY (mod p)
- Y' ≡ Y² + X² (mod p)
- Z' ≡ Y² - X² (mod p)
- T' ≡ 2Z² - Y² + X² (mod p)
where p = 2^255 - 19
These formulas implement Edwards curve point doubling, computing P + P
(elliptic curve point addition) where P = (X:Y:Z).

Input bounds: X, Y limbs < 2^53 (for X + Y < 2^54), Z limbs < 2^54.
Output bounds: X', Z', T' limbs < 2^52, Y' limbs < 2^53.
-/
@[progress]
theorem double_spec_aux (q : ProjectivePoint)
    (h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 53)
    (h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 53)
    (h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val < 2 ^ 54) :
    double q ⦃ c =>
      let X := Field51_as_Nat q.X
      let Y := Field51_as_Nat q.Y
      let Z := Field51_as_Nat q.Z
      let X' := Field51_as_Nat c.X
      let Y' := Field51_as_Nat c.Y
      let Z' := Field51_as_Nat c.Z
      let T' := Field51_as_Nat c.T
      X' % p = (2 * X * Y) % p ∧
      Y' % p = (Y^2 + X^2) % p ∧
      (Z' + X^2) % p = Y^2 % p ∧
      (T' + Z') % p = (2 * Z^2) % p ∧
      (∀ i < 5, c.X[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, c.Y[i]!.val < 2 ^ 53) ∧
      (∀ i < 5, c.Z[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, c.T[i]!.val < 2 ^ 52) ⦄ := by
  sorry


theorem double_spec (q : ProjectivePoint) (hq : q.IsValid) :
    ∃ c, double q = ok c ∧ c.IsValid ∧ c.toPoint = q.toPoint + q.toPoint := by
  sorry

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
