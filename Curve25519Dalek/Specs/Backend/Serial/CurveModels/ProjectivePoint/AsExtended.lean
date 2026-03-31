/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
/-! # Spec Theorem for `ProjectivePoint::as_extended`

Specification and proof for `ProjectivePoint::as_extended`.

This function implements point conversion from projective coordinates (ℙ²) to extended
twisted Edwards coordinates (ℙ³) on the Curve25519 elliptic curve. Given a point
P = (X:Y:Z) in projective coordinates, it computes an equivalent representation
(X':Y':Z':T') in extended coordinates.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/-
natural language description:

• Takes a ProjectivePoint with coordinates (X, Y, Z) in projective ℙ² representation and
returns an EdwardsPoint (X', Y', Z', T') in extended ℙ³ representation. Arithmetics are performed in the
field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given  an input projective point (X, Y, Z), the output EdwardsPoint (X', Y', Z', T') satisfies:
- X' ≡ X·Z (mod p)
- Y' ≡ Y·Z (mod p)
- Z' ≡ Z² (mod p)
- T' ≡ X·Y (mod p)

Note: We compute the output representation (XZ, YZ, Z², XY) instead of the equivalent
(and seemingly more straightforward) representation (X, Y, Z, XY/Z) because the former
representation can be obtained without performing any divisions.
-/

/-- **Spec and proof concerning `backend.serial.curve_models.ProjectivePoint.as_extended`**:
- No panic (always returns successfully)
- Given input ProjectivePoint with coordinates (X, Y, Z), the output EdwardsPoint (X', Y', Z', T')
satisfies the conversion formulas modulo p:
- X' ≡ X·Z (mod p)
- Y' ≡ Y·Z (mod p)
- Z' ≡ Z² (mod p)
- T' ≡ X·Y (mod p)
where p = 2^255 - 19
These formulas implement the (division-free) conversion from projective ℙ² coordinates to extended
twisted Edwards ℙ³ coordinates.
-/
@[step]
theorem as_extended_spec (q : ProjectivePoint)
    (h_qX_bounds : ∀ i, i < 5 → (q.X[i]!).val < 2 ^ 54)
    (h_qY_bounds : ∀ i, i < 5 → (q.Y[i]!).val < 2 ^ 54)
    (h_qZ_bounds : ∀ i, i < 5 → (q.Z[i]!).val < 2 ^ 54) :
    as_extended q ⦃ e =>
      let X := Field51_as_Nat q.X
      let Y := Field51_as_Nat q.Y
      let Z := Field51_as_Nat q.Z
      let X' := Field51_as_Nat e.X
      let Y' := Field51_as_Nat e.Y
      let Z' := Field51_as_Nat e.Z
      let T' := Field51_as_Nat e.T
      X' % p = (X * Z) % p ∧
      Y' % p = (Y * Z) % p ∧
      Z' % p = (Z^2) % p ∧
      T' % p = (X * Y) % p ⦄ := by
  unfold as_extended
  step*
  rw[← Nat.ModEq,← Nat.ModEq,← Nat.ModEq, ← Nat.ModEq]
  simp_all

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
