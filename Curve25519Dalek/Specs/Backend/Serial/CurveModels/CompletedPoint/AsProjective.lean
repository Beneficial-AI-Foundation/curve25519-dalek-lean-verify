/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `CompletedPoint::as_projective`

Specification and proof for `CompletedPoint::as_projective`.

This function implements point conversion from completed coordinates (ℙ¹ × ℙ¹) to projective
coordinates (ℙ²) on the Curve25519 elliptic curve. Given a point P = (X:Y:Z:T) in
completed coordinates (i.e., with affine coordinates given via X/Z = x and Y/T = y),
it computes an equivalent representation (X':Y':Z') in projective
coordinates (i.e., with X'/Z' = x and Y'/Z' = y).

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-
natural language description:

• Takes a CompletedPoint with coordinates (X, Y, Z, T) in completed ℙ¹ × ℙ¹ representation
(i.e., with affine coordinates given via X/Z = x and Y/T = y) and returns a ProjectivePoint
(X', Y', Z') in projective ℙ² representation (i.e., with X'/Z' = x and Y'/Z' = y).
Arithmetics are performed in the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given an input completed point (X, Y, Z, T), the output ProjectivePoint (X', Y', Z') satisfies:
- X' ≡ X·T (mod p)
- Y' ≡ Y·Z (mod p)
- Z' ≡ Z·T (mod p)
-/

/-- **Auxiliary spec for `as_projective`** proving arithmetic correctness.
Input bounds: all coordinates < 2^54.
Output: arithmetic relations modulo p. -/
@[progress]
theorem as_projective_spec_aux (q : CompletedPoint)
  (h_qX_bounds : ∀ i, i < 5 → (q.X[i]!).val < 2 ^ 54)
  (h_qY_bounds : ∀ i, i < 5 → (q.Y[i]!).val < 2 ^ 54)
  (h_qZ_bounds : ∀ i, i < 5 → (q.Z[i]!).val < 2 ^ 54)
  (h_qT_bounds : ∀ i, i < 5 → (q.T[i]!).val < 2 ^ 54) :
  as_projective q ⦃ proj =>
    let X := Field51_as_Nat q.X;
    let Y := Field51_as_Nat q.Y;
    let Z := Field51_as_Nat q.Z;
    let T := Field51_as_Nat q.T;
    let X' := Field51_as_Nat proj.X;
    let Y' := Field51_as_Nat proj.Y;
    let Z' := Field51_as_Nat proj.Z;
    X' % p = (X * T) % p ∧
    Y' % p = (Y * Z) % p ∧
    Z' % p = (Z * T) % p ∧
    (∀ i < 5, proj.X[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, proj.Y[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, proj.Z[i]!.val < 2 ^ 52) ⦄ := by
  sorry

end curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-! ## High-level spec using validity predicates

This section proves that `as_projective` preserves validity and the represented point.
-/

namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

open Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/--
Verification of the `as_projective` function.
The theorem states that converting a valid CompletedPoint to ProjectivePoint:
1. Always succeeds
2. Produces a valid ProjectivePoint
3. Preserves the represented affine point
-/
theorem as_projective_spec
    (q : CompletedPoint) (hq_valid : q.IsValid) :
    ∃ proj, as_projective q = ok proj ∧
    proj.IsValid ∧ proj.toPoint = q.toPoint := by
  sorry

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
