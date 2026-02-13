/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Math.Edwards.Representation

/-! # Spec Theorem for `CompletedPoint::as_projective`

Specification and proof for `CompletedPoint::as_projective`.

This function implements point conversion from completed coordinates (ℙ¹ × ℙ¹) to projective
coordinates (ℙ²) on the Curve25519 elliptic curve. Given a point P = (X:Y:Z:T) in
completed coordinates (i.e., with affine coordinates given via X/Z = x and Y/T = y),
it computes an equivalent representation (X':Y':Z') in projective
coordinates (i.e., with X'/Z' = x and Y'/Z' = y).

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

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
∃ proj,
as_projective q = ok proj ∧
let X := Field51_as_Nat q.X
let Y := Field51_as_Nat q.Y
let Z := Field51_as_Nat q.Z
let T := Field51_as_Nat q.T
let X' := Field51_as_Nat proj.X
let Y' := Field51_as_Nat proj.Y
let Z' := Field51_as_Nat proj.Z
X' % p = (X * T) % p ∧
Y' % p = (Y * Z) % p ∧
Z' % p = (Z * T) % p ∧
-- Output bounds: mul produces < 2^52
(∀ i < 5, proj.X[i]!.val < 2 ^ 52) ∧
(∀ i < 5, proj.Y[i]!.val < 2 ^ 52) ∧
(∀ i < 5, proj.Z[i]!.val < 2 ^ 52)
:= by
  unfold as_projective
  progress*
  rw[← Nat.ModEq,← Nat.ModEq,← Nat.ModEq]
  simp_all

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
  -- Extract bounds from validity
  have h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 54 := hq_valid.X_valid
  have h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 54 := hq_valid.Y_valid
  have h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val < 2 ^ 54 := hq_valid.Z_valid
  have h_qT_bounds : ∀ i < 5, (q.T[i]!).val < 2 ^ 54 := hq_valid.T_valid

  -- Use auxiliary spec
  obtain ⟨proj, h_run, hX_arith, hY_arith, hZ_arith, hpX_bounds, hpY_bounds, hpZ_bounds⟩ :=
    as_projective_spec_aux q h_qX_bounds h_qY_bounds h_qZ_bounds h_qT_bounds

  use proj
  constructor
  · exact h_run

  -- Lift arithmetic to field equalities
  have hX_F : proj.X.toField = q.X.toField * q.T.toField := by
    unfold toField
    have h := lift_mod_eq _ _ hX_arith
    push_cast at h
    exact h

  have hY_F : proj.Y.toField = q.Y.toField * q.Z.toField := by
    unfold toField
    have h := lift_mod_eq _ _ hY_arith
    push_cast at h
    exact h

  have hZ_F : proj.Z.toField = q.Z.toField * q.T.toField := by
    unfold toField
    have h := lift_mod_eq _ _ hZ_arith
    push_cast at h
    exact h

  -- Prove proj.Z.toField ≠ 0
  have hpZ_ne : proj.Z.toField ≠ 0 := by
    rw [hZ_F]
    apply mul_ne_zero hq_valid.Z_ne_zero hq_valid.T_ne_zero

  constructor
  · -- Prove proj.IsValid
    exact {
      X_bounds := hpX_bounds
      Y_bounds := hpY_bounds
      Z_bounds := hpZ_bounds
      Z_ne_zero := hpZ_ne
      on_curve := by
        -- proj represents (X*T/(Z*T), Y*Z/(Z*T)) = (X/Z, Y/T) = q's affine point
        -- Need to show: a*(X')²*(Z')² + (Y')²*(Z')² = (Z')⁴ + d*(X')²*(Y')²
        simp only [hX_F, hY_F, hZ_F]
        have h_curve := hq_valid.on_curve
        simp only [Ed25519] at h_curve ⊢
        ring_nf
        ring_nf at h_curve
        -- The curve equation for CompletedPoint is:
        -- a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y²
        -- After substitution: a*(X*T)²*(Z*T)² + (Y*Z)²*(Z*T)² = (Z*T)⁴ + d*(X*T)²*(Y*Z)²
        -- Which simplifies to: (Z*T)² * (a*X²*T² + Y²*Z²) = (Z*T)² * (Z²*T² + d*X²*Y²)
        -- This follows from h_curve
        linear_combination (q.Z.toField ^ 2 * q.T.toField ^ 2) * h_curve
    }

  · -- Prove proj.toPoint = q.toPoint
    have h_proj_valid : proj.IsValid := {
      X_bounds := hpX_bounds
      Y_bounds := hpY_bounds
      Z_bounds := hpZ_bounds
      Z_ne_zero := hpZ_ne
      on_curve := by
        simp only [hX_F, hY_F, hZ_F]
        have h_curve := hq_valid.on_curve
        simp only [Ed25519] at h_curve ⊢
        linear_combination (q.Z.toField ^ 2 * q.T.toField ^ 2) * h_curve
    }

    have ⟨h_px, h_py⟩ := ProjectivePoint.toPoint_of_isValid h_proj_valid
    have ⟨h_qx, h_qy⟩ := CompletedPoint.toPoint_of_isValid hq_valid

    ext
    · -- x coordinate: proj.toPoint.x = q.toPoint.x
      -- proj.toPoint.x = X'/Z' = (X*T)/(Z*T) = X/Z (when T ≠ 0)
      -- q.toPoint.x = X/Z
      rw [h_px, hX_F, hZ_F, h_qx]
      field_simp [hq_valid.Z_ne_zero, hq_valid.T_ne_zero]
    · -- y coordinate: proj.toPoint.y = q.toPoint.y
      -- proj.toPoint.y = Y'/Z' = (Y*Z)/(Z*T) = Y/T (when Z ≠ 0)
      -- q.toPoint.y = Y/T
      rw [h_py, hY_F, hZ_F, h_qy]
      field_simp [hq_valid.Z_ne_zero, hq_valid.T_ne_zero]

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
