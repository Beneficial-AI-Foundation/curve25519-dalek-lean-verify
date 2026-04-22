/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Math.Edwards.Representation
/-!
# Spec theorem for `CompletedPoint::as_projective`

Specification and proof for `CompletedPoint::as_projective`.

This function implements point conversion from completed coordinates (ℙ¹ × ℙ¹) to projective
coordinates (ℙ²) on the Curve25519 elliptic curve. Given a point P = (X:Y:Z:T) in
completed coordinates (i.e., with affine coordinates given via X/Z = x and Y/T = y),
it computes an equivalent representation (X':Y':Z') in projective
coordinates (i.e., with X'/Z' = x and Y'/Z' = y).

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
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
Output: arithmetic relations modulo p.

The point-level `as_projective_spec` (WP form, takes `IsValid` and
returns `IsValid ∧ toPoint = toPoint`) is the canonical chain target. -/
theorem as_projective_spec_aux (q : CompletedPoint)
    (h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 54)
    (h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 54)
    (h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val < 2 ^ 54)
    (h_qT_bounds : ∀ i < 5, (q.T[i]!).val < 2 ^ 54) :
    as_projective q ⦃ (proj : ProjectivePoint) =>
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
      (∀ i < 5, proj.Z[i]!.val < 2 ^ 52) ⦄ := by
  unfold as_projective
  step*
  rw [← Nat.ModEq, ← Nat.ModEq, ← Nat.ModEq]
  simp_all

end curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-! ## High-level spec using validity predicates

This section proves that `as_projective` preserves validity and the represented point.
-/

namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

open Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Independent sub-lemmas for `as_projective_spec`

These lemmas factor out the key proof steps used in the main theorem:
1. `as_projective_lift_to_field_eqs`: Lift modular arithmetic to field equalities
2. `as_projective_on_curve`: Prove the projective on-curve equation from the
   completed on-curve equation
3. `as_projective_isValid_and_toPoint`: Combined validity and point equality proof
-/

/-- Lift the three modular arithmetic results from `as_projective_spec_aux` to
    field equalities in `CurveField`. Each modular relation `a % p = b % p`
    is lifted via `lift_mod_eq` and then simplified via `push_cast`. -/
private lemma as_projective_lift_to_field_eqs
    (proj : ProjectivePoint)
    (q : CompletedPoint)
    (hX_arith : Field51_as_Nat proj.X % p = (Field51_as_Nat q.X * Field51_as_Nat q.T) % p)
    (hY_arith : Field51_as_Nat proj.Y % p = (Field51_as_Nat q.Y * Field51_as_Nat q.Z) % p)
    (hZ_arith : Field51_as_Nat proj.Z % p = (Field51_as_Nat q.Z * Field51_as_Nat q.T) % p) :
    proj.X.toField = q.X.toField * q.T.toField ∧
    proj.Y.toField = q.Y.toField * q.Z.toField ∧
    proj.Z.toField = q.Z.toField * q.T.toField := by
  constructor
  · unfold toField
    have h := lift_mod_eq _ _ hX_arith
    push_cast at h
    exact h
  constructor
  · unfold toField
    have h := lift_mod_eq _ _ hY_arith
    push_cast at h
    exact h
  · unfold toField
    have h := lift_mod_eq _ _ hZ_arith
    push_cast at h
    exact h

/-- Prove the projective on-curve equation from the completed on-curve equation.
    Given that `proj.X = q.X * q.T`, `proj.Y = q.Y * q.Z`, `proj.Z = q.Z * q.T`,
    the projective curve equation `a * X'² * Z'² + Y'² * Z'² = Z'⁴ + d * X'² * Y'²`
    follows from the completed curve equation
    `a * X² * T² + Y² * Z² = Z² * T² + d * X² * Y²`
    by scaling both sides by `(Z * T)²`. -/
private lemma as_projective_on_curve
    (pX pY pZ qX qY qZ qT : Edwards.CurveField)
    (hX_F : pX = qX * qT)
    (hY_F : pY = qY * qZ)
    (hZ_F : pZ = qZ * qT)
    (h_curve : Ed25519.a * qX ^ 2 * qT ^ 2 + qY ^ 2 * qZ ^ 2 =
               qZ ^ 2 * qT ^ 2 + Ed25519.d * qX ^ 2 * qY ^ 2) :
    Ed25519.a * pX ^ 2 * pZ ^ 2 + pY ^ 2 * pZ ^ 2 =
    pZ ^ 4 + Ed25519.d * pX ^ 2 * pY ^ 2 := by
  simp only [hX_F, hY_F, hZ_F]
  simp only [Ed25519] at h_curve ⊢
  linear_combination (qZ ^ 2 * qT ^ 2) * h_curve

/-- Combined proof of validity and point equality for `as_projective`.
    Given the field equalities, bounds, and the input's validity, this lemma proves
    that the output `ProjectivePoint` is valid and represents the same affine point
    as the input `CompletedPoint`. -/
private lemma as_projective_isValid_and_toPoint
    (proj : ProjectivePoint)
    (q : CompletedPoint) (hq_valid : q.IsValid)
    (hX_F : proj.X.toField = q.X.toField * q.T.toField)
    (hY_F : proj.Y.toField = q.Y.toField * q.Z.toField)
    (hZ_F : proj.Z.toField = q.Z.toField * q.T.toField)
    (hpX_bounds : ∀ i < 5, proj.X[i]!.val < 2 ^ 52)
    (hpY_bounds : ∀ i < 5, proj.Y[i]!.val < 2 ^ 52)
    (hpZ_bounds : ∀ i < 5, proj.Z[i]!.val < 2 ^ 52) :
    proj.IsValid ∧ proj.toPoint = q.toPoint := by
  -- Prove proj.Z.toField ≠ 0
  have hpZ_ne : proj.Z.toField ≠ 0 := by
    rw [hZ_F]
    apply mul_ne_zero hq_valid.Z_ne_zero hq_valid.T_ne_zero
  -- Prove on-curve using the extracted lemma
  have h_on_curve : Ed25519.a * proj.X.toField ^ 2 * proj.Z.toField ^ 2 +
      proj.Y.toField ^ 2 * proj.Z.toField ^ 2 =
      proj.Z.toField ^ 4 + Ed25519.d * proj.X.toField ^ 2 * proj.Y.toField ^ 2 :=
    as_projective_on_curve proj.X.toField proj.Y.toField proj.Z.toField
      q.X.toField q.Y.toField q.Z.toField q.T.toField
      hX_F hY_F hZ_F hq_valid.on_curve
  -- Construct IsValid
  have h_proj_valid : proj.IsValid := {
    X_bounds := hpX_bounds
    Y_bounds := hpY_bounds
    Z_bounds := hpZ_bounds
    Z_ne_zero := hpZ_ne
    on_curve := h_on_curve
  }
  constructor
  · exact h_proj_valid
  · -- Prove proj.toPoint = q.toPoint
    have ⟨h_px, h_py⟩ := ProjectivePoint.toPoint_of_isValid h_proj_valid
    have ⟨h_qx, h_qy⟩ := CompletedPoint.toPoint_of_isValid hq_valid
    ext
    · -- x coordinate: X'/Z' = (X*T)/(Z*T) = X/Z
      rw [h_px, hX_F, hZ_F, h_qx]
      field_simp [hq_valid.Z_ne_zero, hq_valid.T_ne_zero]
    · -- y coordinate: Y'/Z' = (Y*Z)/(Z*T) = Y/T
      rw [h_py, hY_F, hZ_F, h_qy]
      field_simp [hq_valid.Z_ne_zero, hq_valid.T_ne_zero]

/--
Verification of the `as_projective` function (WP form, canonical chain target).

The theorem states that converting a valid CompletedPoint to ProjectivePoint:
1. Always succeeds
2. Produces a valid ProjectivePoint
3. Preserves the represented affine point
-/
@[step]
theorem as_projective_spec
    (q : CompletedPoint) (hq_valid : q.IsValid) :
    as_projective q ⦃ (proj : ProjectivePoint) =>
      proj.IsValid ∧ proj.toPoint = q.toPoint ⦄ := by
  -- Extract bounds from validity
  have h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 54 := hq_valid.X_valid
  have h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 54 := hq_valid.Y_valid
  have h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val < 2 ^ 54 := hq_valid.Z_valid
  have h_qT_bounds : ∀ i < 5, (q.T[i]!).val < 2 ^ 54 := hq_valid.T_valid
  -- Use auxiliary spec, then strengthen its post to the point-level form.
  apply WP.spec_mono
    (as_projective_spec_aux q h_qX_bounds h_qY_bounds h_qZ_bounds h_qT_bounds)
  intro proj ⟨hX_arith, hY_arith, hZ_arith, hpX_bounds, hpY_bounds, hpZ_bounds⟩
  -- Lift arithmetic to field equalities.
  have ⟨hX_F, hY_F, hZ_F⟩ :=
    as_projective_lift_to_field_eqs proj q hX_arith hY_arith hZ_arith
  -- Combine validity and point equality.
  exact as_projective_isValid_and_toPoint proj q hq_valid
    hX_F hY_F hZ_F hpX_bounds hpY_bounds hpZ_bounds

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
