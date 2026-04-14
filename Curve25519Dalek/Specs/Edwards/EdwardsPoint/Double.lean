/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang, Filippo A. E. Nuccio
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Mathlib

/-! # Spec Theorem for `EdwardsPoint::double`

Specification and proof for `EdwardsPoint::double`.

This function doubles an Edwards point (adds it to itself) using elliptic curve point addition.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.EdwardsPoint
/-new-/
open Edwards backend.serial.curve_models backend.serial.curve_models.ProjectivePoint
  backend.serial.u64.field

-- The `linear_combination` steps require extra heartbeats
-- for the algebraic verification of the curve equation.
attribute [local irreducible] p in
/-- **Spec and proof concerning
`edwards.EdwardsPoint.double`**:
- Returns the doubled point 2P (= P + P in elliptic
  curve addition) where P is the input EdwardsPoint -/
@[step]
theorem double_spec (e : EdwardsPoint) (he_valid : e.IsValid) :
    double e ⦃ result =>
    result.IsValid ∧ result.toPoint = e.toPoint + e.toPoint ⦄ := by
  unfold double
  -- Step 1: as_projective (preserves X, Y, Z)
  apply WP.spec_bind
    (edwards.EdwardsPoint.as_projective_spec e)
  intro pp ⟨hpp_X, hpp_Y, hpp_Z⟩
  -- Build pp.OnCurve from e.IsValid
  have hpp_on : pp.OnCurve := {
    Z_ne_zero := by rw [hpp_Z]; exact he_valid.Z_ne_zero
    on_curve := by rw [hpp_X, hpp_Y, hpp_Z]; exact he_valid.on_curve
  }
  -- Step 2: double via core theorem (existential form)
  obtain ⟨cp, h_run, h_cp_valid, h_cp_eq⟩ :=
    double_spec_core pp hpp_on
      (fun i hi => by rw [hpp_X]; exact he_valid.X_bounds i hi)
      (fun i hi => by rw [hpp_Y]; exact he_valid.Y_bounds i hi)
      (by rw [hpp_Z]
          exact FieldElement51.IsValid_of_lt_pow
            he_valid.Z_bounds (by decide))
  -- Thread pp.double = ok cp through the WP chain
  simp only [h_run]
  -- Step 3: as_extended (preserves the point)
  apply WP.spec_mono
    (CompletedPoint.as_extended_spec cp h_cp_valid)
  intro result
    ⟨_, _, _, _, _, _, _, _,
     h_result_valid, h_result_toPoint⟩
  exact ⟨h_result_valid, by
    rw [h_result_toPoint, h_cp_eq]
    congr 1 <;>
      simp only [ProjectivePoint.toPoint',
        hpp_X, hpp_Y, hpp_Z,
        EdwardsPoint.toPoint, dif_pos he_valid,
        EdwardsPoint.toPoint']⟩

end curve25519_dalek.edwards.EdwardsPoint
