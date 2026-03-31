/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
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

-- The `linear_combination` steps require extra heartbeats
-- for the algebraic verification of the curve equation.
attribute [local irreducible] p in
/-- **Spec and proof concerning
`edwards.EdwardsPoint.double`**:
- Returns the doubled point 2P (= P + P in elliptic
  curve addition) where P is the input EdwardsPoint -/
@[externally_verified, step] -- proven in Verus
theorem double_spec (e : EdwardsPoint) (he_valid : e.IsValid) :
    double e ⦃ result =>
    result.IsValid ∧ result.toPoint = e.toPoint + e.toPoint ⦄ := by
    -- Unfold the double function:
  -- double e = do
  --   let pp ← as_projective e
  --   let cp ← ProjectivePoint.double pp
  --   as_extended cp
  unfold edwards.EdwardsPoint.double
  -- Step 1: as_projective (preserves X, Y, Z)
  apply WP.spec_bind
    (edwards.EdwardsPoint.as_projective_spec e)
  intro pp ⟨hpp_X, hpp_Y, hpp_Z⟩
  -- Bounds for double_spec_aux (< 2^53 from IsValid)
  have hX_bounds :
      ∀ i < 5, pp.X[i]!.val < 2 ^ 53 := by
    intro i hi; rw [hpp_X]
    exact he_valid.X_bounds i hi
  have hY_bounds :
      ∀ i < 5, pp.Y[i]!.val < 2 ^ 53 := by
    intro i hi; rw [hpp_Y]
    exact he_valid.Y_bounds i hi
  have hZ_bounds :
      ∀ i < 5, pp.Z[i]!.val < 2 ^ 54 := by
    intro i hi; rw [hpp_Z]
    exact Nat.lt_trans (he_valid.Z_bounds i hi)
      (by norm_num : 2 ^ 53 < 2 ^ 54)
  -- Step 2: ProjectivePoint.double
  apply WP.spec_bind
    (double_spec_aux pp
      hX_bounds hY_bounds hZ_bounds)
  intro cp
    ⟨hX_arith, hY_arith, hZ_arith, hT_arith,
     hcX_bounds, hcY_bounds,
     hcZ_bounds, hcT_bounds⟩
  -- Lift modular arithmetic to field equations
  obtain ⟨hX_F, hY_F, hZ_F, hT_F⟩ :=
    double_lift_to_field_eqs cp pp
      hX_arith hY_arith hZ_arith hT_arith
  -- Rewrite field eqs to use e's coordinates
  rw [hpp_X, hpp_Y] at hX_F
  rw [hpp_X, hpp_Y] at hY_F
  rw [hpp_X, hpp_Y] at hZ_F
  rw [hpp_Z] at hT_F
  -- Setup: curve equation and non-zero denominators
  have hZ_ne : e.Z.toField ≠ 0 := he_valid.Z_ne_zero
  set X := e.X.toField with hX_def
  set Y := e.Y.toField with hY_def
  set Z := e.Z.toField with hZ_def
  have h_curve :
      Ed25519.a * X ^ 2 * Z ^ 2 +
        Y ^ 2 * Z ^ 2 =
      Z ^ 4 + Ed25519.d * X ^ 2 * Y ^ 2 :=
    he_valid.on_curve
  -- Affine coordinates
  set x := X / Z with hx_def
  set y := Y / Z with hy_def
  have hz2 : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ_ne
  have hz4 : Z ^ 4 ≠ 0 := pow_ne_zero 4 hZ_ne
  -- Affine curve equation
  have h_P_on_curve :
      Ed25519.a * x ^ 2 + y ^ 2 =
        1 + Ed25519.d * x ^ 2 * y ^ 2 := by
    simp only [Ed25519] at h_curve ⊢
    simp only [hx_def, hy_def, div_pow]
    field_simp [hz2, hz4]
    linear_combination h_curve
  -- Completeness: denominators are non-zero
  let P : Point Ed25519 := ⟨x, y, h_P_on_curve⟩
  have h_denoms := Ed25519.denomsNeZero P P
  have h_denom_plus :
      1 + Ed25519.d * x ^ 2 * y ^ 2 ≠ 0 := by
    have h := h_denoms.1
    simp only [P] at h
    convert h using 2; ring
  have h_denom_minus :
      1 - Ed25519.d * x ^ 2 * y ^ 2 ≠ 0 := by
    have h := h_denoms.2
    simp only [P] at h
    convert h using 2; ring
  -- Key: y² - x² = 1 + d*x²*y² (since a = -1)
  have h_yx_sq :
      y ^ 2 - x ^ 2 =
        1 + Ed25519.d * x ^ 2 * y ^ 2 := by
    calc y ^ 2 - x ^ 2
        = -1 * x ^ 2 + y ^ 2 := by ring
      _ = Ed25519.a * x ^ 2 + y ^ 2 := by
          simp only [Ed25519]
      _ = 1 + Ed25519.d * x ^ 2 * y ^ 2 :=
          h_P_on_curve
  -- Y² - X² = Z² * (y² - x²)
  have h_YX_factor :
      Y ^ 2 - X ^ 2 =
        Z ^ 2 * (y ^ 2 - x ^ 2) := by
    simp only [hx_def, hy_def, div_pow]
    field_simp [hZ_ne]
  -- 2Z² - (Y² - X²) = Z² * (1 - d*x²*y²)
  have h_denom_factor :
      2 * Z ^ 2 - (Y ^ 2 - X ^ 2) =
        Z ^ 2 *
          (1 - Ed25519.d * x ^ 2 * y ^ 2) := by
    rw [h_YX_factor, h_yx_sq]; ring
  -- Prove CompletedPoint validity
  have hcX_valid : cp.X.IsValid :=
    fun i hi => Nat.lt_trans (hcX_bounds i hi)
      (by norm_num : 2 ^ 52 < 2 ^ 54)
  have hcY_valid : cp.Y.IsValid :=
    fun i hi => Nat.lt_trans (hcY_bounds i hi)
      (by norm_num : 2 ^ 53 < 2 ^ 54)
  have hcZ_valid : cp.Z.IsValid :=
    fun i hi => Nat.lt_trans (hcZ_bounds i hi)
      (by norm_num : 2 ^ 52 < 2 ^ 54)
  have hcT_valid : cp.T.IsValid :=
    fun i hi => Nat.lt_trans (hcT_bounds i hi)
      (by norm_num : 2 ^ 52 < 2 ^ 54)
  have h_cp_Z_ne : cp.Z.toField ≠ 0 := by
    rw [hZ_F, h_YX_factor, h_yx_sq]
    apply mul_ne_zero hz2 h_denom_plus
  have h_cp_T_ne : cp.T.toField ≠ 0 := by
    rw [hT_F, hZ_F, h_denom_factor]
    apply mul_ne_zero hz2 h_denom_minus
  have h_cp_curve :
      Ed25519.a * cp.X.toField ^ 2 *
        cp.T.toField ^ 2 +
        cp.Y.toField ^ 2 * cp.Z.toField ^ 2 =
      cp.Z.toField ^ 2 * cp.T.toField ^ 2 +
        Ed25519.d * cp.X.toField ^ 2 *
        cp.Y.toField ^ 2 := by
    simp only [hX_F, hY_F, hZ_F, hT_F]
    simp only [Ed25519] at h_curve ⊢
    linear_combination
      (4 * (Y ^ 2 + X ^ 2) ^ 2) * h_curve
  have h_cp_valid : cp.IsValid := {
    X_valid := hcX_valid
    Y_valid := hcY_valid
    Z_valid := hcZ_valid
    T_valid := hcT_valid
    Z_ne_zero := h_cp_Z_ne
    T_ne_zero := h_cp_T_ne
    on_curve := h_cp_curve
  }
  -- Step 3: as_extended (preserves the point)
  apply WP.spec_mono
    (CompletedPoint.as_extended_spec cp h_cp_valid)
  intro result
    ⟨_, _, _, _, _, _, _, _,
     h_result_valid, h_result_toPoint⟩
  constructor
  · exact h_result_valid
  · -- result.toPoint = cp.toPoint = e.toPoint + e.toPoint
    rw [h_result_toPoint]
    -- Show cp.toPoint = e.toPoint + e.toPoint
    have ⟨h_cx, h_cy⟩ :=
      CompletedPoint.toPoint_of_isValid h_cp_valid
    have ⟨h_ex, h_ey⟩ :=
      edwards.EdwardsPoint.toPoint_of_isValid
        he_valid
    ext
    · -- x coordinate: 2XY/(Y²-X²) = addition formula
      rw [h_cx, hX_F, hZ_F, add_x]
      calc 2 * X * Y / (Y ^ 2 - X ^ 2)
        _ = 2 * X * Y /
            (Z ^ 2 * (y ^ 2 - x ^ 2)) := by
            rw [h_YX_factor]
        _ = 2 * X * Y / (Z ^ 2 *
            (1 + Ed25519.d * x ^ 2 * y ^ 2)) := by
            rw [h_yx_sq]
        _ = 2 * (Z * x) * (Z * y) / (Z ^ 2 *
            (1 + Ed25519.d * x ^ 2 * y ^ 2)) := by
            simp only [hx_def, hy_def]
            field_simp [hZ_ne]
        _ = Z ^ 2 * (2 * x * y) / (Z ^ 2 *
            (1 + Ed25519.d * x ^ 2 * y ^ 2)) := by
            ring
        _ = (2 * x * y) /
            (1 + Ed25519.d * x ^ 2 * y ^ 2) := by
            rw [mul_div_mul_left _ _ hz2]
        _ = ((e.toPoint).x * (e.toPoint).y +
             (e.toPoint).y * (e.toPoint).x) /
            (1 + Ed25519.d *
              (e.toPoint).x * (e.toPoint).x *
              (e.toPoint).y *
              (e.toPoint).y) := by
            rw [h_ex, h_ey]; ring
    · -- y coordinate: (Y²+X²)/(2Z²-(Y²-X²))
      rw [h_cy, hY_F, hT_F, hZ_F, add_y]
      have h_num_factor :
          Y ^ 2 + X ^ 2 =
            Z ^ 2 * (y ^ 2 + x ^ 2) := by
        have hxe : X = Z * x := by
          simp only [hx_def]
          field_simp [hZ_ne]
        have hye : Y = Z * y := by
          simp only [hy_def]
          field_simp [hZ_ne]
        rw [hxe, hye]; ring
      calc (Y ^ 2 + X ^ 2) /
           (2 * Z ^ 2 - (Y ^ 2 - X ^ 2))
        _ = (Y ^ 2 + X ^ 2) / (Z ^ 2 *
            (1 - Ed25519.d * x ^ 2 * y ^ 2)) := by
            rw [h_denom_factor]
        _ = Z ^ 2 * (y ^ 2 + x ^ 2) / (Z ^ 2 *
            (1 - Ed25519.d * x ^ 2 * y ^ 2)) := by
            rw [h_num_factor]
        _ = (y ^ 2 + x ^ 2) /
            (1 - Ed25519.d * x ^ 2 * y ^ 2) := by
            rw [mul_div_mul_left _ _ hz2]
        _ = ((e.toPoint).y * (e.toPoint).y -
             Ed25519.a * (e.toPoint).x *
              (e.toPoint).x) /
            (1 - Ed25519.d *
              (e.toPoint).x * (e.toPoint).x *
              (e.toPoint).y *
              (e.toPoint).y) := by
            rw [h_ex, h_ey]
            simp only [Ed25519]; ring
