/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Mathlib.Data.ZMod.Basic

-- Required for the #setup_aeneas_simps macro below
set_option linter.hashCommand false
#setup_aeneas_simps

/-!
# Spec theorem for `ProjectivePoint::double`

Specification and proof for `ProjectivePoint::double`.

This function implements point doubling on the Curve25519 elliptic curve using projective
coordinates. Given a point P = (X:Y:Z), it computes 2P (the point added to itself via
elliptic curve addition).

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51

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

/-- **Spec theorem for
`curve25519_dalek.backend.serial.curve_models.ProjectivePoint.double`**

Given input ProjectivePoint with coordinates (X, Y, Z), the output CompletedPoint (X', Y', Z', T')
satisfies the point doubling formulas modulo p:
- X' ≡ 2XY (mod p)
- Y' ≡ Y² + X² (mod p)
- Z' ≡ Y² - X² (mod p)
- T' ≡ 2Z² - Y² + X² (mod p)
where p = 2^255 - 19

Input bounds: X, Y limbs < 2^53 (for X + Y < 2^54), Z limbs < 2^54.
Output bounds: X', Z', T' limbs < 2^52, Y' limbs < 2^53.

TODO: Investigate if c.Y can achieve the tighter < 2^52 bound. Currently c.Y = YY + XX
where YY, XX < 2^52, giving Y < 2^53. -/
@[step]
theorem double_spec_aux
    (q : ProjectivePoint)
    (h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 53)
    (h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 53)
    (h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val < 2 ^ 54) :
    double q ⦃ (c : CompletedPoint) =>
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
  unfold double
  simp only [step_simps]
  let* ⟨ XX, XX_post1, XX_post2 ⟩ ← square_spec
  let* ⟨ YY, YY_post1, YY_post2 ⟩ ← square_spec
  let* ⟨ ZZ2, ZZ2_post1, ZZ2_post2 ⟩ ← square2_spec
  let* ⟨ X_plus_Y, X_plus_Y_post1, X_plus_Y_post2 ⟩ ← add_spec
  let* ⟨ X_plus_Y_sq, X_plus_Y_sq_post1, X_plus_Y_sq_post2 ⟩ ← square_spec
  let* ⟨ YY_plus_XX, YY_plus_XX_post1, YY_plus_XX_post2 ⟩ ← add_spec
  let* ⟨ YY_minus_XX, YY_minus_XX_post1, YY_minus_XX_post2 ⟩ ← sub_spec
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← sub_spec
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← sub_spec
  unfold Field51_as_Nat at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- X' % p = (2 * X * Y) % p
    have : (∑ i ∈ Finset.range 5, 2^(51 * i) * (X_plus_Y[i]!).val) =
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.X[i]!).val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.Y[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      simp_all [Finset.mem_range, Nat.mul_add]
    rw [this] at X_plus_Y_sq_post1;
    have h_YY_plus_XX : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY_plus_XX[i]!).val) =
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      simp_all [Finset.mem_range, Nat.mul_add]
    rw [h_YY_plus_XX] at fe_post2;
    have hB_equiv : (∑ i ∈ Finset.range 5, 2^(51 * i) * YY[i]!.val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * XX[i]!.val) ≡
        (∑ i ∈ Finset.range 5, 2^(51 * i) * q.Y[i]!.val) ^ 2 +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * q.X[i]!.val) ^ 2 [MOD p] := by
      apply Nat.ModEq.add
      · grind only
      · grind only
    apply Nat.ModEq.add_left_cancel hB_equiv; rw [add_comm]
    ring_nf at *
    rw [← Nat.ModEq] at fe_post2
    apply Nat.ModEq.trans fe_post2
    exact X_plus_Y_sq_post1
  · -- Y' % p = (Y^2 + X^2) % p
    rw [← Nat.ModEq] at *
    have h_YY_plus_XX : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY_plus_XX[i]!).val) =
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      simp_all [Finset.mem_range, Nat.mul_add]
    rw [h_YY_plus_XX]
    apply Nat.ModEq.add
    · grind only
    · grind only
  · -- (Z' + X^2) % p = Y^2 % p
    rw [← Nat.ModEq] at *; ring_nf at *;
    apply Nat.ModEq.trans (Nat.ModEq.add_left _ XX_post1.symm)
    apply Nat.ModEq.trans YY_minus_XX_post2
    exact YY_post1
  · -- (T' + Z') % p = (2 * Z^2) % p
    rw [← Nat.ModEq] at *;
    apply Nat.ModEq.trans fe1_post2
    exact ZZ2_post1
  · -- c.X bounds < 2^52
    intro i hi
    exact fe_post1 i hi
  · -- c.Y bounds < 2^53
    -- c.Y = YY_plus_XX = YY + XX where YY < 2^52 and XX < 2^52
    -- So YY_plus_XX < 2^52 + 2^52 = 2^53
    intro i hi
    have h_eq := YY_plus_XX_post1 i hi
    have h_YY := YY_post2 i hi
    have h_XX := XX_post2 i hi
    omega
  · -- c.Z bounds < 2^52
    intro i hi
    exact YY_minus_XX_post1 i hi
  · -- c.T bounds < 2^52
    intro i hi
    exact fe1_post1 i hi

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint

namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

open Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field

lemma double_lift_to_field_eqs (c : CompletedPoint) (q : ProjectivePoint)
    (hX_arith : Field51_as_Nat c.X % p = (2 * Field51_as_Nat q.X * Field51_as_Nat q.Y) % p)
    (hY_arith : Field51_as_Nat c.Y % p = (Field51_as_Nat q.Y ^ 2 + Field51_as_Nat q.X ^ 2) % p)
    (hZ_arith : (Field51_as_Nat c.Z + Field51_as_Nat q.X ^ 2) % p = Field51_as_Nat q.Y ^ 2 % p)
    (hT_arith : (Field51_as_Nat c.T + Field51_as_Nat c.Z) % p = (2 * Field51_as_Nat q.Z ^ 2) % p) :
    c.X.toField = 2 * q.X.toField * q.Y.toField ∧
    c.Y.toField = q.Y.toField ^ 2 + q.X.toField ^ 2 ∧
    c.Z.toField = q.Y.toField ^ 2 - q.X.toField ^ 2 ∧
    c.T.toField = 2 * q.Z.toField ^ 2 - c.Z.toField := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hX_arith; push_cast at h; exact h
  · unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hY_arith; push_cast at h; exact h
  · unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hZ_arith; push_cast at h; exact eq_sub_of_add_eq h
  · unfold FieldElement51.toField at *
    have h := lift_mod_eq _ _ hT_arith; push_cast at h; exact eq_sub_of_add_eq h

attribute [local irreducible] p in
/-- Core geometric proof for point doubling. Takes only `OnCurve` and
the exact bounds needed by `double_spec_aux` (X,Y < 2^53, Z < 2^54).
Both `ProjectivePoint.double_spec` and `EdwardsPoint.double_spec`
delegate to this. -/
theorem double_spec_core
    (q : ProjectivePoint)
    (hq_on : q.OnCurve)
    (h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 53)
    (h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 53)
    (h_qZ_valid : q.Z.IsValid) :
    ∃ c, ProjectivePoint.double q = ok c ∧
    c.IsValid ∧ c.toPoint = q.toPoint' hq_on + q.toPoint' hq_on := by
  obtain ⟨c, h_run, hX_arith, hY_arith, hZ_arith, hT_arith,
          hcX_bounds, hcY_bounds, hcZ_bounds, hcT_bounds⟩ :=
    spec_imp_exists (ProjectivePoint.double_spec_aux q
      h_qX_bounds h_qY_bounds h_qZ_valid)
  use c
  constructor
  · exact h_run
  obtain ⟨hX_F, hY_F, hZ_F, hT_F⟩ :=
    double_lift_to_field_eqs c q hX_arith hY_arith hZ_arith hT_arith
  -- Setup curve identity from OnCurve
  have h_q_curve := hq_on.on_curve
  have h_qZ_ne : q.Z.toField ≠ 0 := hq_on.Z_ne_zero
  -- Let P be the affine point represented by q
  set X := q.X.toField with hX_def
  set Y := q.Y.toField with hY_def
  set Z := q.Z.toField with hZ_def
  -- The curve equation in field terms: a * X² * Z² + Y² * Z² = Z⁴ + d * X² * Y²
  have h_curve_field : Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2 := h_q_curve
  -- Affine coordinates: x = X/Z, y = Y/Z
  set x := X / Z with hx_def
  set y := Y / Z with hy_def
  -- Prove denominators are non-zero using completeness theorem
  -- First construct the affine point P on Ed25519
  have h_P_on_curve : Ed25519.a * x ^ 2 + y ^ 2 = 1 + Ed25519.d * x ^ 2 * y ^ 2 :=
    curve25519_dalek.edwards.affine_on_curve_of_projective X Y Z h_qZ_ne h_curve_field
  let P : Point Ed25519 := ⟨x, y, h_P_on_curve⟩
  have h_denoms := Ed25519.denomsNeZero P P
  -- denomsNeZero gives: 1 + d * P.x * P.x * P.y * P.y ≠ 0, i.e., 1 + d * x * x * y * y ≠ 0
  have h_denom_plus : 1 + Ed25519.d * x^2 * y^2 ≠ 0 := by
    have h := h_denoms.1
    simp only [P] at h
    convert h using 2
    ring
  have h_denom_minus : 1 - Ed25519.d * x^2 * y^2 ≠ 0 := by
    have h := h_denoms.2
    simp only [P] at h
    convert h using 2
    ring
  -- Common helper lemmas (to avoid repetition)
  have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 h_qZ_ne
  have hz4 : Z^4 ≠ 0 := pow_ne_zero 4 h_qZ_ne
  -- Key identity: y² - x² = 1 + d*x²*y² (from curve equation with a = -1)
  have h_yx_sq : y^2 - x^2 = 1 + Ed25519.d * x^2 * y^2 := by
    have hp : Ed25519.a * x^2 + y^2 = 1 + Ed25519.d * x^2 * y^2 := by
      simp only [Ed25519] at h_curve_field ⊢
      simp only [hx_def, hy_def, div_pow]
      field_simp [hz2, hz4]
      linear_combination h_curve_field
    calc y^2 - x^2 = -1 * x^2 + y^2 := by ring
      _ = Ed25519.a * x^2 + y^2 := by simp only [Ed25519]
      _ = 1 + Ed25519.d * x^2 * y^2 := hp
  -- Y² - X² = Z² * (y² - x²)
  have h_YX_factor : Y^2 - X^2 = Z^2 * (y^2 - x^2) := by
    simp only [hx_def, hy_def, div_pow]
    field_simp [h_qZ_ne]
  -- 2Z² - (Y² - X²) = Z² * (1 - d*x²*y²)
  have h_denom_factor : 2 * Z^2 - (Y^2 - X^2) = Z^2 * (1 - Ed25519.d * x^2 * y^2) := by
    rw [h_YX_factor, h_yx_sq]
    ring
  -- Convert specific bounds to IsValid (< 2^54)
  have hcX_valid :
    c.X.IsValid := fun i hi => Nat.lt_trans (hcX_bounds i hi) (by norm_num : 2^52 < 2^54)
  have hcY_valid :
    c.Y.IsValid := fun i hi => Nat.lt_trans (hcY_bounds i hi) (by norm_num : 2^53 < 2^54)
  have hcZ_valid :
    c.Z.IsValid := fun i hi => Nat.lt_trans (hcZ_bounds i hi) (by norm_num : 2^52 < 2^54)
  have hcT_valid :
    c.T.IsValid := fun i hi => Nat.lt_trans (hcT_bounds i hi) (by norm_num : 2^52 < 2^54)
  have h_c_valid : c.IsValid := {
    X_valid := hcX_valid
    Y_valid := hcY_valid
    Z_valid := hcZ_valid
    T_valid := hcT_valid
    Z_ne_zero := by rw [hZ_F, h_YX_factor, h_yx_sq]; apply mul_ne_zero hz2 h_denom_plus
    T_ne_zero := by rw [hT_F, hZ_F, h_denom_factor]; apply mul_ne_zero hz2 h_denom_minus
    on_curve := by
      simp only [hX_F, hY_F, hZ_F, hT_F]
      simp only [Ed25519] at h_curve_field ⊢
      linear_combination (4 * (Y ^ 2 + X ^ 2) ^ 2) * h_curve_field
  }
  constructor
  · exact h_c_valid
  · -- Prove c.toPoint = q.toPoint' hq_on + q.toPoint' hq_on
    have ⟨h_cx, h_cy⟩ := CompletedPoint.toPoint_of_isValid h_c_valid
    have h_qx : (q.toPoint' hq_on).x = x := rfl
    have h_qy : (q.toPoint' hq_on).y = y := rfl
    ext
    · rw [h_cx, hX_F, hZ_F, add_x]
      have hcZ_ne : Y ^ 2 - X ^ 2 ≠ 0 := by
        rw [h_YX_factor, h_yx_sq]
        apply mul_ne_zero hz2 h_denom_plus
      calc 2 * X * Y / (Y ^ 2 - X ^ 2)
        _ = 2 * X * Y / (Z ^ 2 * (y ^ 2 - x ^ 2)) := by
            rw [h_YX_factor]
        _ = 2 * X * Y / (Z ^ 2 * (1 + Ed25519.d * x ^ 2 * y ^ 2)) := by
            rw [h_yx_sq]
        _ = 2 * (Z * x) * (Z * y) /
            (Z ^ 2 * (1 + Ed25519.d * x ^ 2 * y ^ 2)) := by
            simp only [hx_def, hy_def]; field_simp [h_qZ_ne]
        _ = Z ^ 2 * (2 * x * y) /
            (Z ^ 2 * (1 + Ed25519.d * x ^ 2 * y ^ 2)) := by
            ring
        _ = (2 * x * y) /
            (1 + Ed25519.d * x ^ 2 * y ^ 2) := by
            rw [mul_div_mul_left _ _ hz2]
        _ = ((q.toPoint' hq_on).x * (q.toPoint' hq_on).y +
            (q.toPoint' hq_on).y * (q.toPoint' hq_on).x) /
            (1 + Ed25519.d * (q.toPoint' hq_on).x *
            (q.toPoint' hq_on).x * (q.toPoint' hq_on).y *
            (q.toPoint' hq_on).y) := by
            rw [h_qx, h_qy]; ring
    · rw [h_cy, hY_F, hT_F, hZ_F, add_y]
      have h_num_factor : Y ^ 2 + X ^ 2 = Z ^ 2 * (y ^ 2 + x ^ 2) := by
        have hx : X = Z * x := by
          simp only [hx_def]; field_simp [h_qZ_ne]
        have hy : Y = Z * y := by
          simp only [hy_def]; field_simp [h_qZ_ne]
        rw [hx, hy]; ring
      calc (Y ^ 2 + X ^ 2) / (2 * Z ^ 2 - (Y ^ 2 - X ^ 2))
        _ = (Y ^ 2 + X ^ 2) /
            (Z ^ 2 * (1 - Ed25519.d * x ^ 2 * y ^ 2)) := by
            rw [h_denom_factor]
        _ = Z ^ 2 * (y ^ 2 + x ^ 2) /
            (Z ^ 2 * (1 - Ed25519.d * x ^ 2 * y ^ 2)) := by
            rw [h_num_factor]
        _ = (y ^ 2 + x ^ 2) /
            (1 - Ed25519.d * x ^ 2 * y ^ 2) := by
            rw [mul_div_mul_left _ _ hz2]
        _ = ((q.toPoint' hq_on).y * (q.toPoint' hq_on).y -
            Ed25519.a * (q.toPoint' hq_on).x *
            (q.toPoint' hq_on).x) /
            (1 - Ed25519.d * (q.toPoint' hq_on).x *
            (q.toPoint' hq_on).x * (q.toPoint' hq_on).y *
            (q.toPoint' hq_on).y) := by
            rw [h_qx, h_qy]; simp only [Ed25519]; ring

/-- Verification of the `double` function for `ProjectivePoint` in WP form.
Thin wrapper over `double_spec_core`: widens bounds from `< 2^52`
to `< 2^53` and bridges `toPoint' → toPoint`. -/
@[step]
theorem double_spec
    (q : ProjectivePoint) (hq_valid : q.IsValid) :
    ProjectivePoint.double q ⦃ (c : CompletedPoint) =>
      c.IsValid ∧ c.toPoint = q.toPoint + q.toPoint ⦄ := by
  obtain ⟨c, h_run, h_c_valid, h_eq⟩ := double_spec_core q
    hq_valid.toOnCurve
    (fun i hi => Nat.lt_trans (hq_valid.X_bounds i hi)
      (by norm_num : 2 ^ 52 < 2 ^ 53))
    (fun i hi => Nat.lt_trans (hq_valid.Y_bounds i hi)
      (by norm_num : 2 ^ 52 < 2 ^ 53))
    (FieldElement51.IsValid_of_lt_pow hq_valid.Z_bounds
      (by decide))
  have h_eq' : c.toPoint = q.toPoint + q.toPoint := by
    simp only [toPoint, dif_pos hq_valid, toPoint'] at h_eq ⊢
    exact h_eq
  simp only [h_run, spec_ok, h_c_valid, h_eq', and_self]

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
