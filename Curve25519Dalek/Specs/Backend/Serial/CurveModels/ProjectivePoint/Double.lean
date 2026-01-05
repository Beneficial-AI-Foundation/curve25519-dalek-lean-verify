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

open Aeneas.Std Result

open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Add
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Sub

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
    ∃ c, double q = ok c ∧
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
    -- Output bounds: X, Z, T < 2^52 (from sub); Y < 2^53 (sum of two < 2^52 values)
    -- TODO: Investigate if c.Y can achieve the tighter < 2^52 bound. Currently c.Y = YY + XX
    -- where YY, XX < 2^52, giving Y < 2^53. Options to achieve < 2^52:
    -- (1) The Rust code could reduce YY_plus_XX before storing in c.Y
    -- (2) There may be algebraic properties that constrain Y more tightly
    -- (3) The downstream consumer (to_projective) may not require the tight bound
    (∀ i < 5, c.X[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 53) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 52) := by
  unfold double
  progress*
  · -- BEGIN TASK
    intro i hi
    have := h_qX_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := h_qY_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK: X_plus_Y bounds for squaring (X < 2^53, Y < 2^53 → X+Y < 2^54)
    intro i hi
    have := h_qX_bounds i hi
    have := h_qY_bounds i hi
    have : ∀ i < 5, YY[i]!.val < 2 ^ 52 := by grind
    have := this i (by grind)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK: YY_plus_XX = add YY XX bounds (YY, XX < 2^52 → output < 2^54 for sub)
    intro i hi
    have := YY_post_2 i hi
    have := XX_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := YY_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := XX_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have : ∀ i < 5, X_plus_Y_sq[i]!.val < 2 ^ 52 := by grind
    have := this i (by grind)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := XX_post_2 i hi
    have : ∀ i < 5, ZZ2[i]!.val < 2 ^ 53 := by grind
    have := this i (by grind)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK: X_plus_Y_sq input to sub (< 2^63 first arg bound)
    intro i hi
    have := X_plus_Y_sq_post_2 i hi
    have : ∀ i < 5, YY_minus_XX[i]!.val < 2 ^ 52 := by grind
    have := this i (by grind)
    scalar_tac
    -- END TASK
  unfold Field51_as_Nat at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- BEGIN TASK: X' % p = (2 * X * Y) % p
    have : (∑ i ∈ Finset.range 5, 2^(51 * i) * (X_plus_Y[i]!).val) =
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.X[i]!).val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.Y[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      simp_all [Finset.mem_range, Nat.mul_add]
    rw [this] at X_plus_Y_sq_post_1;
    have h_YY_plus_XX : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY_plus_XX[i]!).val) =
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      simp_all [Finset.mem_range, Nat.mul_add]
    rw [h_YY_plus_XX] at fe_post_2;
    have hB_equiv : (∑ i ∈ Finset.range 5, 2^(51 * i) * YY[i]!.val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * XX[i]!.val) ≡
        (∑ i ∈ Finset.range 5, 2^(51 * i) * q.Y[i]!.val) ^ 2 +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * q.X[i]!.val) ^ 2 [MOD p] := by
      apply Nat.ModEq.add
      · grind
      · grind
    apply Nat.ModEq.add_left_cancel hB_equiv; rw [add_comm]
    ring_nf at *
    rw [← Nat.ModEq] at fe_post_2
    apply Nat.ModEq.trans fe_post_2
    exact X_plus_Y_sq_post_1
    -- END TASK
  · -- BEGIN TASK: Y' % p = (Y^2 + X^2) % p
    rw [← Nat.ModEq] at *
    have h_YY_plus_XX : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY_plus_XX[i]!).val) =
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
        (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro i hi
      simp_all [Finset.mem_range, Nat.mul_add]
    rw [h_YY_plus_XX]
    apply Nat.ModEq.add
    · grind
    · grind
    -- END TASK
  · -- BEGIN TASK: (Z' + X^2) % p = Y^2 % p
    rw [← Nat.ModEq] at *; ring_nf at *;
    apply Nat.ModEq.trans (Nat.ModEq.add_left _ XX_post_1.symm)
    apply Nat.ModEq.trans YY_minus_XX_post_2
    exact YY_post_1
    -- END TASK
  · -- BEGIN TASK: (T' + Z') % p = (2 * Z^2) % p
    rw [← Nat.ModEq] at *;
    apply Nat.ModEq.trans fe1_post_2
    exact ZZ2_post_1
    -- END TASK
  · -- BEGIN TASK: c.X bounds < 2^52
    intro i hi
    exact fe_post_1 i hi
    -- END TASK
  · -- BEGIN TASK: c.Y bounds < 2^53
    -- c.Y = YY_plus_XX = YY + XX where YY < 2^52 and XX < 2^52
    -- So YY_plus_XX < 2^52 + 2^52 = 2^53
    intro i hi
    have h_eq := YY_plus_XX_post_1 i hi
    have h_YY := YY_post_2 i hi
    have h_XX := XX_post_2 i hi
    omega
    -- END TASK
  · -- BEGIN TASK: c.Z bounds < 2^52
    intro i hi
    exact YY_minus_XX_post_1 i hi
    -- END TASK
  · -- BEGIN TASK: c.T bounds < 2^52
    intro i hi
    exact fe1_post_1 i hi
    -- END TASK

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/-! ## Mathematical Verification

This section proves that the geometric implementation `double_spec_aux` corresponds to the
mathematical operation of point doubling on the Edwards curve.

The proof bridges low-level Rust implementation to high-level mathematics using the
infrastructure from `Curve25519Dalek.Defs.Edwards`.
-/

namespace Edwards

open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field

set_option maxHeartbeats 400000 in
/--
Verification of the `double` function.
The theorem states that the Rust implementation of point doubling corresponds
exactly to the mathematical addition of the point to itself (`q + q`) on the Edwards curve.
-/
theorem double_spec
    (q : ProjectivePoint) (hq_valid : q.IsValid) :
    ∃ c, ProjectivePoint.double q = ok c ∧
    c.IsValid ∧ c.toPoint = q.toPoint + q.toPoint := by
  -- Extract bounds from validity (< 2^52) and lift to double_spec_aux requirements
  have h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 53 :=
    fun i hi => Nat.lt_trans (hq_valid.X_bounds i hi) (by norm_num : 2^52 < 2^53)
  have h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 53 :=
    fun i hi => Nat.lt_trans (hq_valid.Y_bounds i hi) (by norm_num : 2^52 < 2^53)
  have h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val < 2 ^ 54 :=
    fun i hi => Nat.lt_trans (hq_valid.Z_bounds i hi) (by norm_num : 2^52 < 2^54)

  -- Use double_spec_aux to get the arithmetic properties and bounds
  obtain ⟨c, h_run, hX_arith, hY_arith, hZ_arith, hT_arith,
          hcX_bounds, hcY_bounds, hcZ_bounds, hcT_bounds⟩ :=
    ProjectivePoint.double_spec_aux q h_qX_bounds h_qY_bounds h_qZ_bounds

  use c
  constructor
  · exact h_run

  -- Now we have:
  -- - c : CompletedPoint (the result)
  -- - hX_arith : Field51_as_Nat c.X % p = (2 * Field51_as_Nat q.X * Field51_as_Nat q.Y) % p
  -- - hY_arith : Field51_as_Nat c.Y % p = (Y^2 + X^2) % p
  -- - hZ_arith : (Field51_as_Nat c.Z + X^2) % p = Y^2 % p
  -- - hT_arith : (Field51_as_Nat c.T + c.Z) % p = (2 * Z^2) % p
  -- - hcX_bounds, hcY_bounds, hcZ_bounds, hcT_bounds : output limb bounds

  -- Lift to field equalities
  -- Note: toField is (Field51_as_Nat · : CurveField)
  have hX_F : c.X.toField = 2 * q.X.toField * q.Y.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hX_arith
    push_cast at h
    exact h

  have hY_F : c.Y.toField = q.Y.toField^2 + q.X.toField^2 := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hY_arith
    push_cast at h
    exact h

  have hZ_F : c.Z.toField = q.Y.toField^2 - q.X.toField^2 := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hZ_arith
    push_cast at h
    exact eq_sub_of_add_eq h

  have hT_F : c.T.toField = 2 * q.Z.toField^2 - c.Z.toField := by
    unfold FieldElement51.toField at *
    have h := lift_mod_eq _ _ hT_arith
    push_cast at h
    exact eq_sub_of_add_eq h

  -- Setup curve identity from input validity
  have h_q_curve := hq_valid.on_curve
  have h_qZ_ne : q.Z.toField ≠ 0 := hq_valid.Z_ne_zero

  -- Let P be the affine point represented by q
  set X := q.X.toField with hX_def
  set Y := q.Y.toField with hY_def
  set Z := q.Z.toField with hZ_def

  -- The curve equation in field terms: a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y²
  have h_curve_field : Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2 := h_q_curve

  -- Affine coordinates: x = X/Z, y = Y/Z
  set x := X / Z with hx_def
  set y := Y / Z with hy_def

  -- Prove denominators are non-zero using completeness theorem
  -- First construct the affine point P on Ed25519
  have h_P_on_curve : Ed25519.a * x^2 + y^2 = 1 + Ed25519.d * x^2 * y^2 := by
    have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 h_qZ_ne
    have hz4 : Z^4 ≠ 0 := pow_ne_zero 4 h_qZ_ne
    simp only [Ed25519] at h_curve_field ⊢
    simp only [hx_def, hy_def, div_pow]
    field_simp [hz2, hz4]
    linear_combination h_curve_field

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
  have hcX_valid : c.X.IsValid := fun i hi => Nat.lt_trans (hcX_bounds i hi) (by norm_num : 2^52 < 2^54)
  have hcY_valid : c.Y.IsValid := fun i hi => Nat.lt_trans (hcY_bounds i hi) (by norm_num : 2^53 < 2^54)
  have hcZ_valid : c.Z.IsValid := fun i hi => Nat.lt_trans (hcZ_bounds i hi) (by norm_num : 2^52 < 2^54)
  have hcT_valid : c.T.IsValid := fun i hi => Nat.lt_trans (hcT_bounds i hi) (by norm_num : 2^52 < 2^54)

  constructor
  · -- Prove c.IsValid (bounds, Z_ne_zero, T_ne_zero, on_curve)
    exact {
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

  · -- Prove c.toPoint = q.toPoint + q.toPoint
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

    -- Unfold toPoint for c and q
    have ⟨h_cx, h_cy⟩ := CompletedPoint.toPoint_of_isValid h_c_valid
    have ⟨h_qx, h_qy⟩ := ProjectivePoint.toPoint_of_isValid hq_valid

    -- Show equality via the addition formula
    ext
    · -- x coordinate: c.toPoint.x = (q.toPoint + q.toPoint).x
      -- c.toPoint.x = 2XY / (Y² - X²)
      -- (q + q).x = 2xy / (1 + d*x²y²) where x = X/Z, y = Y/Z
      rw [h_cx, hX_F, hZ_F]  -- LHS: c.X.toField / c.Z.toField = 2*X*Y / (Y² - X²)
      rw [add_x]  -- RHS: expand addition formula

      -- Key facts for denominators
      have hcZ_ne : Y^2 - X^2 ≠ 0 := by
        rw [h_YX_factor, h_yx_sq]
        apply mul_ne_zero hz2 h_denom_plus

      have h_add_denom_ne : 1 + Ed25519.d * q.toPoint.x * q.toPoint.x * q.toPoint.y * q.toPoint.y ≠ 0 := by
        rw [h_qx, h_qy]
        convert h_denom_plus using 2
        simp only [hx_def, hy_def]; ring

      -- Calculate: 2XY / (Y² - X²)
      calc 2 * X * Y / (Y^2 - X^2)
        _ = 2 * X * Y / (Z^2 * (y^2 - x^2)) := by rw [h_YX_factor]
        _ = 2 * X * Y / (Z^2 * (1 + Ed25519.d * x^2 * y^2)) := by rw [h_yx_sq]
        _ = 2 * (Z * x) * (Z * y) / (Z^2 * (1 + Ed25519.d * x^2 * y^2)) := by
            simp only [hx_def, hy_def]; field_simp [h_qZ_ne]
        _ = Z^2 * (2 * x * y) / (Z^2 * (1 + Ed25519.d * x^2 * y^2)) := by ring
        _ = (2 * x * y) / (1 + Ed25519.d * x^2 * y^2) := by rw [mul_div_mul_left _ _ hz2]
        _ = (q.toPoint.x * q.toPoint.y + q.toPoint.y * q.toPoint.x) /
            (1 + Ed25519.d * q.toPoint.x * q.toPoint.x * q.toPoint.y * q.toPoint.y) := by
            rw [h_qx, h_qy]; ring

    · -- y coordinate: c.toPoint.y = (q.toPoint + q.toPoint).y
      -- c.toPoint.y = (Y² + X²) / (2Z² - (Y² - X²))
      -- (q + q).y = (y² - a*x²) / (1 - d*x²y²) = (y² + x²) / (1 - d*x²y²) since a = -1
      rw [h_cy, hY_F, hT_F, hZ_F]  -- LHS: c.Y.toField / c.T.toField
      rw [add_y]  -- RHS: expand addition formula

      -- Helper: Y² + X² = Z² * (y² + x²)
      have h_num_factor : Y^2 + X^2 = Z^2 * (y^2 + x^2) := by
        have hx : X = Z * x := by simp only [hx_def]; field_simp [h_qZ_ne]
        have hy : Y = Z * y := by simp only [hy_def]; field_simp [h_qZ_ne]
        rw [hx, hy]; ring

      -- Calculate: (Y² + X²) / (2Z² - (Y² - X²))
      calc (Y^2 + X^2) / (2 * Z^2 - (Y^2 - X^2))
        _ = (Y^2 + X^2) / (Z^2 * (1 - Ed25519.d * x^2 * y^2)) := by rw [h_denom_factor]
        _ = Z^2 * (y^2 + x^2) / (Z^2 * (1 - Ed25519.d * x^2 * y^2)) := by rw [h_num_factor]
        _ = (y^2 + x^2) / (1 - Ed25519.d * x^2 * y^2) := by rw [mul_div_mul_left _ _ hz2]
        _ = (q.toPoint.y * q.toPoint.y - Ed25519.a * q.toPoint.x * q.toPoint.x) /
            (1 - Ed25519.d * q.toPoint.x * q.toPoint.x * q.toPoint.y * q.toPoint.y) := by
            rw [h_qx, h_qy]; simp only [Ed25519]; ring

  -- -- 1. Unwrap validity witness P from the input
  -- rcases hq_valid with ⟨P, hP⟩

  -- -- Bridge: Convert the coerced q back to P using our previous lemmas
  -- have h_q_eq_P : (q : Point Ed25519) = P := ProjectivePoint.toPoint'_eq_of_isValid hP
  -- rw [h_q_eq_P]

  -- -- 2. Run the Aeneas specification
  -- have ⟨out, h_run, h_arith⟩ := ProjectivePoint.double_spec_aux q
  --   (fun i h => hq_bounds.1 i h)
  --   (fun i h => hq_bounds.2.1 i h)
  --   (fun i h => hq_bounds.2.2 i h)

  -- exists out
  -- constructor; · exact h_run

  -- -- 3. Mathematical Arithmetic Proof
  -- -- This block proves that the output limbs correspond to P + P coordinates.
  -- let P2 := P + P

  -- have h_out_represents_P2 : out.IsValid' P2 := by
  --   dsimp only at hP
  --   rcases hP with ⟨hZ_nonzero, hX_in, hY_in⟩
  --   rcases h_arith with ⟨hX_new, hY_new, hZ_new, hT_new⟩

  --   -- Lift low-level limbs to field elements
  --   let X_nat := Field51_as_Nat q.X
  --   let Y_nat := Field51_as_Nat q.Y
  --   let Z_nat := Field51_as_Nat q.Z

  --   have hX_F : field_from_limbs out.X = 2 * field_from_limbs q.X * field_from_limbs q.Y := by
  --     dsimp [field_from_limbs]; rw [Edwards.lift_mod_eq _ _ hX_new]; push_cast; rfl

  --   have hY_F : field_from_limbs out.Y = field_from_limbs q.Y ^ 2 + field_from_limbs q.X ^ 2 := by
  --     dsimp [field_from_limbs]; rw [Edwards.lift_mod_eq _ _ hY_new]; push_cast; rfl

  --   have hZ_F : field_from_limbs out.Z = field_from_limbs q.Y ^ 2 - field_from_limbs q.X ^ 2 := by
  --     have h := Edwards.lift_mod_eq _ _ hZ_new; push_cast at h; apply eq_sub_of_add_eq h

  --   have hT_F : field_from_limbs out.T = 2 * field_from_limbs q.Z ^ 2 - field_from_limbs out.Z := by
  --     have h := Edwards.lift_mod_eq _ _ hT_new; push_cast at h; apply eq_sub_of_add_eq h

  --   -- Setup Curve Identities
  --   unfold CompletedPoint.IsValid'
  --   have h_d_not_square : ¬IsSquare Ed25519.d := d_not_square
  --   have h_neg_one_square : IsSquare (-1 : CurveField) := by
  --     apply ZMod.exists_sq_eq_neg_one_iff.mpr; decide

  --   have h_curve : -P.x^2 + P.y^2 = 1 + Ed25519.d * P.x^2 * P.y^2 := by
  --     have h := P.on_curve; simp only [Ed25519, neg_mul, one_mul] at h; exact h

  --   -- Helper: Prove denominators are non-zero
  --   have h_denom_plus : 1 + Ed25519.d * P.x^2 * P.y^2 ≠ 0 := by
  --     intro h_zero
  --     rw [add_eq_zero_iff_eq_neg] at h_zero
  --     have ⟨k, hk⟩ := h_neg_one_square
  --     rw [←neg_eq_iff_eq_neg, hk] at h_zero
  --     by_cases h_xy_nz : P.x * P.y = 0
  --     · rw [mul_assoc, ← mul_pow, h_xy_nz] at h_zero
  --       simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h_zero
  --       rw [h_zero] at hk; norm_num at hk;

  --     · apply h_d_not_square
  --       use k / (P.x * P.y)
  --       field_simp [h_xy_nz]; ring_nf at h_zero; rw [h_zero]
  --       have h_nz : P.x^2 * P.y^2 ≠ 0 := by
  --         rw [←mul_pow]
  --         exact pow_ne_zero 2 h_xy_nz
  --       rw [mul_assoc, mul_div_cancel_right₀ _ h_nz]

  --   have h_denom_minus : 1 - Ed25519.d * P.x^2 * P.y^2 ≠ 0 := by
  --     intro h_zero
  --     rw [sub_eq_zero] at h_zero

  --     by_cases h_xy_nz : P.x * P.y = 0
  --     · rw [mul_assoc, ← mul_pow, h_xy_nz] at h_zero
  --       simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h_zero
  --       norm_num at h_zero
  --     · apply h_d_not_square
  --       use 1 / (P.x * P.y)
  --       rw [mul_assoc] at h_zero; field_simp [h_xy_nz]; rw [← mul_pow] at h_zero ⊢
  --       have h_nz_sq : (P.x * P.y) ^ 2 ≠ 0 := pow_ne_zero 2 h_xy_nz
  --       rw [eq_div_iff h_nz_sq]; ring_nf at h_zero ⊢; exact h_zero.symm

  --   -- Prove the 4 components of IsValid (Z≠0, T≠0, X correct, Y correct)
  --   refine ⟨?_, ?_, ?_, ?_⟩

  --   -- 1. Prove Z ≠ 0
  --   · rw [hZ_F, hX_in, hY_in]
  --     rw [mul_pow, mul_pow]
  --     have h_factor : P.y^2 * field_from_limbs q.Z ^ 2 - P.x^2 * field_from_limbs q.Z ^ 2 =
  --                     field_from_limbs q.Z ^ 2 * (P.y^2 - P.x^2) := by ring
  --     rw [h_factor]
  --     apply mul_ne_zero
  --     · exact pow_ne_zero 2 hZ_nonzero
  --     · have h_curve' : P.y^2 - P.x^2 = 1 + Ed25519.d * P.x^2 * P.y^2 := by
  --         calc
  --           P.y ^ 2 - P.x ^ 2
  --           _ = -P.x ^ 2 + P.y ^ 2 := by ring
  --           _ = 1 + Ed25519.d * P.x ^ 2 * P.y ^ 2 := h_curve
  --       rw [h_curve']
  --       exact h_denom_plus

  --   -- 2. Prove T ≠ 0
  --   · rw [hT_F, hZ_F, hX_in, hY_in]
  --     rw [mul_pow, mul_pow]
  --     have h_factor : 2 * field_from_limbs q.Z ^ 2 -
  --       (P.y^2 * field_from_limbs q.Z ^ 2 - P.x^2 * field_from_limbs q.Z ^ 2) =
  --                     field_from_limbs q.Z ^ 2 * (2 - (P.y^2 - P.x^2)) := by ring
  --     rw [h_factor]
  --     apply mul_ne_zero
  --     · exact pow_ne_zero 2 hZ_nonzero
  --     · have h_curve' : 2 - (P.y^2 - P.x^2) = 1 - Ed25519.d * P.x^2 * P.y^2 := by
  --         calc
  --           2 - (P.y ^ 2 - P.x ^ 2)
  --           _ = 2 - (-P.x ^ 2 + P.y ^ 2) := by ring
  --           _= 2 - (1 + Ed25519.d * P.x ^ 2 * P.y ^ 2) := by rw [← h_curve]
  --           _ = 1 - Ed25519.d * P.x ^ 2 * P.y ^ 2 := by ring
  --       rw [h_curve']
  --       exact h_denom_minus

  --   -- 3. Verify X coordinate
  --   · rw [(add_def P P).1]; dsimp only [add_coords]
  --     rw [hX_F, hZ_F, hX_in, hY_in]

  --     have h_denom : 1 + Ed25519.d * P.x * P.x * P.y * P.y ≠ 0 := by convert h_denom_plus using 1; ring
  --     have h_subst : 1 + Ed25519.d * P.x^2 * P.y^2 = P.y^2 - P.x^2 := by rw [←h_curve]; ring
  --     have h_comm : 1 + P.x^2 * P.y^2 * Ed25519.d = 1 + Ed25519.d * P.x^2 * P.y^2 := by ring
  --     field_simp [h_denom, ← h_curve]; rw [h_comm]; ring_nf at h_denom; rw [eq_div_iff h_denom, h_subst]
  --     ring_nf

  --   -- 4. Verify Y coordinate
  --   · rw [(add_def P P).2]; dsimp only [add_coords]

  --     rw [hY_F, hT_F, hZ_F, hX_in, hY_in]

  --     have h_a : Ed25519.a = -1 := rfl; rw [h_a]

  --     have h_denom : 1 - Ed25519.d * P.x * P.x * P.y * P.y ≠ 0 := by convert h_denom_minus using 1; ring
  --     have h_subst : 1 - Ed25519.d * P.x^2 * P.y^2 = 2 - (P.y^2 - P.x^2) := by
  --       calc
  --         1 - Ed25519.d * P.x ^ 2 * P.y ^ 2
  --         _ = 2 - (1 + Ed25519.d * P.x ^ 2 * P.y ^ 2) := by ring
  --         _ = 2 - (- P.x ^ 2 + P.y ^ 2 ) := by rw [h_curve]
  --         _= 2 - (P.y ^ 2 - P.x ^ 2) := by ring
  --     have h_comm : 1 - P.y^2 * P.x^2 * Ed25519.d = 1 - Ed25519.d * P.x^2 * P.y^2 := by ring
  --     field_simp [h_denom]; rw [h_comm]; ring_nf at h_denom; rw [eq_div_iff h_denom]; rw [h_subst]
  --     ring

  -- -- 4. Re-pack validity and equality using bridge lemmas
  -- constructor
  -- · exact ⟨P2, h_out_represents_P2⟩
  -- · rw [CompletedPoint.toPoint'_eq_of_isValid h_out_represents_P2]


end Edwards
