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
-/
@[progress]
theorem double_spec (q : ProjectivePoint)
    (h_qX_bounds : ∀ i < 5, (q.X[i]!).val ≤ 2 ^ 52)
    (h_qY_bounds : ∀ i < 5, (q.Y[i]!).val ≤ 2 ^ 52)
    (h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val ≤ 2 ^ 52) :
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
    (T' + Z') % p = (2 * Z^2) % p := by
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
  · -- BEGIN TASK
    intro i hi
    have := h_qZ_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := h_qX_bounds i hi
    have := h_qY_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := h_qX_bounds i hi
    have := h_qY_bounds i hi
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
    have := X_plus_Y_sq_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := ZZ2_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := YY_minus_XX_post_1 i hi
    scalar_tac
    -- END TASK
  unfold Field51_as_Nat at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- BEGIN TASK
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
      apply Nat.ModEq.add; grind; grind
    apply Nat.ModEq.add_left_cancel hB_equiv; rw [add_comm]
    ring_nf at *
    rw [← Nat.ModEq] at fe_post_2
    apply Nat.ModEq.trans fe_post_2
    exact X_plus_Y_sq_post_1
    -- END TASK
  · -- BEGIN TASK
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
  · -- BEGIN TASK
    rw [← Nat.ModEq] at *; ring_nf at *;
    apply Nat.ModEq.trans (Nat.ModEq.add_left _ XX_post_1.symm)
    apply Nat.ModEq.trans YY_minus_XX_post_2
    exact YY_post_1
    -- END TASK
  · -- BEGIN TASK
    rw [← Nat.ModEq] at *;
    apply Nat.ModEq.trans fe1_post_2
    exact ZZ2_post_1
    -- END TASK

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/-! ## Mathematical Verification

This section proves that the geometric implementation `double_spec` corresponds to the
mathematical operation of point doubling on the Edwards curve.

The proof bridges low-level Rust implementation to high-level mathematics using the
infrastructure from `Curve25519Dalek.Defs.Edwards`.
-/

namespace Edwards

open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- Helper lemma for modular arithmetic lifting -/
theorem lift_mod_eq (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) := by
  apply (ZMod.natCast_eq_natCast_iff a b p).mpr
  exact h

/--
Verification of the `double` function.
The theorem states that the Rust implementation of point doubling corresponds
exactly to the mathematical addition of the point to itself (`q + q`) on the Edwards curve.
-/
theorem double_spec_math
    (q : ProjectivePoint) (hq_valid : q.IsValid') (hq_bounds : q.InBounds) :
    ∃ c, ProjectivePoint.double q = .ok c ∧ c.IsValid' ∧
    (↑c : Point Ed25519) = ↑q + ↑q := by

  -- 1. Unwrap validity witness P from the input
  rcases hq_valid with ⟨P, hP⟩

  -- Bridge: Convert the coerced q back to P using our previous lemmas
  have h_q_eq_P : (↑q : Point Ed25519) = P := ProjectivePoint.toPoint'_eq_of_isValid hP
  rw [h_q_eq_P]

  -- 2. Run the Aeneas specification
  have ⟨out, h_run, h_arith⟩ := ProjectivePoint.double_spec q
    (fun i h => hq_bounds.1 i h)
    (fun i h => hq_bounds.2.1 i h)
    (fun i h => hq_bounds.2.2 i h)

  exists out
  constructor; · exact h_run

  -- 3. Mathematical Arithmetic Proof
  -- This block proves that the output limbs correspond to P + P coordinates.
  let P2 := P + P

  have h_out_represents_P2 : out.IsValid P2 := by
    rw [ProjectivePoint.IsValid] at hP
    rcases hP with ⟨hZ_nonzero, hX_in, hY_in⟩
    rcases h_arith with ⟨hX_new, hY_new, hZ_new, hT_new⟩

    -- Lift low-level limbs to field elements
    let X_nat := Field51_as_Nat q.X
    let Y_nat := Field51_as_Nat q.Y
    let Z_nat := Field51_as_Nat q.Z

    have hX_F : field_from_limbs out.X = 2 * field_from_limbs q.X * field_from_limbs q.Y := by
      dsimp [field_from_limbs]; rw [lift_mod_eq _ _ hX_new]; push_cast; rfl

    have hY_F : field_from_limbs out.Y = field_from_limbs q.Y ^ 2 + field_from_limbs q.X ^ 2 := by
      dsimp [field_from_limbs]; rw [lift_mod_eq _ _ hY_new]; push_cast; rfl

    have hZ_F : field_from_limbs out.Z = field_from_limbs q.Y ^ 2 - field_from_limbs q.X ^ 2 := by
      have h := lift_mod_eq _ _ hZ_new; push_cast at h; apply eq_sub_of_add_eq h

    have hT_F : field_from_limbs out.T = 2 * field_from_limbs q.Z ^ 2 - field_from_limbs out.Z := by
      have h := lift_mod_eq _ _ hT_new; push_cast at h; apply eq_sub_of_add_eq h

    -- Setup Curve Identities
    unfold CompletedPoint.IsValid
    have h_d_not_square : ¬IsSquare Ed25519.d := sorry
    have h_neg_one_square : IsSquare (-1 : CurveField) := by
      apply ZMod.exists_sq_eq_neg_one_iff.mpr; decide

    have h_curve : -P.x^2 + P.y^2 = 1 + Ed25519.d * P.x^2 * P.y^2 := by
      have h := P.h_on_curve; simp only [Ed25519, neg_mul, one_mul] at h; exact h

    -- Helper: Prove denominators are non-zero
    have h_denom_plus : 1 + Ed25519.d * P.x^2 * P.y^2 ≠ 0 := by
      intro h_zero
      rw [add_eq_zero_iff_eq_neg] at h_zero
      have ⟨k, hk⟩ := h_neg_one_square
      rw [←neg_eq_iff_eq_neg, hk] at h_zero
      by_cases h_xy_nz : P.x * P.y = 0
      · rw [mul_assoc, ← mul_pow, h_xy_nz] at h_zero
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h_zero
        rw [h_zero] at hk; norm_num at hk;

      · apply h_d_not_square
        use k / (P.x * P.y)
        field_simp [h_xy_nz]; ring_nf at h_zero; rw [h_zero]
        have h_nz : P.x^2 * P.y^2 ≠ 0 := by
          rw [←mul_pow]
          exact pow_ne_zero 2 h_xy_nz
        rw [mul_assoc, mul_div_cancel_right₀ _ h_nz]

    have h_denom_minus : 1 - Ed25519.d * P.x^2 * P.y^2 ≠ 0 := by
      intro h_zero
      rw [sub_eq_zero] at h_zero

      by_cases h_xy_nz : P.x * P.y = 0
      · rw [mul_assoc, ← mul_pow, h_xy_nz] at h_zero
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h_zero
        norm_num at h_zero
      · apply h_d_not_square
        use 1 / (P.x * P.y)
        rw [mul_assoc] at h_zero; field_simp [h_xy_nz]; rw [← mul_pow] at h_zero ⊢
        have h_nz_sq : (P.x * P.y) ^ 2 ≠ 0 := pow_ne_zero 2 h_xy_nz
        rw [eq_div_iff h_nz_sq]; ring_nf at h_zero ⊢; exact h_zero.symm

    -- Prove the 4 components of IsValid (Z≠0, T≠0, X correct, Y correct)
    refine ⟨?_, ?_, ?_, ?_⟩

    -- 1. Prove Z ≠ 0
    · rw [hZ_F, hX_in, hY_in]
      grind

    -- 2. Prove T ≠ 0
    · rw [hT_F, hZ_F, hX_in, hY_in]
      rw [mul_pow, mul_pow]
      have h_factor : 2 * field_from_limbs q.Z ^ 2 -
        (P.y^2 * field_from_limbs q.Z ^ 2 - P.x^2 * field_from_limbs q.Z ^ 2) =
                      field_from_limbs q.Z ^ 2 * (2 - (P.y^2 - P.x^2)) := by ring
      rw [h_factor]
      apply mul_ne_zero
      · exact pow_ne_zero 2 hZ_nonzero
      · have h_curve' : 2 - (P.y^2 - P.x^2) = 1 - Ed25519.d * P.x^2 * P.y^2 := by
          calc
            2 - (P.y ^ 2 - P.x ^ 2)
            _ = 2 - (-P.x ^ 2 + P.y ^ 2) := by ring
            _= 2 - (1 + Ed25519.d * P.x ^ 2 * P.y ^ 2) := by rw [← h_curve]
            _ = 1 - Ed25519.d * P.x ^ 2 * P.y ^ 2 := by ring
        rw [h_curve']
        exact h_denom_minus

    -- 3. Verify X coordinate
    · rw [(add_def P P).1]; dsimp only [add_coords]
      rw [hX_F, hZ_F, hX_in, hY_in]

      have h_denom : 1 + Ed25519.d * P.x * P.x * P.y * P.y ≠ 0 := by convert h_denom_plus using 1; ring
      have h_subst : 1 + Ed25519.d * P.x^2 * P.y^2 = P.y^2 - P.x^2 := by rw [←h_curve]; ring
      have h_comm : 1 + P.x^2 * P.y^2 * Ed25519.d = 1 + Ed25519.d * P.x^2 * P.y^2 := by ring
      field_simp [h_denom, ← h_curve]; rw [h_comm]; ring_nf at h_denom; rw [eq_div_iff h_denom, h_subst]
      ring_nf

    -- 4. Verify Y coordinate
    · rw [(add_def P P).2]; dsimp only [add_coords]

      rw [hY_F, hT_F, hZ_F, hX_in, hY_in]

      have h_a : Ed25519.a = -1 := rfl; rw [h_a]

      have h_denom : 1 - Ed25519.d * P.x * P.x * P.y * P.y ≠ 0 := by convert h_denom_minus using 1; ring
      have h_subst : 1 - Ed25519.d * P.x^2 * P.y^2 = 2 - (P.y^2 - P.x^2) := by
        calc
          1 - Ed25519.d * P.x ^ 2 * P.y ^ 2
          _ = 2 - (1 + Ed25519.d * P.x ^ 2 * P.y ^ 2) := by ring
          _ = 2 - (- P.x ^ 2 + P.y ^ 2 ) := by rw [h_curve]
          _= 2 - (P.y ^ 2 - P.x ^ 2) := by ring
      have h_comm : 1 - P.y^2 * P.x^2 * Ed25519.d = 1 - Ed25519.d * P.x^2 * P.y^2 := by ring
      field_simp [h_denom]; rw [h_comm]; ring_nf at h_denom; rw [eq_div_iff h_denom]; rw [h_subst]
      ring

  -- 4. Re-pack validity and equality using bridge lemmas
  constructor
  · exact ⟨P2, h_out_represents_P2⟩
  · rw [CompletedPoint.toPoint'_eq_of_isValid h_out_represents_P2]


end Edwards
