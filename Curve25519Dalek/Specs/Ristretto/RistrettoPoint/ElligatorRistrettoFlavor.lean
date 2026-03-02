/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.FunsExternal
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended

/-! # Spec Theorem for `RistrettoPoint::elligator_ristretto_flavor`

Specification and proof for `RistrettoPoint::elligator_ristretto_flavor`.

This function implements the Ristretto Elligator map, which is the MAP function
defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4).

It maps an arbitrary field element s to a valid Ristretto point.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.math
open Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a field element s and maps it to a valid RistrettoPoint using the Elligator map:

  https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4

  Arithmetics are performed in the field 𝔽ₚ where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic) for all valid field element inputs s
• The output is indeed a valid RistrettoPoint (i.e., an even Edwards point that lies on the curve)
• The output matches the pure mathematical Elligator map applied to the field value of s
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.elligator_ristretto_flavor`**:
• The function always succeeds (no panic) for all valid field element inputs
• The output is indeed a valid RistrettoPoint (i.e., an even Edwards point that lies on the curve)
• The output point corresponds to `elligator_ristretto_flavor_pure s.toField`, bridging
  the implementation to the pure mathematical Elligator map defined in Representation.lean
-/
@[progress]
theorem elligator_ristretto_flavor_spec
    (s : backend.serial.u64.field.FieldElement51)
    (h_s_valid : s.IsValid) :
    elligator_ristretto_flavor s ⦃ result =>
    result.IsValid ∧
    result.toPoint = (elligator_ristretto_flavor_pure s.toField).val ⦄ := by
  unfold elligator_ristretto_flavor
  progress*
  · exact h_s_valid -- 1: s < 2^54 (square precond)
  · intro i hi;
    unfold backend.serial.u64.constants.SQRT_M1
    interval_cases i <;> decide -- 2: SQRT_M1 < 2^54
  · intro i hi; have := r_0_sq_post_2 i hi; omega -- 3: r_0_sq < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 4: r < 2^53
  · intro i hi;
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide -- 5: ONE < 2^53
  · intro i hi;
    unfold backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED
    interval_cases i <;> decide -- 6: ONE_MINUS_EDWARDS_D_SQUARED < 2^54
  · intro i hi;
    unfold backend.serial.u64.constants.EDWARDS_D
    interval_cases i <;> decide -- 7: EDWARDS_D < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 8: r < 2^54
  · intro i hi;
    unfold backend.serial.u64.constants.MINUS_ONE
    interval_cases i <;> decide -- 9: MINUS_ONE < 2^63
  · intro i hi; have := d_times_r_post_2 i hi; omega -- 10: d_times_r < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 11: r < 2^53
  · intro i hi;
    unfold backend.serial.u64.constants.EDWARDS_D
    interval_cases i <;> decide -- 12: EDWARDS_D < 2^53
  · intro i hi; have := c_minus_dr_post_1 i hi; omega -- 13: c_minus_dr < 2^54
  · intro i hi; have := N_s_post_2 i hi; omega -- 14: N_s ≤ 2^52-1
  · intro i hi; have := D_post_2 i hi; omega -- 15: D ≤ 2^52-1
  · intro i hi; have := __discr_post_1 i hi; omega -- 16: __discr.2 < 2^54
  · exact h_s_valid -- 17: s < 2^54 (mul rhs)
  · intro i hi; have := s_prime_post_2 i hi; omega -- 18: s_prime < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 19: r < 2^63
  · intro i hi;
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide -- 20: ONE < 2^54
  · intro i hi; simp only [c1_post i hi] -- 21: c1 < 2^54 (conditional_assign)
    split
    · have := r_post_2 i hi; omega
    · unfold backend.serial.u64.constants.MINUS_ONE; interval_cases i <;> decide
  · intro i hi; have := r_minus_one_post_1 i hi; omega -- 22: r_minus_one < 2^54
  · intro i hi; have := c_r_minus_one_post_2 i hi; omega -- 23: c_r_minus_one < 2^54
  · intro i hi; -- 24: EDWARDS_D_MINUS_ONE_SQUARED < 2^54
    unfold backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED
    interval_cases i <;> decide
  · intro i hi; have := c_r_minus_one_post_2 i hi;
    grind only [#b83a]
  · intro i hi; have := D_post_2 i hi; omega -- 26: D < 2^54
  · intro i hi; simp only [s1_post i hi] -- 27: s1 < 2^54 (conditional)
    split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post_2 i hi; omega
      · have := s_prime_post_2 i hi; omega
    · have := __discr_post_1 i hi; omega
  · intro i hi; simp only [s1_post i hi] -- 28: s1 < 2^53 (conditional)
    split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post_2 i hi; omega
      · have := s_prime_post_2 i hi; omega
    · have := __discr_post_1 i hi; omega
  · intro i hi; simp only [s1_post i hi] -- 29: s1 < 2^53 (conditional)
    split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post_2 i hi; omega
      · have := s_prime_post_2 i hi; omega
    · have := __discr_post_1 i hi; omega
  · intro i hi; have := D_post_2 i hi; omega -- 30: D < 2^54
  · intro i hi; have := N_t_post_1 i hi; omega -- 31: N_t < 2^54
  · intro i hi; -- 32: SQRT_AD_MINUS_ONE < 2^54
    unfold backend.serial.u64.constants.SQRT_AD_MINUS_ONE
    interval_cases i <;> decide
  · intro i hi; -- 33: ONE < 2^63
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide
  · intro i hi; have := s_sq_post_2 i hi; omega -- 34: s_sq < 2^54
  · intro i hi; -- 35: ONE < 2^53
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide
  · intro i hi; have := s_sq_post_2 i hi; omega -- 36: s_sq < 2^53
  · intro i hi; have h := cp_X_post_2 i hi -- 37: cp_X < 2^54
    simp only [Array.getElem!_Nat_eq] at h ⊢; omega
  · intro i hi; have h := cp_Y_post_1 i hi -- 38: cp_Y < 2^54
    simp only [Array.getElem!_Nat_eq] at h ⊢; omega
  · intro i hi; have h := cp_Z_post_2 i hi -- 39: cp_Z < 2^54
    simp only [Array.getElem!_Nat_eq] at h ⊢; omega
  · -- 40: IsValid ∧ toPoint = elligator_ristretto_flavor_pure
    -- Step 1: Lift arithmetic postconditions to field equalities
    have hX_F : ep.X.toField = cp_X.toField * cp_T.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_1
      push_cast at h; exact h
    have hY_F : ep.Y.toField = cp_Y.toField * cp_Z.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_2
      push_cast at h; exact h
    have hZ_F : ep.Z.toField = cp_Z.toField * cp_T.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_3
      push_cast at h; exact h
    have hT_F : ep.T.toField = cp_X.toField * cp_Y.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_4
      push_cast at h; exact h
    have h_cp_T_F : cp_T.toField = 1 + s1.toField ^ 2 := by
        unfold toField
        have h_nat : Field51_as_Nat cp_T = Field51_as_Nat ONE + Field51_as_Nat s_sq := by
          unfold Field51_as_Nat
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi; rw [cp_T_post_1 i hi, mul_add]
        rw [h_nat]; push_cast
        have hsq := lift_mod_eq _ _ s_sq_post_1
        push_cast at hsq; rw [hsq, ONE_spec]
        simp only [Nat.cast_one]
    -- Step 2: Prove ep.Z.toField ≠ 0
    -- Elligator invariant: the denominator 1 + s² is never zero in 𝔽_p
    -- for the specific s produced by the algorithm.
    have h_cp_T_ne : cp_T.toField ≠ 0 := by
      rw [h_cp_T_F]
      intro h_zero
      have h_s1_sq_eq_m1 : s1.toField ^ 2 = -1 := by
        linear_combination h_zero
      
      -- Elligator invariant: The value `s1` produced by the map never squares to -1.
      -- This requires analyzing the `sqrt_ratio_i` output and `not_sq` selection.
      sorry -- Elligator invariant: 1 + s₁² ≠ 0 in 𝔽_p
    -- Elligator invariant: N_t · √(ad−1) is never zero in 𝔽_p.
    -- √(ad−1) ≠ 0 follows from sqrt_ad_minus_one_ne_zero;
    -- N_t ≠ 0 requires algorithmic reasoning about the Elligator map.
    have h_cp_Z_ne : cp_Z.toField ≠ 0 := by
      sorry -- Elligator invariant: N_t · √(ad−1) ≠ 0 in 𝔽_p
    have hZ_ne : ep.Z.toField ≠ 0 := by
      rw [hZ_F]
      exact mul_ne_zero h_cp_Z_ne h_cp_T_ne
    -- Step 3: Completed point lies on the twisted Edwards curve.
    -- This is the key Elligator invariant: the map produces a valid curve point.
    have h_cp_curve :
        Ed25519.a * cp_X.toField ^ 2 * cp_T.toField ^ 2 +
          cp_Y.toField ^ 2 * cp_Z.toField ^ 2 =
        cp_Z.toField ^ 2 * cp_T.toField ^ 2 +
          Ed25519.d * cp_X.toField ^ 2 * cp_Y.toField ^ 2 := by
      sorry -- Elligator invariant: completed point (cp_X, cp_Y, cp_Z, cp_T) on curve
    -- Step 4: Assemble EdwardsPoint.IsValid
    have h_ep_valid : edwards.EdwardsPoint.IsValid ep := {
      X_bounds := fun i hi => by have := ep_post_5 i hi; omega
      Y_bounds := fun i hi => by have := ep_post_6 i hi; omega
      Z_bounds := fun i hi => by have := ep_post_7 i hi; omega
      T_bounds := fun i hi => by have := ep_post_8 i hi; omega
      Z_ne_zero := hZ_ne
      T_relation := by rw [hX_F, hY_F, hT_F, hZ_F]; ring
      on_curve := by
        simp only [hX_F, hY_F, hZ_F]
        linear_combination (cp_Z.toField ^ 2 * cp_T.toField ^ 2) * h_cp_curve
    }
    constructor
    · -- RistrettoPoint.IsValid ep = EdwardsPoint.IsValid ∧ IsSquare (Z² - Y²)
      refine ⟨h_ep_valid, ?_⟩
      simp only [hZ_F, hY_F]
      -- Goal: IsSquare ((cpZ*cpT)² - (cpY*cpZ)²)
      -- Factor: cpZ² · (cpT² - cpY²) with cpT = 1+s², cpY = 1-s²
      --   ⟹ cpZ² · 4 · s1² = (2 · cpZ · s1)²
      have h_s_sq_F : s_sq.toField = s1.toField ^ 2 := by
        unfold toField
        have h := lift_mod_eq _ _ s_sq_post_1
        push_cast at h; exact h
      have h_cp_Y_F : cp_Y.toField + s_sq.toField = ONE.toField := by
        unfold toField
        have h := lift_mod_eq _ _ cp_Y_post_2
        push_cast at h; exact h
      have h_cp_T_F : cp_T.toField = ONE.toField + s_sq.toField := by
        unfold toField
        have h_nat : Field51_as_Nat cp_T = Field51_as_Nat ONE + Field51_as_Nat s_sq := by
          unfold Field51_as_Nat
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi; rw [cp_T_post_1 i hi, mul_add]
        rw [h_nat]; push_cast; ring
      have h_ONE_F : ONE.toField = (1 : CurveField) := by
        unfold toField; rw [ONE_spec]; simp only [Nat.cast_one]
      exact ⟨2 * cp_Z.toField * s1.toField, by
        have h_Y : cp_Y.toField = ONE.toField - s_sq.toField := by
          linear_combination h_cp_Y_F
        rw [h_cp_T_F, h_Y, h_s_sq_F, h_ONE_F]; ring⟩
    · -- toPoint ep = (elligator_ristretto_flavor_pure s.toField).val
      -- Strategy: decompose into x and y coordinate equality, then show
      -- each coordinate of the implementation matches the pure Elligator map.
      -- ep.toPoint = (ep.X/ep.Z, ep.Y/ep.Z) = (cp_X/cp_Z, cp_Y/cp_T)
      -- Pure spec: x = 2sD/(N_t·√(ad-1)), y = (1-s²)/(1+s²)
      sorry




end curve25519_dalek.ristretto.RistrettoPoint
