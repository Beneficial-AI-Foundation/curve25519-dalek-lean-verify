/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub

/-! # Spec Theorem for `EdwardsPoint::as_projective_niels`

Specification and proof for `EdwardsPoint::as_projective_niels`.

This function converts an EdwardsPoint to a ProjectiveNielsPoint, which is a
representation optimized for point addition operations.

Source: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field.FieldElement51
     curve25519_dalek.backend.serial.u64.constants
     curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.edwards

open Edwards

namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to ProjectiveNiels coordinates (A, B, Z', C), where:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z (unchanged)
  - C ≡ T * 2 * d (mod p)

natural language specs:

• The function always succeeds (no panic)
• For the input Edwards point (X, Y, Z, T), the resulting ProjectiveNielsPoint has coordinates:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z
  - C ≡ T * 2 * d (mod p)
where p = 2^255 - 19
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.as_projective_niels`**:
- No panic (always returns successfully)
- For the input Edwards point (X, Y, Z, T), the resulting ProjectiveNielsPoint has coordinates:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z
  - C ≡ T * 2 * d (mod p)
where p = 2^255 - 19
-/
@[progress]
theorem as_projective_niels_spec (e : EdwardsPoint)
    (h_bounds : ∀ i < 5, e.X[i]!.val < 2 ^ 53 ∧ e.Y[i]!.val < 2 ^ 53 ∧
      e.Z[i]!.val < 2 ^ 53 ∧ e.T[i]!.val < 2 ^ 53) :
    ∃ pn, as_projective_niels e = ok pn ∧
    let X := Field51_as_Nat e.X
    let Y := Field51_as_Nat e.Y
    let Z := Field51_as_Nat e.Z
    let T := Field51_as_Nat e.T
    let A := Field51_as_Nat pn.Y_plus_X
    let B := Field51_as_Nat pn.Y_minus_X
    let Z' := Field51_as_Nat pn.Z
    let C := Field51_as_Nat pn.T2d
    let d2 := Field51_as_Nat EDWARDS_D2
    A % p = (Y + X) % p ∧
    (B + X) % p = Y % p ∧
    Z' % p = Z % p ∧
    C % p = (T * d2) % p := by
  unfold as_projective_niels
  progress*
  · -- BEGIN TASK
    intro i hi
    have := (h_bounds i hi).2.2.2
    grind
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have := (h_bounds i hi).2.2.2
    grind
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have :=(h_bounds i hi).2.2.2
    grind
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have :=(h_bounds i hi).2.2.2
    grind
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    have :=(h_bounds i hi).2.2.2
    grind
    -- END TASK
  · -- BEGIN TASK
    intro i hi
    unfold EDWARDS_D2 Aeneas.Std.eval_global EDWARDS_D2_body from_limbs
    interval_cases i
    all_goals decide
    -- END TASK
  · refine ⟨?_, ?_, ?_⟩
    · -- BEGIN TASK
      apply congrArg (· % p)
      unfold Field51_as_Nat
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      grind
      -- END TASK
    · -- BEGIN TASK
      assumption
      -- END TASK
    · -- BEGIN TASK
      assumption
      -- END TASK

/--
Geometric verification of `as_projective_niels`.
The theorem states that converting an EdwardsPoint to ProjectiveNiels coordinates
preserves the underlying mathematical point.
-/
theorem as_projective_niels_spec'
    (e : ExtendedPoint) (he_valid : e.IsValid) (he_bounds : e.InBounds) :
    ∃ n, e.as_projective_niels = ok n ∧
    n.IsValid ∧
    (n : Point Ed25519) = (e : Point Ed25519) := by
  have he_valid' : e.IsValid := he_valid
  rcases he_valid' with ⟨P, hP⟩

  have h_bounds_spec : ∀ i < 5, e.X[i]!.val < 2 ^ 53 ∧ e.Y[i]!.val < 2 ^ 53 ∧
      e.Z[i]!.val < 2 ^ 53 ∧ e.T[i]!.val < 2 ^ 53 := by
    intro i hi
    rcases he_bounds with ⟨hX, hY, hZ, hT⟩
    refine ⟨?_, ?_, ?_, ?_ ⟩
    · --
      have hX' := hX i hi; scalar_tac
    · --
      have hY' := hY i hi; scalar_tac
    · --
      have hZ' := hZ i hi; scalar_tac
    · --
      have hT' := hT i hi; scalar_tac

  have ⟨n, h_run, h_arith⟩ := as_projective_niels_spec e h_bounds_spec
  rcases h_arith with ⟨hA_raw, hB_raw, hZ_raw, hT_raw⟩

  have hA : (Field51_as_Nat n.Y_plus_X : CurveField) = Field51_as_Nat e.Y + Field51_as_Nat e.X := by
    rw [←Nat.cast_add]
    apply lift_mod_eq _ _ hA_raw

  have hB : (Field51_as_Nat n.Y_minus_X : CurveField) = Field51_as_Nat e.Y - Field51_as_Nat e.X := by
    apply eq_sub_of_add_eq
    rw [←Nat.cast_add]
    apply lift_mod_eq _ _ hB_raw

  have hZ' : (Field51_as_Nat n.Z : CurveField) = Field51_as_Nat e.Z := by
    apply lift_mod_eq _ _ hZ_raw

  have hC : (Field51_as_Nat n.T2d : CurveField) = Field51_as_Nat e.T * Field51_as_Nat EDWARDS_D2 := by
    rw [←Nat.cast_mul]
    apply lift_mod_eq _ _ hT_raw

  use n

  refine ⟨by exact h_run, ?_, ?_ ⟩
  · -- subgoal 1
    rcases hP with ⟨hZ_ne_zero, hX_eq, hY_eq, hT_eq⟩
    use P
    dsimp [field_from_limbs] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    · --
      rw [hZ']; exact hZ_ne_zero
    · --
      rw [hA, hX_eq, hY_eq, hZ']; try ring
    · --
      rw [hB, hY_eq, hX_eq, hZ']; try ring
    · --
      rw [hC, hZ', hT_eq]
      have h_const : (Field51_as_Nat EDWARDS_D2 : CurveField) = 2 * Ed25519.d := by
          rw [EDWARDS_D2, Ed25519]
          dsimp; rw [d];
          unfold Aeneas.Std.eval_global EDWARDS_D2_body from_limbs
          try decide
      rw [h_const]; try ring
  · --subgoal 2
    have he_eq : e.toPoint' = P := by
      rw [ExtendedPoint.toPoint', dif_pos he_valid]
      progress*
      rcases hP with ⟨hz, hx, hy, ht⟩
      ext <;> apply mul_right_cancel₀ hz
      · rw [←hx];
        sorry
      · rw [←hy];
        sorry

    have hn_valid : n.IsValid := by
      rcases hP with ⟨hZ_ne_zero, hX_eq, hY_eq, hT_eq⟩
      unfold ProjectiveNielsPoint.IsValid
      use P
      dsimp only [field_from_limbs] at *
      refine ⟨?_, ?_, ?_, ?_⟩
      · --
        rw [hZ']; exact hZ_ne_zero
      · --
        rw [hA, hZ', hY_eq, hX_eq]; try ring
      · --
        rw [hB, hZ', hY_eq, hX_eq]; try ring
      · --
        rw [hC, hT_eq, hZ']
        have h_const : (Field51_as_Nat EDWARDS_D2 : CurveField) = 2 * Ed25519.d := by
          rw [EDWARDS_D2, Ed25519]
          dsimp; rw [d];
          unfold Aeneas.Std.eval_global EDWARDS_D2_body from_limbs
          try decide

        rw [h_const]; try ring

    have hn_eq : n.toPoint' = P := by
      rw [ProjectiveNielsPoint.toPoint']
      rcases hn_valid with ⟨hz, ha, hb, hy_minus_x⟩
      ext
      · --
        sorry
      · --
        sorry

    rw [he_eq, hn_eq]
    


end curve25519_dalek.edwards.EdwardsPoint
