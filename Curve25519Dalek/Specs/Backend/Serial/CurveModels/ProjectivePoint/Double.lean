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
-- simp_all is too heavy?
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
    -- Goal 1: Precondition for `X`
    intro i hi
    have hx := h_qX_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 2: Precondition for `Y`
    intro i hi
    have hy := h_qY_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 3: Precondition for `Z`
    intro i hi
    have hz := h_qZ_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 4: Precondition for `q.X+q.Y`
    intro i hi
    have hx := h_qX_bounds i hi
    have hy := h_qY_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 5: Precondition for `X_plus_Y`
    intro i hi
    have hx := h_qX_bounds i hi
    have hy := h_qY_bounds i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 6: Precondition for `YY_plus_XX`
    intro i hi
    have := YY_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 7: Precondition for `YY`
    intro i hi
    have := XX_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 8: Precondition for `XX`
    intro i hi
    have := YY_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 9: Precondition for `X_plus_Y_sq`
    intro i hi
    have := XX_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 10: Precondition for `YY_plus_XX`
    intro i hi
    have := X_plus_Y_sq_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 11: Precondition for `ZZ2`
    intro i hi
    have := ZZ2_post_2 i hi
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    -- Goal 12: Precondition for `YY_minus_XX`
    intro i hi
    have := YY_minus_XX_post_1 i hi
    scalar_tac
    -- END TASK
  -- Goal 13:
  -- BEGIN TASK
  unfold Field51_as_Nat at *

  have h_X_plus_Y : (∑ i ∈ Finset.range 5, 2^(51 * i) * (X_plus_Y[i]!).val) =
      (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.X[i]!).val) +
      (∑ i ∈ Finset.range 5, 2^(51 * i) * (q.Y[i]!).val) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
    intro i hi
    simp_all [Finset.mem_range, Nat.mul_add]

  have h_YY_plus_XX : (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY_plus_XX[i]!).val) =
      (∑ i ∈ Finset.range 5, 2^(51 * i) * (YY[i]!).val) +
      (∑ i ∈ Finset.range 5, 2^(51 * i) * (XX[i]!).val) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
    intro i hi
    simp_all [Finset.mem_range, Nat.mul_add]

  refine ⟨?_, ?_, ?_, ?_⟩

  · -- Goal 13.1: X' coordinate
    rw [h_X_plus_Y] at X_plus_Y_sq_post_1;
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

  · -- Goal 13.2: Y' coordinate
    rw [← Nat.ModEq] at *
    rw [h_YY_plus_XX]
    apply Nat.ModEq.add
    · grind
    · grind

  · -- Goal 13.3: Z' coordinate
    rw [← Nat.ModEq] at *; ring_nf at *;
    apply Nat.ModEq.trans (Nat.ModEq.add_left _ XX_post_1.symm)
    apply Nat.ModEq.trans YY_minus_XX_post_2
    exact YY_post_1

  · -- Goal 13.4: T' coordinate
    rw [← Nat.ModEq] at *;
    apply Nat.ModEq.trans fe1_post_2
    exact ZZ2_post_1
  -- END TASK


end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
