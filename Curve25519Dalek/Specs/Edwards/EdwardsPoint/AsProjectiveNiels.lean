/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub

/-! # Spec Theorem for `EdwardsPoint::as_projective_niels`

Specification and proof for `EdwardsPoint::as_projective_niels`.

This function converts an EdwardsPoint to a ProjectiveNielsPoint, which is a
representation optimized for point addition operations.

Source: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64.field.FieldElement51
  curve25519_dalek.backend.serial.u64.constants
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
    spec (as_projective_niels e) (fun pn =>
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
    C % p = (T * d2) % p) := by
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

end curve25519_dalek.edwards.EdwardsPoint
