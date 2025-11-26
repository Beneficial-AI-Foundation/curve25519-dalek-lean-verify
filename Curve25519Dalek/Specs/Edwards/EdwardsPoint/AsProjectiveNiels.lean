/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub

/-! # Spec Theorem for `EdwardsPoint::as_projective_niels`

Specification and proof for `EdwardsPoint::as_projective_niels`.

This function converts an EdwardsPoint to a ProjectiveNielsPoint, which is a
representation optimized for point addition operations.

**Source**: curve25519-dalek/src/edwards.rs

-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.field.FieldElement51

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
    (h_bounds : ∀ i < 5, e.X[i]!.val < 2^53 ∧ e.Y[i]!.val < 2^53 ∧ e.Z[i]!.val < 2^53 ∧ e.T[i]!.val < 2^53) :
    ∃ pn,
    as_projective_niels e = ok pn ∧

    let X := Field51_as_Nat e.X
    let Y := Field51_as_Nat e.Y
    let Z := Field51_as_Nat e.Z
    let T := Field51_as_Nat e.T
    let A := Field51_as_Nat pn.Y_plus_X
    let B := Field51_as_Nat pn.Y_minus_X
    let Z' := Field51_as_Nat pn.Z
    let C := Field51_as_Nat pn.T2d
    let d2 := Field51_as_Nat backend.serial.u64.constants.EDWARDS_D2

    A % p = (Y + X) % p ∧
    (B + X) % p = Y % p ∧
    Z' % p = Z % p ∧
    C % p = (T * d2) % p := by
    unfold as_projective_niels

    have hX : ∀ i < 5, e.X[i]!.val < 2^53 := fun i hi => (h_bounds i hi).1
    have hY : ∀ i < 5, e.Y[i]!.val < 2^53 := fun i hi => (h_bounds i hi).2.1
    have hZ : ∀ i < 5, e.Z[i]!.val < 2^53 := fun i hi => (h_bounds i hi).2.2.1
    have hT : ∀ i < 5, e.T[i]!.val < 2^53 := fun i hi => (h_bounds i hi).2.2.2

    progress
    progress

    · intro i hi; apply lt_trans (hY i hi); norm_num
    · intro i hi; apply lt_trans (hX i hi); norm_num

    progress with Mul.mul_spec as ⟨ fe2, h_mul_math, h_mul_bounds ⟩

    · intro i hi
      apply lt_trans (hT i hi)
      norm_num

    · intro i hi
      simp only [backend.serial.u64.constants.EDWARDS_D2]
      dsimp [Aeneas.Std.eval_global, backend.serial.u64.constants.EDWARDS_D2_body]
      dsimp [backend.serial.u64.field.FieldElement51.from_limbs]
      interval_cases i
      all_goals decide

    refine ⟨?_, ?_, ?_⟩

    · -- Addition (A % p = (Y + X) % p)
      apply congrArg (· % p); unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl

      intro i hi
      rw [Finset.mem_range] at hi; rw [← Nat.mul_add]; congr 1
      progress

    · assumption

    · exact h_mul_math



end curve25519_dalek.edwards.EdwardsPoint
