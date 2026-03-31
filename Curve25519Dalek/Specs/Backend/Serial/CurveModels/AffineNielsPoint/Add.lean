/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
/-! # Spec Theorem for `CompletedPoint::add`

Specification and proof for `CompletedPoint::add`.

This function implements the mixed addition of an AffineNielsPoint to an
Edwards point in extended coordinates, returning the result in completed
coordinates (ℙ¹ × ℙ¹). Given
- an EdwardsPoint P = (X:Y:Z:T) in extended ℙ³ coordinates (with X/Z = x, Y/Z = y, and T = XY/Z),
- an AffineNielsPoint N = (Y+X, Y−X, 2dXY),
it computes a CompletedPoint C = (X':Y':Z':T') corresponding to P + N.

The concrete formulas are:
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PP        = Y_plus_X  · N.y_plus_x
- MM        = Y_minus_X · N.y_minus_x
- Txy2d     = T · N.xy2d
- Z2        = Z + Z
- X'        = PP − MM
- Y'        = PP + MM
- Z'        = Z2 + Txy2d
- T'        = Z2 − Txy2d

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint

/-
natural language description:

• Takes an EdwardsPoint (X, Y, Z, T) in extended coordinates and an AffineNielsPoint
(Y+X, Y−X, 2dXY) and returns a CompletedPoint (X', Y', Z', T') in completed coordinates
(ℙ¹ × ℙ¹), representing the group addition P + N. Arithmetic is performed in the
field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given inputs P = (X, Y, Z, T) and N = (Y+X, Y−X, 2dXY), the output C = (X', Y', Z', T')
  satisfies modulo p:
  - X' ≡ ( (Y+X)·N.y_plus_x − (Y−X)·N.y_minus_x ) (mod p)
  - Y' ≡ ( (Y+X)·N.y_plus_x + (Y−X)·N.y_minus_x ) (mod p)
  - Z' ≡ ( 2·Z + T·N.xy2d ) (mod p)
  - T' ≡ ( 2·Z − T·N.xy2d ) (mod p)
-/

@[step]
theorem add_spec
    (self : edwards.EdwardsPoint)
    (other : backend.serial.curve_models.AffineNielsPoint)
    (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
    (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
    (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
    (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
    (h_otherYpX_bounds : ∀ i, i < 5 → (other.y_plus_x[i]!).val < 2 ^ 53)
    (h_otherYmX_bounds : ∀ i, i < 5 → (other.y_minus_x[i]!).val < 2 ^ 53)
    (h_otherXY2d_bounds : ∀ i, i < 5 → (other.xy2d[i]!).val < 2 ^ 53) :
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add self other ⦃ c =>
      let X := Field51_as_Nat self.X
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      let T := Field51_as_Nat self.T
      let YpX := Field51_as_Nat other.y_plus_x
      let YmX := Field51_as_Nat other.y_minus_x
      let XY2D := Field51_as_Nat other.xy2d
      let X' := Field51_as_Nat c.X
      let Y' := Field51_as_Nat c.Y
      let Z' := Field51_as_Nat c.Z
      let T' := Field51_as_Nat c.T
      (X' + Y * YmX) % p = (((Y + X) * YpX) + X * YmX) % p ∧
      (Y' + X * YmX) % p = (((Y + X) * YpX) + Y  * YmX) % p ∧
      Z' % p = ((2 * Z) + (T * XY2D)) % p ∧
      (T' + (T * XY2D)) % p = (2 * Z) % p ⦄ := by
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add
  simp only [step_simps]
  let* ⟨ Y_plus_X, Y_plus_X_post1, Y_plus_X_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
  let* ⟨ Y_minus_X, Y_minus_X_post1, Y_minus_X_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec
  let* ⟨ PP, PP_post1, PP_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ MM, MM_post1, MM_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ Txy2d, Txy2d_post1, Txy2d_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ Z2, Z2_post1, Z2_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
  obtain ⟨fe2, h_fe2_ok, fe2_post1, fe2_post2⟩ := CompletedPoint.add_spec' Z2_post2 Txy2d_post2
  simp only [h_fe2_ok, bind_tc_ok]
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec
  constructor
  · rw [← Nat.ModEq]
    rw [← Nat.ModEq] at fe_post2
    rw [← pointwise_add_Field51_as_Nat self.Y self.X Y_plus_X Y_plus_X_post1]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.y_minus_x) Y_minus_X_post2
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat fe) this)
    rw [add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm PP_post1)
    apply Nat.ModEq.trans (Nat.ModEq.symm fe_post2)
    apply Nat.ModEq.add_left
    exact MM_post1
  constructor
  · rw [← Nat.ModEq]
    rw [pointwise_add_Field51_as_Nat PP MM fe1 fe1_post1]
    have := Nat.ModEq.add PP_post1 MM_post1
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.y_minus_x) this
    apply Nat.ModEq.trans this
    rw [← pointwise_add_Field51_as_Nat self.Y self.X Y_plus_X Y_plus_X_post1, add_assoc]
    apply Nat.ModEq.add_left
    rw [← add_mul]
    apply Nat.ModEq.mul_right
    rw [← Nat.ModEq] at Y_minus_X_post2
    exact Y_minus_X_post2
  refine ⟨?_, ?_⟩
  · rw [← Nat.ModEq]
    rw [pointwise_add_Field51_as_Nat Z2 Txy2d fe2 fe2_post1,
       pointwise_add_Field51_as_Nat self.Z self.Z Z2 Z2_post1]
    simp only [(by omega : ∀ a, a + a = 2 * a)]
    apply Nat.ModEq.add_left _ Txy2d_post1
  · rw [← Nat.ModEq]
    rw [← Nat.ModEq] at fe3_post2
    have := Nat.ModEq.add_left (Field51_as_Nat fe3) Txy2d_post1
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe3_post2
    apply Nat.ModEq.trans this
    rw [pointwise_add_Field51_as_Nat self.Z self.Z Z2 Z2_post1,
       (by omega : ∀ a, a + a = 2 * a)]

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint
