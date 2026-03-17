/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add




/- # Spec Theorem for `CompletedPoint::sub`

Specification and proof for `CompletedPoint::sub`.

This function implements the mixed subtraction of an AffineNielsPoint from an
Edwards point in extended coordinates, returning the result in completed
coordinates (ℙ¹ × ℙ¹). Given
- an EdwardsPoint P = (X:Y:Z:T) in extended ℙ³ coordinates (with X/Z = x, Y/Z = y, and T = XY/Z),
- an AffineNielsPoint N = (Y+X, Y−X, 2dXY),
it computes a CompletedPoint C = (X':Y':Z':T') corresponding to P − N.

The concrete formulas are:
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PM        = Y_plus_X  · N.y_minus_x
- MP        = Y_minus_X · N.y_plus_x
- Txy2d     = T · N.xy2d
- Z2        = Z + Z
- X'        = PM − MP
- Y'        = PM + MP
- Z'        = Z2 − Txy2d
- T'        = Z2 + Txy2d

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/


open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint



/-
natural language description:

• Takes an EdwardsPoint (X, Y, Z, T) in extended coordinates and an AffineNielsPoint
(Y+X, Y−X, 2dXY) and returns a CompletedPoint (X', Y', Z', T') in completed coordinates
(ℙ¹ × ℙ¹), representing the group subtraction P − N. Arithmetic is performed in the
field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given inputs P = (X, Y, Z, T) and N = (Y+X, Y−X, 2dXY), the output C = (X', Y', Z', T')
  satisfies modulo p:
  - X' ≡ ( (Y+X)·N.y_minus_x − (Y−X)·N.y_plus_x ) (mod p)
  - Y' ≡ ( (Y+X)·N.y_minus_x + (Y−X)·N.y_plus_x ) (mod p)
  - Z' ≡ ( 2·Z − T·N.xy2d ) (mod p)
  - T' ≡ ( 2·Z + T·N.xy2d ) (mod p)
-/


@[progress]
theorem sub_spec
  (self : edwards.EdwardsPoint)
  (other : backend.serial.curve_models.AffineNielsPoint)
  (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
  (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
  (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
  (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
  (h_otherYpX_bounds : ∀ i, i < 5 → (other.y_plus_x[i]!).val < 2 ^ 53)
  (h_otherYmX_bounds : ∀ i, i < 5 → (other.y_minus_x[i]!).val < 2 ^ 53)
  (h_otherXY2d_bounds : ∀ i, i < 5 → (other.xy2d[i]!).val < 2 ^ 53) :
Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub self other ⦃ c =>
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
(X' + Y * YpX) % p = (((Y + X) * YmX) + X * YpX) % p ∧
(Y' + X * YpX) % p = (((Y + X) * YmX) + Y  * YpX) % p ∧
(Z' + (T * XY2D)) % p = (2 * Z) % p ∧
T' % p = ((2 * Z) + (T * XY2D)) % p ⦄
:= by
  unfold Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub
  progress as ⟨Y_plus_X , h_Y_plus_X, Y_plus_X_bounds ⟩
  progress as ⟨Y_minus_X,   Y_minus_X_bounds, h_Y_minus_X⟩
  progress  as ⟨ PM , h_PM , PM_bounds⟩
  progress  as ⟨ MP, h_MP, MP_bounds⟩
  progress  as ⟨ Txy2d, h_Txy2d, Txy2d_bounds⟩
  progress as ⟨Z2, hZ2,  fZ2bounds⟩
  progress as ⟨fe1, h_fe1,  fe1_bounds⟩
  have hzz: ∀ i < 5, Z2[i]!.val < 2 ^ 54 := by simp_all
  obtain ⟨MPPM, h_MPPM_ok, h_MPPM, MPPM_bounds⟩ := CompletedPoint.add_spec' hzz  Txy2d_bounds
  simp only [h_MPPM_ok, bind_tc_ok]
  progress as ⟨fe2, h_fe2, fe2_bounds⟩
  progress as ⟨fe3, h_fe3, fe3_bounds⟩
  constructor
  · rw[← Nat.ModEq]
    rw[← Nat.ModEq] at fe1_bounds
    rw[← pointwise_add_Field51_as_Nat self.Y self.X Y_plus_X h_Y_plus_X]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.y_plus_x) h_Y_minus_X
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat fe1) this)
    rw[add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply  Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm h_PM)
    apply Nat.ModEq.trans (Nat.ModEq.symm fe1_bounds)
    apply Nat.ModEq.add_left
    exact h_MP
  constructor
  · rw[← Nat.ModEq]
    rw[pointwise_add_Field51_as_Nat PM MP fe2 h_fe2]
    have := Nat.ModEq.add h_PM h_MP
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.y_plus_x) this
    apply Nat.ModEq.trans this
    rw[← pointwise_add_Field51_as_Nat self.Y self.X Y_plus_X h_Y_plus_X, add_assoc]
    apply Nat.ModEq.add_left
    rw[← add_mul]
    apply Nat.ModEq.mul_right
    rw[← Nat.ModEq] at h_Y_minus_X
    exact h_Y_minus_X
  constructor
  · rw[← Nat.ModEq]
    rw[← Nat.ModEq] at fe3_bounds
    have :=  Nat.ModEq.add_left  (Field51_as_Nat fe3) h_Txy2d
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe3_bounds
    apply Nat.ModEq.trans this
    rw[pointwise_add_Field51_as_Nat self.Z self.Z Z2 hZ2,
       (by scalar_tac :∀ a, a + a = 2 * a)]
  · rw[← Nat.ModEq]
    rw[pointwise_add_Field51_as_Nat Z2 Txy2d MPPM h_MPPM,
       pointwise_add_Field51_as_Nat self.Z self.Z Z2 hZ2]
    simp only [(by scalar_tac :∀ a, a + a = 2 * a)]
    apply Nat.ModEq.add_left _ h_Txy2d

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint
