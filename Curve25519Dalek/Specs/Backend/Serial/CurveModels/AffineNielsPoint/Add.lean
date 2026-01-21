/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
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

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.curve_models.AddShared0EdwardsPointSharedAAffineNielsPointCompletedPoint




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

set_option maxHeartbeats 1000000 in
-- simp_all is heavy


@[progress]
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
∃ c,
add self other = ok c ∧
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
(T' + (T * XY2D)) % p = (2 * Z) % p
:= by
  unfold AddShared0EdwardsPointSharedAAffineNielsPointCompletedPoint.add
  progress as ⟨Y_plus_X , h_Y_plus_X, Y_plus_X_bounds ⟩
  progress as ⟨Y_minus_X,   Y_minus_X_bounds, h_Y_minus_X⟩
  · grind
  · grind
  progress  as ⟨ PP , h_PP , PP_bounds⟩
  · grind
  progress  as ⟨ MM, h_MM, MM_bounds⟩
  · grind
  · grind
  progress  as ⟨ Txy2d, h_Txy2d, Txy2d_bounds⟩
  · grind
  · grind
  progress as ⟨Z2, h_Z2,  Z2_bounds⟩
  progress as ⟨PPMM, h_PPMM,  PPMM_bounds⟩
  · grind
  · grind
  progress as ⟨fe, h_fe,  fe_bounds⟩
  · grind
  · grind
  have hzz: ∀ i < 5, Z2[i]!.val < 2 ^ 54 := by simp_all
  obtain ⟨fe2, h_fe2_ok, h_fe2, fe2_bounds⟩ := CompletedPoint.add_spec' hzz  Txy2d_bounds
  simp only [h_fe2_ok, bind_tc_ok]
  progress as ⟨fe3, h_fe3, fe3_bounds⟩
  · grind
  · grind
  constructor
  · rw[← Nat.ModEq]
    rw[← Nat.ModEq] at PPMM_bounds
    have :  Field51_as_Nat self.Y + Field51_as_Nat self.X =Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ ]
      simp_all
      scalar_tac
    rw[this]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.y_minus_x) h_Y_minus_X
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat PPMM) this)
    rw[add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply  Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm h_PP)
    apply Nat.ModEq.trans (Nat.ModEq.symm PPMM_bounds)
    apply Nat.ModEq.add_left
    exact h_MM
  constructor
  · rw[← Nat.ModEq]
    have :  Field51_as_Nat fe = Field51_as_Nat PP + Field51_as_Nat MM := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this]
    have := Nat.ModEq.add h_PP h_MM
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.y_minus_x) this
    apply Nat.ModEq.trans this
    have :  Field51_as_Nat self.Y + Field51_as_Nat self.X =Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ ]
      simp_all
      scalar_tac
    rw[this, add_assoc]
    apply Nat.ModEq.add_left
    rw[← add_mul]
    apply Nat.ModEq.mul_right
    rw[← Nat.ModEq] at h_Y_minus_X
    exact h_Y_minus_X
  constructor
  · rw[← Nat.ModEq]
    have :  Field51_as_Nat fe2 = Field51_as_Nat Z2 + Field51_as_Nat Txy2d := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this]
    have :  Field51_as_Nat Z2 = Field51_as_Nat self.Z + Field51_as_Nat self.Z := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    simp[this, (by scalar_tac :∀ a, a + a = 2 * a)]
    apply Nat.ModEq.add_left _ h_Txy2d
  · rw[← Nat.ModEq]
    rw[← Nat.ModEq] at fe3_bounds
    have :=  Nat.ModEq.add_left  (Field51_as_Nat fe3) h_Txy2d
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe3_bounds
    apply Nat.ModEq.trans this
    have :  Field51_as_Nat Z2 = Field51_as_Nat self.Z + Field51_as_Nat self.Z := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this, (by scalar_tac :∀ a, a + a = 2 * a)]

end curve25519_dalek.backend.serial.curve_models.AddShared0EdwardsPointSharedAAffineNielsPointCompletedPoint
