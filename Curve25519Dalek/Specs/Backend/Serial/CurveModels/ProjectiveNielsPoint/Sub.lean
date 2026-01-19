/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add



/-! # Spec Theorem for `CompletedPoint::sub`

Specification and proof for `CompletedPoint::sub`.

This function implements the mixed subtraction of a ProjectiveNielsPoint from an
Edwards point in extended coordinates, returning the result in completed
coordinates (ℙ¹ × ℙ¹). Given
- an EdwardsPoint P = (X:Y:Z:T) in extended ℙ³ coordinates (with X/Z = x, Y/Z = y, and T = XY/Z),
- a ProjectiveNielsPoint N = (Y+X, Y−X, Z, 2dXY),
it computes a CompletedPoint C = (X':Y':Z':T') corresponding to P − N.

The concrete formulas are:
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PM        = Y_plus_X  · N.Y_minus_X
- MP        = Y_minus_X · N.Y_plus_X
- TT2d      = T · N.T2d
- ZZ        = Z · N.Z
- ZZ2       = ZZ + ZZ
- X'        = PM − MP
- Y'        = PM + MP
- Z'        = ZZ2 − TT2d
- T'        = ZZ2 + TT2d

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/
open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.curve_models.SubShared0EdwardsPointSharedAProjectiveNielsPointCompletedPoint
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint




/-
natural language description:

• Takes an EdwardsPoint (X, Y, Z, T) in extended coordinates and a ProjectiveNielsPoint
(Y+X, Y−X, Z, 2dXY) and returns a CompletedPoint (X', Y', Z', T') in completed coordinates
(ℙ¹ × ℙ¹), representing the group subtraction P − N. Arithmetic is performed in the
field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given inputs P = (X, Y, Z, T) and N = (Y+X, Y−X, Z, 2dXY), the output C = (X', Y', Z', T')
  satisfies modulo p:
  - X' ≡ ( (Y+X)·N.Y_minus_X − (Y−X)·N.Y_plus_X ) (mod p)
  - Y' ≡ ( (Y+X)·N.Y_minus_X + (Y−X)·N.Y_plus_X ) (mod p)
  - Z' ≡ ( 2·Z·N.Z − T·N.T2d ) (mod p)
  - T' ≡ ( 2·Z·N.Z + T·N.T2d ) (mod p)
-/

set_option maxHeartbeats 1000000 in
-- simp_all is heavy


@[progress]
theorem sub_spec
  (self : edwards.EdwardsPoint)
  (other : backend.serial.curve_models.ProjectiveNielsPoint)
  (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
  (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
  (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
  (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
  (h_otherYpX_bounds : ∀ i, i < 5 → (other.Y_plus_X[i]!).val < 2 ^ 53)
  (h_otherYmX_bounds : ∀ i, i < 5 → (other.Y_minus_X[i]!).val < 2 ^ 53)
  (h_otherZ_bounds : ∀ i, i < 5 → (other.Z[i]!).val < 2 ^ 53)
  (h_otherT2d_bounds : ∀ i, i < 5 → (other.T2d[i]!).val < 2 ^ 53) :
∃ c, sub self other = ok c ∧
let X := Field51_as_Nat self.X
let Y := Field51_as_Nat self.Y
let Z := Field51_as_Nat self.Z
let T := Field51_as_Nat self.T
let YpX := Field51_as_Nat other.Y_plus_X
let YmX := Field51_as_Nat other.Y_minus_X
let Z₀ := Field51_as_Nat other.Z
let T2d := Field51_as_Nat other.T2d
let X' := Field51_as_Nat c.X
let Y' := Field51_as_Nat c.Y
let Z' := Field51_as_Nat c.Z
let T' := Field51_as_Nat c.T
(X' + Y * YpX) % p = (((Y + X) * YmX) + X * YpX) % p ∧
(Y' + X * YpX) % p = (((Y + X) * YmX) + Y  * YpX) % p ∧
(Z' + (T * T2d) )% p = (2 * Z * Z₀)  % p ∧
T' % p = ((2 * Z * Z₀) + (T * T2d)) % p
:= by
  unfold sub
  progress as ⟨Y_plus_X , h_Y_plus_X, Y_plus_X_bounds ⟩
  progress as ⟨Y_minus_X,   Y_minus_X_bounds, h_Y_minus_X⟩
  · intro i hi
    apply lt_trans (h_selfY_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_selfX_bounds i hi)
    simp
  progress  as ⟨ PM , h_PM , PM_bounds⟩
  · intro i hi
    apply lt_trans (h_otherYmX_bounds  i hi)
    simp
  progress  as ⟨ MP, h_MP, MP_bounds⟩
  · intro i hi
    apply lt_trans (Y_minus_X_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_otherYpX_bounds i hi)
    simp
  progress  as ⟨ TT2d, h_TT2d, TT2d_bounds⟩
  · intro i hi
    apply lt_trans (h_selfT_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_otherT2d_bounds i hi)
    simp
  progress  as ⟨ ZZ, h_ZZ, ZZ_bounds⟩
  · intro i hi
    apply lt_trans (h_selfZ_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (h_otherZ_bounds i hi)
    simp
  progress as ⟨ZZ2, h_ZZ2,  ZZ2_bounds⟩
  · intro i hi
    apply lt_trans (ZZ_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (ZZ_bounds i hi)
    simp
  progress as ⟨fe, h_fe,  fe_bounds⟩
  · intro i hi
    apply lt_trans (PM_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (MP_bounds i hi)
    simp
  progress as ⟨fe1, h_fe1,  fe1_bounds⟩
  · intro i hi
    apply lt_trans (PM_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (MP_bounds i hi)
    simp
  have hzz: ∀ i < 5, ZZ2[i]!.val < 2 ^ 54 := by simp_all
  obtain ⟨fe2, h_fe2_ok, h_fe2, fe2_bounds⟩ := CompletedPoint.add_spec' hzz  TT2d_bounds
  simp only [h_fe2_ok, bind_tc_ok]
  progress as ⟨fe3, h_fe3, fe3_bounds⟩
  · intro i hi
    apply lt_trans (ZZ2_bounds i hi)
    simp
  · intro i hi
    apply lt_trans (TT2d_bounds i hi)
    simp
  constructor
  · rw[← Nat.ModEq]
    rw[← Nat.ModEq] at fe_bounds
    have :  Field51_as_Nat self.Y + Field51_as_Nat self.X =Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ ]
      simp_all
      scalar_tac
    rw[this]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.Y_plus_X) h_Y_minus_X
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat fe) this)
    rw[add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply  Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm h_PM)
    apply Nat.ModEq.trans (Nat.ModEq.symm fe_bounds)
    apply Nat.ModEq.add_left
    exact h_MP
  constructor
  · rw[← Nat.ModEq]
    have :  Field51_as_Nat fe1 = Field51_as_Nat PM + Field51_as_Nat MP := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this]
    have := Nat.ModEq.add h_PM h_MP
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.Y_plus_X) this
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
    rw[← Nat.ModEq] at fe3_bounds
    have :=  Nat.ModEq.add_left  (Field51_as_Nat fe3) h_TT2d
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe3_bounds
    apply Nat.ModEq.trans this
    have :  Field51_as_Nat ZZ2 = Field51_as_Nat ZZ + Field51_as_Nat ZZ := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this, (by scalar_tac :∀ a, a + a = 2 * a)]
    have := Nat.ModEq.mul_left 2 h_ZZ
    rw[mul_assoc]
    exact this
  · rw[← Nat.ModEq]
    have :  Field51_as_Nat fe2 = Field51_as_Nat ZZ2 + Field51_as_Nat TT2d := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    rw[this]
    have :  Field51_as_Nat ZZ2 = Field51_as_Nat ZZ + Field51_as_Nat ZZ := by
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp_all
      scalar_tac
    simp[this, (by scalar_tac :∀ a, a + a = 2 * a)]
    have := Nat.ModEq.mul_left 2 h_ZZ
    have :=  Nat.ModEq.add_right (Field51_as_Nat TT2d) this
    apply Nat.ModEq.trans this
    rw[mul_assoc]
    apply Nat.ModEq.add_left
    exact h_TT2d

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
