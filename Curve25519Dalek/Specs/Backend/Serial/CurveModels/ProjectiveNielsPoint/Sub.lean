/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
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
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.u64.field
open Edwards
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.edwards

set_option maxHeartbeats 1000000 in
/-- Auxiliary spec for sub proving arithmetic correctness and output bounds.
Input bounds: EdwardsPoint coords < 2^53, ProjectiveNielsPoint (IsValid') bounds. -/
theorem sub_spec_aux_54_52_53_52
    (self : edwards.EdwardsPoint)
    (other : backend.serial.curve_models.ProjectiveNielsPoint)
    (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
    (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
    (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
    (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
    (h_otherYpX_bounds : ∀ i, i < 5 → (other.Y_plus_X[i]!).val < 2 ^ 54)
    (h_otherYmX_bounds : ∀ i, i < 5 → (other.Y_minus_X[i]!).val < 2 ^ 52)
    (h_otherZ_bounds : ∀ i, i < 5 → (other.Z[i]!).val < 2 ^ 53)
    (h_otherT2d_bounds : ∀ i, i < 5 → (other.T2d[i]!).val < 2 ^ 52) :
    sub self other ⦃ c =>
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
    (Y' + X * YpX) % p = (((Y + X) * YmX) + Y * YpX) % p ∧
    (Z' + (T * T2d)) % p = (2 * Z * Z₀) % p ∧
    T' % p = ((2 * Z * Z₀) + (T * T2d)) % p ∧
    -- Output bounds (all < 2^54)
    (∀ i < 5, c.X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 54) ⦄ := by
  unfold sub
  progress as ⟨Y_plus_X, h_Y_plus_X, Y_plus_X_bounds⟩
  progress as ⟨Y_minus_X, Y_minus_X_bounds, h_Y_minus_X⟩
  progress as ⟨PM, h_PM, PM_bounds⟩
  progress as ⟨MP, h_MP, MP_bounds⟩
  progress as ⟨TT2d, h_TT2d, TT2d_bounds⟩
  progress as ⟨ZZ, h_ZZ, ZZ_bounds⟩
  progress as ⟨ZZ2, h_ZZ2, ZZ2_bounds⟩
  progress as ⟨fe, h_fe, fe_bounds⟩
  -- fe1 = PM + MP: use tighter add spec (< 2^52) + (< 2^52) → < 2^53
  obtain ⟨fe1, h_fe1_ok, h_fe1, fe1_bounds⟩ := CompletedPoint.add_spec_52_52 PM_bounds MP_bounds
  simp only [h_fe1_ok, bind_tc_ok]
  -- fe2 = ZZ2 - TT2d: sub operation
  progress as ⟨fe2, h_fe2, fe2_bounds⟩
  -- fe3 = ZZ2 + TT2d: use tighter add spec (< 2^53) + (< 2^52) → < 2^54
  have hzz2_tight : ∀ i < 5, ZZ2[i]!.val < 2 ^ 53 := by
    intro i hi
    have h1 : ZZ2[i]!.val = ZZ[i]!.val + ZZ[i]!.val := h_ZZ2 i hi
    have h2 : ZZ[i]!.val < 2 ^ 52 := ZZ_bounds i hi
    calc ZZ2[i]!.val = ZZ[i]!.val + ZZ[i]!.val := h1
        _ < 2 ^ 52 + 2 ^ 52 := by omega
        _ = 2 ^ 53 := by norm_num
  obtain ⟨fe3, h_fe3_ok, h_fe3, fe3_bounds⟩ := CompletedPoint.add_spec_53_52 hzz2_tight TT2d_bounds
  simp only [h_fe3_ok, bind_tc_ok]
  -- Arithmetic proofs
  constructor
  · -- X relation: (X' + Y * YpX) % p = (((Y + X) * YmX) + X * YpX) % p
    rw [← Nat.ModEq]
    rw [← Nat.ModEq] at fe_bounds
    have : Field51_as_Nat self.Y + Field51_as_Nat self.X = Field51_as_Nat Y_plus_X := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow,
        Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      scalar_tac
    rw [this]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.Y_plus_X) h_Y_minus_X
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat fe) this)
    rw [add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm h_PM)
    apply Nat.ModEq.trans (Nat.ModEq.symm fe_bounds)
    apply Nat.ModEq.add_left
    exact h_MP
  constructor
  · -- Y relation: (Y' + X * YpX) % p = (((Y + X) * YmX) + Y * YpX) % p
    rw [← Nat.ModEq]
    have : Field51_as_Nat fe1 = Field51_as_Nat PM + Field51_as_Nat MP := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow,
        Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      scalar_tac
    rw [this]
    have := Nat.ModEq.add h_PM h_MP
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.Y_plus_X) this
    apply Nat.ModEq.trans this
    have : Field51_as_Nat self.Y + Field51_as_Nat self.X = Field51_as_Nat Y_plus_X := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow,
        Nat.ModEq.add_iff_left, Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      scalar_tac
    rw [this, add_assoc]
    apply Nat.ModEq.add_left
    rw [← add_mul]
    apply Nat.ModEq.mul_right
    rw [← Nat.ModEq] at h_Y_minus_X
    exact h_Y_minus_X
  constructor
  · -- Z relation: (Z' + (T * T2d)) % p = (2 * Z * Z₀) % p
    rw [← Nat.ModEq]
    rw [← Nat.ModEq] at fe2_bounds
    have := Nat.ModEq.add_left (Field51_as_Nat fe2) h_TT2d
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe2_bounds
    apply Nat.ModEq.trans this
    have : Field51_as_Nat ZZ2 = Field51_as_Nat ZZ + Field51_as_Nat ZZ := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow,
        Nat.ModEq.add_iff_right, Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      scalar_tac
    rw [this, (by scalar_tac : ∀ a, a + a = 2 * a)]
    have := Nat.ModEq.mul_left 2 h_ZZ
    rw [mul_assoc]
    exact this
  constructor
  · -- T relation: T' % p = ((2 * Z * Z₀) + (T * T2d)) % p
    rw [← Nat.ModEq]
    have : Field51_as_Nat fe3 = Field51_as_Nat ZZ2 + Field51_as_Nat TT2d := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow,
        Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      scalar_tac
    rw [this]
    have : Field51_as_Nat ZZ2 = Field51_as_Nat ZZ + Field51_as_Nat ZZ := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, Nat.reducePow,
        Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      scalar_tac
    simp [this, (by scalar_tac : ∀ a, a + a = 2 * a)]
    have := Nat.ModEq.mul_left 2 h_ZZ
    have := Nat.ModEq.add_right (Field51_as_Nat TT2d) this
    apply Nat.ModEq.trans this
    rw [mul_assoc]
    apply Nat.ModEq.add_left
    exact h_TT2d
  -- Output bounds (all < 2^54)
  constructor
  · -- X bounds: fe from sub gives < 2^52 < 2^54
    intro i hi
    apply lt_trans (h_fe i hi)
    norm_num
  constructor
  · -- Y bounds: fe1 from add_spec_52_52 gives < 2^53 < 2^54
    intro i hi
    apply lt_trans (fe1_bounds i hi)
    norm_num
  constructor
  · -- Z bounds: fe2 from sub gives < 2^52 < 2^54
    intro i hi
    apply lt_trans (h_fe2 i hi)
    norm_num
  · -- T bounds: fe3 from add_spec_53_52 gives < 2^54
    exact fe3_bounds


theorem sub_spec_bounds'
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid') :
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
    (Y' + X * YpX) % p = (((Y + X) * YmX) + Y * YpX) % p ∧
    (Z' + (T * T2d)) % p = (2 * Z * Z₀) % p ∧
    T' % p = ((2 * Z * Z₀) + (T * T2d)) % p ∧
    -- Output bounds (all < 2^54)
    (∀ i < 5, c.X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 54) := by
  exact spec_imp_exists (sub_spec_aux_54_52_53_52 self other
    hself.X_bounds hself.Y_bounds hself.Z_bounds hself.T_bounds
    hother.Y_plus_X_bounds hother.Y_minus_X_bounds hother.Z_bounds hother.T2d_bounds)


set_option maxHeartbeats 1000000000 in
@[progress]
theorem sub_spec'
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid') :
    Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint.sub self other ⦃ c =>
    c.IsValid ∧ c.toPoint = self.toPoint - other.toPointI ⦄ := by
  obtain ⟨c, hc_run, hX_arith, hY_arith, hZ_arith, hT_arith, hcX_bounds, hcY_bounds, hcZ_bounds, hcT_bounds⟩ :=
    sub_spec_bounds' self hself other hother
  simp [spec]
  apply exists_imp_spec
  use c, hc_run

  -- Lift arithmetic to field equalities
  have hX_F : c.X.toField + self.Y.toField * other.Y_plus_X.toField =
      (self.Y.toField + self.X.toField) * other.Y_minus_X.toField +
      self.X.toField * other.Y_plus_X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hX_arith
    push_cast at h
    exact h

  have hY_F : c.Y.toField + self.X.toField * other.Y_plus_X.toField =
      (self.Y.toField + self.X.toField) * other.Y_minus_X.toField +
      self.Y.toField * other.Y_plus_X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hY_arith
    push_cast at h
    exact h

  have hZ_F : c.Z.toField + self.T.toField * other.T2d.toField =
      2 * self.Z.toField * other.Z.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hZ_arith
    push_cast at h
    exact h

  have hT_F : c.T.toField = 2 * self.Z.toField * other.Z.toField +
      self.T.toField * other.T2d.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hT_arith
    push_cast at h
    exact h

  -- Simplify to get direct expressions
  have hX_F' : c.X.toField = (self.Y.toField + self.X.toField) * other.Y_minus_X.toField -
      (self.Y.toField - self.X.toField) * other.Y_plus_X.toField := by
    have := hX_F; linear_combination this

  have hY_F' : c.Y.toField = (self.Y.toField + self.X.toField) * other.Y_minus_X.toField +
      (self.Y.toField - self.X.toField) * other.Y_plus_X.toField := by
    have := hY_F; linear_combination this

  have hZ_F' : c.Z.toField = 2 * self.Z.toField * other.Z.toField -
      self.T.toField * other.T2d.toField := by
    have := hZ_F; linear_combination this

  -- Setup self's affine coordinates
  set X1 := self.X.toField with hX1_def
  set Y1 := self.Y.toField with hY1_def
  set Z1 := self.Z.toField with hZ1_def
  set T1 := self.T.toField with hT1_def

  have hZ1_ne : Z1 ≠ 0 := hself.Z_ne_zero
  have hZ1_2 : Z1^2 ≠ 0 := pow_ne_zero 2 hZ1_ne
  have hZ1_4 : Z1^4 ≠ 0 := pow_ne_zero 4 hZ1_ne

  have h_self_curve : Ed25519.a * X1^2 * Z1^2 + Y1^2 * Z1^2 = Z1^4 + Ed25519.d * X1^2 * Y1^2 :=
    hself.on_curve
  have h_self_T : X1 * Y1 = T1 * Z1 := hself.T_relation

  set x1 := X1 / Z1 with hx1_def
  set y1 := Y1 / Z1 with hy1_def

  have h_P1_on_curve : Ed25519.a * x1^2 + y1^2 = 1 + Ed25519.d * x1^2 * y1^2 := by
    simp only [Ed25519] at h_self_curve ⊢
    simp only [hx1_def, hy1_def, div_pow]
    field_simp [hZ1_2, hZ1_4]
    linear_combination h_self_curve

  let P1 : Point Ed25519 := ⟨x1, y1, h_P1_on_curve⟩

  -- Setup other's affine coordinates from ProjectiveNielsPoint
  set YpX := other.Y_plus_X.toField with hYpX_def
  set YmX := other.Y_minus_X.toField with hYmX_def
  set Z2 := other.Z.toField with hZ2_def
  set T2d := other.T2d.toField with hT2d_def

  have hZ2_ne : Z2 ≠ 0 := hother.Z_ne_zero
  have h2 : (2 : Edwards.CurveField) ≠ 0 := by decide
  have h2Z2_ne : 2 * Z2 ≠ 0 := mul_ne_zero h2 hZ2_ne
  have h2Z2_2 : (2 * Z2)^2 ≠ 0 := pow_ne_zero 2 h2Z2_ne
  have h2Z2_4 : (2 * Z2)^4 ≠ 0 := pow_ne_zero 4 h2Z2_ne

  set x2 := (YpX - YmX) / (2 * Z2) with hx2_def
  set y2 := (YpX + YmX) / (2 * Z2) with hy2_def

  have h_P2_on_curve : Ed25519.a * x2^2 + y2^2 = 1 + Ed25519.d * x2^2 * y2^2 := by
    have h_other_curve := hother.on_curve
    simp only [Ed25519] at h_other_curve ⊢
    simp only [hx2_def, hy2_def, div_pow]
    field_simp [h2Z2_2, h2Z2_4]
    ring_nf; ring_nf at h_other_curve
    linear_combination h_other_curve

  let P2 : Point Ed25519 := ⟨x2, y2, h_P2_on_curve⟩

  -- Use completeness theorem for denominators
  have h_denoms := Ed25519.denomsNeZero P1 P2
  have h_denom_plus : 1 + Ed25519.d * x1 * x2 * y1 * y2 ≠ 0 := by
    have h := h_denoms.1
    simp only [P1, P2] at h
    convert h using 1

  have h_denom_minus : 1 - Ed25519.d * x1 * x2 * y1 * y2 ≠ 0 := by
    have h := h_denoms.2
    simp only [P1, P2] at h
    convert h using 1

  -- Bounds are already < 2^54 from sub_spec_aux, which satisfies IsValid
  have hcX_valid : c.X.IsValid := hcX_bounds
  have hcY_valid : c.Y.IsValid := hcY_bounds
  have hcZ_valid : c.Z.IsValid := hcZ_bounds
  have hcT_valid : c.T.IsValid := hcT_bounds

  -- Use T2d_relation to express T1*T2d in terms of affine coordinates
  have h_T2d_rel := hother.T2d_relation

  have h_YpX_YmX : YpX^2 - YmX^2 = (YpX - YmX) * (YpX + YmX) := by ring
  have h_factor_x2y2 : (YpX - YmX) * (YpX + YmX) = 4 * Z2^2 * x2 * y2 := by
    simp only [hx2_def, hy2_def]
    field_simp [h2Z2_ne]
    ring

  have h_T2d_expr : T2d = 2 * Ed25519.d * Z2 * x2 * y2 := by
    have h_rel : 2 * Z2 * T2d = Ed25519.d * (YpX^2 - YmX^2) := h_T2d_rel
    rw [h_YpX_YmX, h_factor_x2y2] at h_rel
    have h_simpl : T2d * (2 * Z2) = 2 * Ed25519.d * Z2 * x2 * y2 * (2 * Z2) := by
      linear_combination h_rel
    field_simp [hZ2_ne, h2] at h_simpl
    calc T2d = 2 * Z2 * Ed25519.d * x2 * y2 := h_simpl
      _ = 2 * Ed25519.d * Z2 * x2 * y2 := by ring

  have h_T1_expr : T1 = x1 * y1 * Z1 := by
    simp only [hx1_def, hy1_def]
    field_simp [hZ1_ne]
    linear_combination -h_self_T

  have h_T1_T2d : T1 * T2d = 2 * Ed25519.d * x1 * x2 * y1 * y2 * Z1 * Z2 := by
    rw [h_T1_expr, h_T2d_expr]
    ring

  -- For sub: Z' = 2*Z1*Z2*(1 - d*x1*x2*y1*y2) and T' = 2*Z1*Z2*(1 + d*x1*x2*y1*y2)
  have hZ_factored : c.Z.toField = 2 * Z1 * Z2 * (1 - Ed25519.d * x1 * x2 * y1 * y2) := by
    rw [hZ_F']
    simp only [hZ1_def, hZ2_def, hT1_def, hT2d_def]
    rw [h_T1_T2d]
    ring

  have hT_factored : c.T.toField = 2 * Z1 * Z2 * (1 + Ed25519.d * x1 * x2 * y1 * y2) := by
    rw [hT_F]
    simp only [hZ1_def, hZ2_def, hT1_def, hT2d_def]
    rw [h_T1_T2d]
    ring

  -- Prove Z' ≠ 0 and T' ≠ 0 using completeness
  -- NOTE: swapped vs add! Z' uses denom_minus, T' uses denom_plus
  have hcZ_ne : c.Z.toField ≠ 0 := by
    rw [hZ_factored]
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · exact h2
    · exact hZ1_ne
    · exact hZ2_ne
    · exact h_denom_minus

  have hcT_ne : c.T.toField ≠ 0 := by
    rw [hT_factored]
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · exact h2
    · exact hZ1_ne
    · exact hZ2_ne
    · exact h_denom_plus

  -- Derive factored forms for c.X and c.Y
  have hYpX' : YpX = Z2 * (x2 + y2) := by
    simp only [hx2_def, hy2_def]; field_simp [h2Z2_ne]; ring
  have hYmX' : YmX = Z2 * (y2 - x2) := by
    simp only [hx2_def, hy2_def]; field_simp [h2Z2_ne]; ring
  have hX1' : X1 = Z1 * x1 := by simp only [hx1_def]; field_simp [hZ1_ne]
  have hY1' : Y1 = Z1 * y1 := by simp only [hy1_def]; field_simp [hZ1_ne]

  -- For sub: X' = 2*Z1*Z2*(x1*y2 - y1*x2), Y' = 2*Z1*Z2*(y1*y2 - x1*x2)
  have hX_factored : c.X.toField = 2 * Z1 * Z2 * (x1 * y2 - y1 * x2) := by
    rw [hX_F', hYpX', hYmX', hX1', hY1']; ring

  have hY_factored : c.Y.toField = 2 * Z1 * Z2 * (y1 * y2 - x1 * x2) := by
    rw [hY_F', hYpX', hYmX', hX1', hY1']; ring

  -- On-curve proof: P1 + (-P2) is on Ed25519
  have h_c_on_curve : Ed25519.a * c.X.toField^2 * c.T.toField^2 +
      c.Y.toField^2 * c.Z.toField^2 =
      c.Z.toField^2 * c.T.toField^2 + Ed25519.d * c.X.toField^2 * c.Y.toField^2 := by
    have h_diff_on_curve := (P1 + (-P2)).on_curve
    -- (P1 + (-P2)).x and .y
    have h_diff_x : (P1 + (-P2)).x = (x1 * y2 - y1 * x2) / (1 - Ed25519.d * x1 * x2 * y1 * y2) := by
      rw [add_x]; simp only [P1, P2, neg_x, neg_y]
      congr 1 <;> ring
    have h_diff_y : (P1 + (-P2)).y = (y1 * y2 - x1 * x2) / (1 + Ed25519.d * x1 * x2 * y1 * y2) := by
      rw [add_y];
      have :=Edwards.neg_x P2
      rw[this]
      have :=Edwards.neg_y P2
      rw[this]
      simp only [P1, P2, Ed25519]
      ring_nf

    -- c.X/c.Z = (P1+(-P2)).x and c.Y/c.T = (P1+(-P2)).y
    have h_cx_eq : c.X.toField / c.Z.toField = (P1 + (-P2)).x := by
      rw [hX_factored, hZ_factored, h_diff_x]
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_minus]
    have h_cy_eq : c.Y.toField / c.T.toField = (P1 + (-P2)).y := by
      rw [hY_factored, hT_factored, h_diff_y]
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_plus]
    -- Clear denominators from the affine curve equation
    have hcZ2 : c.Z.toField^2 ≠ 0 := pow_ne_zero 2 hcZ_ne
    have hcT2 : c.T.toField^2 ≠ 0 := pow_ne_zero 2 hcT_ne
    simp only [Ed25519] at h_diff_on_curve ⊢
    have h_key : (Ed25519.a * (P1 + (-P2)).x^2 + (P1 + (-P2)).y^2) =
        (1 + Ed25519.d * (P1 + (-P2)).x^2 * (P1 + (-P2)).y^2) := by
      simp only [Ed25519]
      exact h_diff_on_curve
    calc Ed25519.a * c.X.toField^2 * c.T.toField^2 + c.Y.toField^2 * c.Z.toField^2
        = (Ed25519.a * (c.X.toField / c.Z.toField)^2 + (c.Y.toField / c.T.toField)^2) *
            c.Z.toField^2 * c.T.toField^2 := by field_simp [hcZ2, hcT2]
      _ = (Ed25519.a * (P1 + (-P2)).x^2 + (P1 + (-P2)).y^2) * c.Z.toField^2 * c.T.toField^2 := by
            rw [h_cx_eq, h_cy_eq]
      _ = (1 + Ed25519.d * (P1 + (-P2)).x^2 * (P1 + (-P2)).y^2) * c.Z.toField^2 * c.T.toField^2 := by
            rw [h_key]
      _ = c.Z.toField^2 * c.T.toField^2 + Ed25519.d * c.X.toField^2 * c.Y.toField^2 := by
            rw [← h_cx_eq, ← h_cy_eq]
            simp only [div_pow]
            field_simp [hcZ2, hcT2]

  constructor
  · exact {
      X_valid := hcX_valid
      Y_valid := hcY_valid
      Z_valid := hcZ_valid
      T_valid := hcT_valid
      Z_ne_zero := hcZ_ne
      T_ne_zero := hcT_ne
      on_curve := h_c_on_curve
    }

  · have h_c_valid : c.IsValid := {
      X_valid := hcX_valid
      Y_valid := hcY_valid
      Z_valid := hcZ_valid
      T_valid := hcT_valid
      Z_ne_zero := hcZ_ne
      T_ne_zero := hcT_ne
      on_curve := h_c_on_curve
    }

    have ⟨h_cx, h_cy⟩ := CompletedPoint.toPoint_of_isValid h_c_valid
    have ⟨h_selfx, h_selfy⟩ := EdwardsPoint.toPoint_of_isValid hself
    have ⟨h_otherx, h_othery⟩ := ProjectiveNielsPoint.toPoint_of_isValid' hother

    -- Relate self.toPoint to x1, y1
    have h_self_x : self.toPoint.x = x1 := by simp only [h_selfx, hx1_def, hX1_def, hZ1_def]
    have h_self_y : self.toPoint.y = y1 := by simp only [h_selfy, hy1_def, hY1_def, hZ1_def]

    -- Relate other.toPointI to x2, y2
    have h_other_x : other.toPointI.x = x2 := by simp only [h_otherx, hx2_def, hYpX_def, hYmX_def, hZ2_def]
    have h_other_y : other.toPointI.y = y2 := by simp only [h_othery, hy2_def, hYpX_def, hYmX_def, hZ2_def]

    ext
    · -- x coordinate: X'/Z' = (P1 - P2).x = (P1 + (-P2)).x
      rw [h_cx, hX_factored, hZ_factored]
      simp only [sub_eq_add_neg]
      rw [add_x]
      simp only [neg_x, neg_y, h_self_x, h_self_y, h_other_x, h_other_y]
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_minus]
    · -- y coordinate: Y'/T' = (P1 - P2).y = (P1 + (-P2)).y
      rw [h_cy, hY_factored, hT_factored]
      simp only [sub_eq_add_neg]
      rw [add_y]
      have :=Edwards.neg_x other.toPointI
      rw[this]
      have :=Edwards.neg_y other.toPointI
      rw[this]
      simp only [h_self_x, h_self_y, h_other_x, h_other_y, Ed25519]
      field_simp [h2, hZ1_ne, hZ2_ne, h_denom_plus]
      ring_nf

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint
