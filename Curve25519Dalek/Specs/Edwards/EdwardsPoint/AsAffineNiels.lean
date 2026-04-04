/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EdwardsD2
import Curve25519Dalek.Aux

/-! # Spec Theorem for `EdwardsPoint::as_affine_niels`

Specification and proof for `EdwardsPoint::as_affine_niels`.

This function converts an EdwardsPoint from extended twisted Edwards
coordinates (X, Y, Z, T) to an AffineNielsPoint (y_plus_x, y_minus_x, xy2d)
by first dehomogenizing (dividing by Z) to obtain the affine coordinates,
and then computing the affine Niels representation optimized for mixed addition.

Given an EdwardsPoint P = (X:Y:Z:T) in extended ℙ³ coordinates
(with X/Z = x, Y/Z = y, and T = XY/Z), it computes an
AffineNielsPoint N = (y_plus_x, y_minus_x, xy2d) corresponding to the
same curve point in affine Niels form.

The concrete formulas are:
- recip      = Z⁻¹
- x          = X · recip
- y          = Y · recip
- y_plus_x   = y + x
- y_minus_x  = y − x
- xy2d       = x · y · 2d

**Source**: curve25519-dalek/src/edwards.rs, lines 543:4-553:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64.field.FieldElement51
  curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.backend.serial.curve_models.AffineNielsPoint
open curve25519_dalek.montgomery
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint (X, Y, Z, T) in extended coordinates and computes
  an AffineNielsPoint (y_plus_x, y_minus_x, xy2d) representing the same
  curve point in affine Niels form. Arithmetic is performed in the
  field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given input P = (X, Y, Z, T) with Z ≢ 0 (mod p), the output
  N = (y_plus_x, y_minus_x, xy2d) satisfies modulo p:
  - y_plus_x · Z ≡ Y + X (mod p)
  - y_minus_x · Z + X ≡ Y (mod p)
  - xy2d · Z² ≡ X · Y · (2 · d) (mod p)
• Output bounds:
  - y_plus_x: all limbs < 2^54
  - y_minus_x: all limbs < 2^52
  - xy2d: all limbs < 2^52
-/

-- ========================================================================
-- Helper lemma: bridge from toField ≠ 0 to Field51_as_Nat % p ≠ 0
-- ========================================================================

private lemma field51_modP_ne_zero_of_toField_ne_zero
    (fe : backend.serial.u64.field.FieldElement51)
    (h : fe.toField ≠ 0) :
    Field51_as_Nat fe % p ≠ 0 := by
  intro hmod
  apply h
  unfold curve25519_dalek.backend.serial.u64.field.FieldElement51.toField
  exact Edwards.lift_mod_eq (Field51_as_Nat fe) 0 (by simpa [Nat.zero_mod] using hmod)

-- ========================================================================
-- Helper lemmas for modular arithmetic reasoning
-- ========================================================================

/-- y_plus_x modular arithmetic: `(y + x) * Z ≡ Y + X` from
    `y * Z ≡ Y` and `x * Z ≡ X`. -/
private lemma ypx_mod_arith (ypx_nat y_nat x_nat Z_nat X_nat Y_nat : ℕ)
    (h_ypx : ypx_nat = y_nat + x_nat)
    (h_yZ : y_nat * Z_nat ≡ Y_nat [MOD p])
    (h_xZ : x_nat * Z_nat ≡ X_nat [MOD p]) :
    ypx_nat * Z_nat ≡ Y_nat + X_nat [MOD p] := by
  rw [h_ypx, add_mul]
  exact Nat.ModEq.add h_yZ h_xZ

/-- y_minus_x modular arithmetic: `ymx * Z + X ≡ Y` from
    `(ymx + x) ≡ y`, `x * Z ≡ X`, and `y * Z ≡ Y`. -/
private lemma ymx_mod_arith (ymx_nat x_nat y_nat Z_nat X_nat Y_nat : ℕ)
    (h_ymx : ymx_nat + x_nat ≡ y_nat [MOD p])
    (h_xZ : x_nat * Z_nat ≡ X_nat [MOD p])
    (h_yZ : y_nat * Z_nat ≡ Y_nat [MOD p]) :
    ymx_nat * Z_nat + X_nat ≡ Y_nat [MOD p] := by
  have h_sum_Z := Nat.ModEq.mul_right Z_nat h_ymx
  rw [add_mul] at h_sum_Z
  calc ymx_nat * Z_nat + X_nat
      ≡ ymx_nat * Z_nat + x_nat * Z_nat [MOD p] :=
        Nat.ModEq.add_left _ (Nat.ModEq.symm h_xZ)
    _ ≡ y_nat * Z_nat [MOD p] := h_sum_Z
    _ ≡ Y_nat [MOD p] := h_yZ

/-- xy2d modular arithmetic: `xy2d * Z * Z ≡ X * Y * (2 * d)` from
    `xy2d ≡ x * y * (2 * d)`, `x * Z ≡ X`, and `y * Z ≡ Y`. -/
private lemma xy2d_mod_arith (xy2d_nat fe_nat d2_nat x_nat y_nat Z_nat X_nat Y_nat : ℕ)
    (h_xy2d : xy2d_nat ≡ fe_nat * d2_nat [MOD p])
    (h_fe : fe_nat ≡ x_nat * y_nat [MOD p])
    (h_d2 : d2_nat ≡ 2 * d [MOD p])
    (h_xZ : x_nat * Z_nat ≡ X_nat [MOD p])
    (h_yZ : y_nat * Z_nat ≡ Y_nat [MOD p]) :
    xy2d_nat * Z_nat * Z_nat ≡ X_nat * Y_nat * (2 * d) [MOD p] := by
  have h_step1 : xy2d_nat ≡ x_nat * y_nat * (2 * d) [MOD p] := by
    calc xy2d_nat
        ≡ fe_nat * d2_nat [MOD p] := h_xy2d
      _ ≡ (x_nat * y_nat) * d2_nat [MOD p] := Nat.ModEq.mul_right _ h_fe
      _ ≡ (x_nat * y_nat) * (2 * d) [MOD p] := Nat.ModEq.mul_left _ h_d2
  calc xy2d_nat * Z_nat * Z_nat
      ≡ x_nat * y_nat * (2 * d) * Z_nat * Z_nat [MOD p] :=
        Nat.ModEq.mul_right _ (Nat.ModEq.mul_right _ h_step1)
    _ = (x_nat * Z_nat) * (y_nat * Z_nat) * (2 * d) := by ring
    _ ≡ X_nat * Y_nat * (2 * d) [MOD p] :=
        Nat.ModEq.mul_right _ (Nat.ModEq.mul h_xZ h_yZ)

-- ========================================================================
-- Main spec theorem
-- ========================================================================


/-- **Spec and proof concerning `edwards.EdwardsPoint.as_affine_niels`**:
- No panic (always returns successfully)
- Given input:
  • an EdwardsPoint `self` satisfying `self.IsValid`
    (coordinates X, Y, Z, T with limbs < 2^53, Z ≠ 0 in the field,
    extended coordinate relation XY = TZ, and the curve equation),
the output AffineNielsPoint (y_plus_x, y_minus_x, xy2d) computed by
`as_affine_niels self` satisfies modulo p:
- y_plus_x · Z ≡ Y + X (mod p)
- y_minus_x · Z + X ≡ Y (mod p)
- xy2d · Z² ≡ X · Y · (2 · d) (mod p)
where p = 2^255 - 19.

These are the standard affine Niels conversion formulas obtained by dehomogenizing
the extended coordinates and computing y ± x and 2dxy.

Output bounds (from field element arithmetic):
- y_plus_x: all limbs < 2^54
- y_minus_x: all limbs < 2^52
- xy2d: all limbs < 2^52
-/
@[step]
theorem as_affine_niels_spec
  (self : EdwardsPoint)
  (hself : self.IsValid) :
  as_affine_niels self ⦃ an =>
  let X := Field51_as_Nat self.X
  let Y := Field51_as_Nat self.Y
  let Z := Field51_as_Nat self.Z
  let ypx := Field51_as_Nat an.y_plus_x
  let ymx := Field51_as_Nat an.y_minus_x
  let xy2d_val := Field51_as_Nat an.xy2d
  (ypx * Z) % p = (Y + X) % p ∧
  (ymx * Z + X) % p = Y % p ∧
  (xy2d_val * Z * Z) % p = (X * Y * (2 * d)) % p ∧
  (∀ i < 5, an.y_plus_x[i]!.val < 2 ^ 54) ∧
  (∀ i < 5, an.y_minus_x[i]!.val < 2 ^ 52) ∧
  (∀ i < 5, an.xy2d[i]!.val < 2 ^ 52) ⦄
:= by
  have h_X_bounds := hself.X_bounds
  have h_Y_bounds := hself.Y_bounds
  have h_Z_bounds := hself.Z_bounds
  have h_Z_nonzero : Field51_as_Nat self.Z % p ≠ 0 :=
    field51_modP_ne_zero_of_toField_ne_zero self.Z hself.Z_ne_zero
  unfold as_affine_niels
  step*
  · have h_recip_Z : Field51_as_Nat recip * Field51_as_Nat self.Z ≡ 1 [MOD p] := by
      rw [Nat.ModEq, Nat.mul_mod, show (1 : ℕ) % p = 1 from by decide]
      exact recip_post1 h_Z_nonzero
    have h_xZ : Field51_as_Nat x * Field51_as_Nat self.Z ≡ Field51_as_Nat self.X [MOD p] := by
      calc Field51_as_Nat x * Field51_as_Nat self.Z
          ≡ Field51_as_Nat self.X * Field51_as_Nat recip * Field51_as_Nat self.Z [MOD p] :=
            Nat.ModEq.mul_right _ x_post1
        _ = Field51_as_Nat self.X * (Field51_as_Nat recip * Field51_as_Nat self.Z) := by ring
        _ ≡ Field51_as_Nat self.X * 1 [MOD p] := Nat.ModEq.mul_left _ h_recip_Z
        _ = Field51_as_Nat self.X := by ring
    have h_yZ : Field51_as_Nat y * Field51_as_Nat self.Z ≡ Field51_as_Nat self.Y [MOD p] := by
      calc Field51_as_Nat y * Field51_as_Nat self.Z
          ≡ Field51_as_Nat self.Y * Field51_as_Nat recip * Field51_as_Nat self.Z [MOD p] :=
            Nat.ModEq.mul_right _ y_post1
        _ = Field51_as_Nat self.Y * (Field51_as_Nat recip * Field51_as_Nat self.Z) := by ring
        _ ≡ Field51_as_Nat self.Y * 1 [MOD p] := Nat.ModEq.mul_left _ h_recip_Z
        _ = Field51_as_Nat self.Y := by ring
    have h_ypx_val : Field51_as_Nat fe2 = Field51_as_Nat y + Field51_as_Nat x :=
      pointwise_add_Field51_as_Nat y x fe2 fe2_post1
    have h_d2_mod : Field51_as_Nat fe1 ≡ 2 * d [MOD p] := by
      rw [Nat.ModEq, fe1_post1, Nat.mod_mod_of_dvd]; simp
    exact ⟨
      (ypx_mod_arith _ _ _ _ _ _ h_ypx_val h_yZ h_xZ),
      (ymx_mod_arith _ _ _ _ _ _ fe3_post2 h_xZ h_yZ),
      (xy2d_mod_arith _ _ _ _ _ _ _ _ xy2d_post1 fe_post1 h_d2_mod h_xZ h_yZ),
      fe2_post2, fe3_post1, xy2d_post2⟩

end curve25519_dalek.edwards.EdwardsPoint
