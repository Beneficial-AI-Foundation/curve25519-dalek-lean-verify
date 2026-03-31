/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
/-! # Spec Theorem for `AffinePoint::to_edwards`

Specification and proof for `edwards.affine.AffinePoint.to_edwards`.

This function converts an affine Edwards point (x, y) to extended twisted Edwards
coordinates (X, Y, Z, T) = (x, y, 1, x·y), lifting from affine to projective representation.

**Source**: curve25519-dalek/src/edwards/affine.rs, lines 60:4-67:5

-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.affine.AffinePoint
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    Converts an affine Edwards point with coordinates (x, y) to extended twisted
    Edwards coordinates (X, Y, Z, T) by setting:
      X = x, Y = y, Z = 1, T = x * y (mod p)
    where p = 2^255 - 19.

natural language specs:

    When the function succeeds (no panic when input limbs < 2^54):
      - The X and Y coordinates are exactly the input x and y
      - The Z coordinate is the field element 1 (Field51_as_Nat Z = 1)
      - The T coordinate satisfies T ≡ x · y (mod p)
      - T limbs are bounded by 2^52, Z limbs by 2^53
      - If the input AffinePoint is valid and its coordinate limbs are < 2^53,
        the resulting EdwardsPoint is valid (IsValid) and represents the same
        mathematical curve point: result.toPoint = self.toPoint
-/

@[step]
private lemma ONE_bounds_spec :
    ONE ⦃ result => Field51_as_Nat result = 1 ∧ ∀ i < 5, result[i]!.val < 2 ^ 53 ⦄ := by
  unfold ONE from_limbs
  simp only [spec_ok]
  decide

/-- **Spec and proof concerning `edwards.affine.AffinePoint.to_edwards`**:
- No panic when the input AffinePoint is valid (coordinate limbs < 2^54)
- The resulting EdwardsPoint has X = self.x, Y = self.y
- Z has field value 1, T ≡ x · y (mod p)
- T limbs < 2^52, Z limbs < 2^53
- If coordinate limbs are < 2^53, the resulting EdwardsPoint is valid (IsValid)
-/
@[step]
theorem to_edwards_spec (self : AffinePoint) (hself : self.IsValid)
    (hx53 : ∀ i < 5, self.x[i]!.val < 2 ^ 53)
    (hy53 : ∀ i < 5, self.y[i]!.val < 2 ^ 53) :
    to_edwards self ⦃ result =>
      result.X = self.x ∧ result.Y = self.y ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T % p = (Field51_as_Nat self.x * Field51_as_Nat self.y) % p ∧
      (∀ i < 5, result.T[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, result.Z[i]!.val < 2 ^ 53) ∧
      result.IsValid ⦄ := by
  unfold to_edwards
  have hx : ∀ i < 5, self.x[i]!.val < 2 ^ 54 := hself.x_valid
  have hy : ∀ i < 5, self.y[i]!.val < 2 ^ 54 := hself.y_valid
  step as ⟨T, hT_mod, hT_bounds⟩
  step as ⟨Z, hZ_val, hZ_bounds⟩
  have hZ_F : Z.toField = 1 := by
    unfold FieldElement51.toField; rw [hZ_val]; exact Nat.cast_one
  have hT_F : T.toField = self.x.toField * self.y.toField := by
    unfold FieldElement51.toField
    have h := Edwards.lift_mod_eq _ _ hT_mod
    push_cast at h; exact h
  refine ⟨hZ_val, hT_mod, hT_bounds, hZ_bounds, ?_⟩
  exact {
    X_bounds := hx53
    Y_bounds := hy53
    Z_bounds := hZ_bounds
    T_bounds := fun i hi => by dsimp only; have := hT_bounds i hi; omega
    Z_ne_zero := by rw [hZ_F]; exact one_ne_zero
    T_relation := by rw [hT_F, hZ_F, mul_one]
    on_curve := by dsimp only; rw [hZ_F]; simp only [one_pow, mul_one]; exact hself.on_curve
  }

end curve25519_dalek.edwards.affine.AffinePoint
