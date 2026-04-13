/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
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

    When the input is a valid AffinePoint with limbs satisfying the tighter < 2^53 bound:
      - Structurally, X = self.x and Y = self.y (direct Rust copies)
      - The resulting EdwardsPoint is valid (IsValid)
      - The conversion preserves the represented mathematical point:
        result.toPoint = self.toPoint in `Point Ed25519`
-/

@[step]
private lemma ONE_bounds_spec :
    ONE ⦃ result => Field51_as_Nat result = 1 ∧ ∀ i < 5, result[i]!.val < 2 ^ 53 ⦄ := by
  unfold ONE from_limbs
  simp only [spec_ok]
  decide

/-- **Spec and proof concerning `edwards.affine.AffinePoint.to_edwards`**:
- No panic when `self` is a valid AffinePoint and its limbs are < 2^53
- Structural: `result.X = self.x` and `result.Y = self.y` (direct Rust copies)
- The resulting EdwardsPoint is valid: `result.IsValid`
- Math bridge: `result.toPoint = self.toPoint` (same curve point in `Point Ed25519`)
-/
@[step]
theorem to_edwards_spec (self : AffinePoint) (hself : self.IsValid)
  (hx53 : ∀ i < 5, self.x[i]!.val < 2 ^ 53)
  (hy53 : ∀ i < 5, self.y[i]!.val < 2 ^ 53) :
    to_edwards self ⦃ result =>
      result.X = self.x ∧
      result.Y = self.y ∧
      result.IsValid ∧
      result.toPoint = self.toPoint ⦄ := by
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
  have hres_valid : ({ X := self.x, Y := self.y, Z := Z, T := T } : EdwardsPoint).IsValid := {
    X_bounds := hx53
    Y_bounds := hy53
    Z_bounds := hZ_bounds
    T_bounds := fun i hi => by dsimp only; have := hT_bounds i hi; omega
    Z_ne_zero := by rw [hZ_F]; exact one_ne_zero
    T_relation := by rw [hT_F, hZ_F, mul_one]
    on_curve := by dsimp only; rw [hZ_F]; simp only [one_pow, mul_one]; exact hself.on_curve
  }
  refine ⟨hres_valid, ?_⟩
  have ⟨hpx, hpy⟩ := EdwardsPoint.toPoint_of_isValid hres_valid
  unfold AffinePoint.toPoint
  rw [dif_pos hself]
  ext
  · simp [hpx, hZ_F]
  · simp [hpy, hZ_F]

end curve25519_dalek.edwards.affine.AffinePoint
