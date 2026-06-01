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

/-!
# Spec theorem for `curve25519_dalek::edwards::affine::AffinePoint::to_edwards`

Converts an affine Edwards point with coordinates `(x, y)` to extended twisted Edwards
coordinates `(X, Y, Z, T)` by setting

  `X = x`,  `Y = y`,  `Z = 1`,  `T = x · y (mod p)`,

where `p = 2^255 - 19`. This lifts the affine representation of the point to the
extended projective representation used internally by the Edwards group law.

Source: "curve25519-dalek/src/edwards/affine.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- Local helper: weakened spec for `ONE` with `2^53` limb bounds, suitable for
feeding into the `to_edwards` proof. -/
@[step]
private theorem ONE_bounds_spec :
    ONE ⦃ (result : FieldElement51) =>
      Field51_as_Nat result = 1 ∧
      ∀ i < 5, result[i]!.val < 2 ^ 53 ⦄ := by
  unfold ONE from_limbs
  simp only [spec_ok]
  decide

namespace curve25519_dalek.edwards.affine.AffinePoint

/-- **Spec theorem for `curve25519_dalek::edwards::affine::AffinePoint::to_edwards`**
• No panic when `self` is a valid AffinePoint and its limbs are < 2^53
• `result.X = self.x` (direct Rust copy of the affine `x` coordinate)
• `result.Y = self.y` (direct Rust copy of the affine `y` coordinate)
• The resulting EdwardsPoint is valid: `result.IsValid`
• Math bridge: `result.toPoint = self.toPoint` (same curve point in `Point Ed25519`)
-/
@[step]
theorem to_edwards_spec (self : AffinePoint) (hself : self.IsValid)
    (hx53 : ∀ i < 5, self.x[i]!.val < 2 ^ 53)
    (hy53 : ∀ i < 5, self.y[i]!.val < 2 ^ 53) :
    to_edwards self ⦃ (result : EdwardsPoint) =>
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
    unfold toField; rw [hZ_val]; exact Nat.cast_one
  have hT_F : T.toField = self.x.toField * self.y.toField := by
    unfold toField
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
  unfold toPoint
  rw [dif_pos hself]
  ext
  · simp [hpx, hZ_F]
  · simp [hpy, hZ_F]

end curve25519_dalek.edwards.affine.AffinePoint
