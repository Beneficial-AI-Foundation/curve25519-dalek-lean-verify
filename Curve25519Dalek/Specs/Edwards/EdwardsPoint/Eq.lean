/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::eq`

Performs equality comparison between two `EdwardsPoint` values:

• Takes two `EdwardsPoint`s `self` and `other`.
• Returns `true` if they represent the same point on the curve, `false` otherwise.
• Implementation: delegates to constant-time equality (`ct_eq`), which cross-multiplies
  coordinates (X₁·Z₂ vs X₂·Z₁ and Y₁·Z₂ vs Y₂·Z₁), then converts the resulting
  `Choice` to `Bool`.

Two extended Edwards points (X₁:Y₁:Z₁:T₁) and (X₂:Y₂:Z₂:T₂) are considered equal
when they represent the same affine point, i.e., X₁·Z₂ = X₂·Z₁ and Y₁·Z₂ = Y₂·Z₁ (mod p).

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek

/-- If `c.val = 1`, then `c = Choice.one` (by proof irrelevance on the `valid` field). -/
@[simp]
theorem Choice.eq_one (c : subtle.Choice) : c.val = 1#u8 → c = Choice.one := by
  intro h; cases c; simp_all only [Choice.one]

end curve25519_dalek

namespace curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCmpPartialEqEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::eq`**
• The function always succeeds (no panic) for valid inputs
• The result is `true` if and only if the two points represent the same point on the curve
-/
@[step]
theorem eq_spec (self other : EdwardsPoint)
    (h_self_valid : self.IsValid) (h_other_valid : other.IsValid) :
    eq self other ⦃ (result : Bool) =>
      result = true ↔ self.toPoint = other.toPoint ⦄ := by
  unfold eq
  step*
  · have := h_self_valid.X_bounds
    grind
  · have := h_self_valid.Y_bounds
    grind
  · have := h_self_valid.Z_bounds
    grind
  · have := h_other_valid.X_bounds
    grind
  · have := h_other_valid.Y_bounds
    grind
  · have := h_other_valid.Z_bounds
    grind
  · unfold Bool.Insts.CoreConvertFromChoice.from
    simp only [spec_ok, decide_eq_true_eq]
    have : c = Choice.one ↔ c.val = 1#u8 := by
      constructor
      · intro h
        rw [h, Choice.one]
      · apply Choice.eq_one
    rw [← this]
    exact c_post2 h_self_valid h_other_valid

end curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCmpPartialEqEdwardsPoint
