/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.Affine.AffinePoint.CtEq

/-!
# Spec theorem for `curve25519_dalek::edwards::affine::AffinePoint::eq`

Equality comparison for two affine Edwards points.

• Takes two `AffinePoint`s `self` and `other`.
• Returns `true` if they represent the same point, `false` otherwise.
• Implementation: delegates to `ct_eq` (constant-time equality), which compares
  the x- and y-coordinates element-wise, then converts the resulting `Choice` to `Bool`.

Two affine Edwards points (x₁, y₁) and (x₂, y₂) are considered equal when their
coordinates are equal modulo p, i.e., x₁ ≡ x₂ (mod p) and y₁ ≡ y₂ (mod p).

Source: "curve25519-dalek/src/edwards/affine.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpPartialEqAffinePoint

/-- **Spec theorem for `curve25519_dalek::edwards::affine::AffinePoint::eq`**
• The function always succeeds (no panic) for valid input affine Edwards points
• The result is `true` if and only if the two points represent the same point on the curve
-/
@[step]
theorem eq_spec (self other : AffinePoint) (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    eq self other ⦃ (result : Bool) =>
      result = true ↔ self.toPoint = other.toPoint ⦄ := by
  unfold eq
  step*
  · unfold Bool.Insts.CoreConvertFromChoice.from
    simp only [spec_ok, decide_eq_true_eq]
    rw [Choice.val_eq_one_iff]
    exact c_post2 h_self_valid h_other_valid

end curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpPartialEqAffinePoint
