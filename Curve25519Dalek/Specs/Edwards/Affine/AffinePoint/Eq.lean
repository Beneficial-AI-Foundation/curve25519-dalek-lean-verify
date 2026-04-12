/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.Affine.AffinePoint.CtEq
/-! # Spec Theorem for `AffinePoint::eq`

Specification and proof for the `eq` (PartialEq) trait implementation for affine Edwards points.

This function performs equality comparison for two affine Edwards points by delegating
to constant-time equality (`ct_eq`) and converting the resulting `Choice` to `Bool`.
Two affine Edwards points (x₁, y₁) and (x₂, y₂) are considered equal when their
coordinates are equal modulo p, i.e., x₁ ≡ x₂ (mod p) and y₁ ≡ y₂ (mod p).

**Source**: curve25519-dalek/src/edwards/affine.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpPartialEqAffinePoint



/-- If `c.val = 1`, then `c = Choice.one` (by proof irrelevance on the `valid` field). -/
@[simp]
theorem Choice.eq_one (c : subtle.Choice) : c.val = 1#u8 → c = Choice.one := by
  intro h; cases c; simp_all [Choice.one]

/-- If `c.val = 0`, then `c = Choice.zero` (by proof irrelevance on the `valid` field). -/
@[simp]
theorem Choice.eq_zero (c : subtle.Choice) : c.val = 0#u8 → c = Choice.zero := by
  intro h; cases c; simp_all [Choice.zero]
/-
natural language description:

• Takes two AffinePoints `self` and `other`
• Returns `true` if they represent the same point, `false` otherwise
• Implementation: delegates to `ct_eq` (constant-time equality) which compares
  the x-coordinates and y-coordinates element-wise, then converts the `Choice` to `Bool`

natural language specs:

• The function always succeeds (no panic) for valid input affine Edwards points
• The result is `true` if and only if the two points represent the same point on the curve
-/

/-- **Spec and proof concerning `edwards.affine.PartialEqAffinePoint.eq`**:
• The function always succeeds (no panic) for valid inputs
• The result is `true` if and only if the two points represent the same point on the curve
-/
@[step]
theorem eq_spec (self other : AffinePoint) (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    eq self other ⦃ result =>
    result = true ↔ self.toPoint = other.toPoint ⦄ := by
  unfold eq
  step*
  · unfold Bool.Insts.CoreConvertFromChoice.from
    simp only [spec_ok, decide_eq_true_eq]
    have : c = Choice.one ↔ c.val = 1#u8 := by
      constructor
      · intro h
        rw[h, Choice.one]
      · apply Choice.eq_one
    rw[← this]
    exact c_post2 h_self_valid h_other_valid

end curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpPartialEqAffinePoint
