/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.Affine.AffinePoint.Identity

/-!
# Spec theorem for `curve25519_dalek::edwards::affine::AffinePoint::default`

Returns the default value for an `AffinePoint`, which is `AffinePoint::identity()`,
i.e. the neutral element `(0, 1)` of the Ed25519 group law.

Source: "curve25519-dalek/src/edwards/affine.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreDefaultDefault

/-- **Spec theorem for `curve25519_dalek::edwards::affine::AffinePoint::default`**
• The function always succeeds (no panic)
• The x-coordinate of the result is `0`
• The y-coordinate of the result is `1`
• The resulting `AffinePoint` is valid
• The result represents the identity element of the Ed25519 group
-/
@[step]
theorem default_spec :
    default ⦃ (q : AffinePoint) =>
      Field51_as_Nat q.x = 0 ∧
      Field51_as_Nat q.y = 1 ∧
      q.IsValid ∧
      q.toPoint = 0 ⦄ := by
  unfold default
  step*

end curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreDefaultDefault
