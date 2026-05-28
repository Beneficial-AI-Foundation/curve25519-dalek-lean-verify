/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulByPow2
import Curve25519Dalek.Math.Edwards.Representation

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_by_cofactor`

Takes an `EdwardsPoint` `e` and returns the result of multiplying the point by the cofactor
`8 = 2 ^ 3` (i.e., computes `[8]e` where `e` is the input point).

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_by_cofactor`**
• The function always succeeds (no panic) for valid input `EdwardsPoint`s
• Returns a valid `EdwardsPoint`
• `result.toPoint` equals `8 • self.toPoint` (i.e. `[8]e`, multiplication by the cofactor)
-/
@[step]
theorem mul_by_cofactor_spec (self : EdwardsPoint) (hself : self.IsValid) :
    mul_by_cofactor self ⦃ (result : EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = h • self.toPoint ⦄ := by
  unfold mul_by_cofactor
  step as ⟨result, hvalid, hpoint⟩
  refine ⟨hvalid, ?_⟩
  simp_all [h]

end curve25519_dalek.edwards.EdwardsPoint
