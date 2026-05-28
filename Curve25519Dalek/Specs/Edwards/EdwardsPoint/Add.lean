/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjectiveNiels
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::add`

Add two Edwards points via elliptic curve group addition, returning their sum as an
EdwardsPoint.

- The core implementation (`&EdwardsPoint + &EdwardsPoint`) takes two EdwardsPoints by
  reference, converts the right-hand operand to projective niels form, performs the
  addition in completed point coordinates, and converts the result back to extended
  twisted Edwards coordinates (Section 3.1 in
  https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf).
- The by-value wrapper (`EdwardsPoint + EdwardsPoint`) takes its operands by value and
  delegates to the core `&EdwardsPoint + &EdwardsPoint` addition.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::add`**
• The function always succeeds (no panic) for valid inputs
• The result is a valid Edwards point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/
@[step]
theorem add_spec
    (self other : edwards.EdwardsPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    add self other ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint + other.toPoint ⦄ := by
  unfold add
  step*

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint

namespace curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddEdwardsPointEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::add`**
• The function always succeeds (no panic) for valid inputs
• The result is a valid Edwards point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/
@[step]
theorem add_spec
    (self other : EdwardsPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    add self other ⦃ (result : EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint + other.toPoint ⦄ := by
  unfold add
  step*

end curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddEdwardsPointEdwardsPoint
