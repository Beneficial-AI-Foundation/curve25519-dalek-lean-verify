/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjectiveNiels
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Sub
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
/-!
# Spec theorem for `EdwardsPoint::sub`

Specification and proof for the `Sub` trait implementation for Edwards points.

This function subtracts two Edwards points via elliptic curve subtraction using the
extended twisted Edwards coordinates: it converts the second operand to projective niels
form, performs the subtraction in completed point coordinates, and converts back to
extended coordinates.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint

/-
natural language description:

• Takes two EdwardsPoints `self` and `other`
• Returns their difference as an EdwardsPoint via elliptic curve group subtraction
• Implementation: converts `other` to projective niels form, performs subtraction
  in completed point coordinates, and converts the result back to extended coordinates

natural language specs:

• The function always succeeds (no panic) for valid input Edwards points
• The result is a valid Edwards point
• The result represents the difference of the inputs (in the context of elliptic curve subtraction)
-/

/-- **Spec and proof concerning `Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint.sub`**:
• The function always succeeds (no panic) for valid inputs
• The result is a valid Edwards point
• The result represents the difference of the inputs (in the context of elliptic curve subtraction)
-/
@[step, externally_verified]
-- proven in Verus
theorem sub_spec
    (self other : edwards.EdwardsPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    sub self other ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint - other.toPoint ⦄ := by
  unfold sub
  step*

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint
