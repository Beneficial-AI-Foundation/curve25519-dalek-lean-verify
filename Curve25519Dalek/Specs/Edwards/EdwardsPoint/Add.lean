/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjectiveNiels
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
/-! # Spec Theorems for `EdwardsPoint::add`

Specification and proof for the `add` trait implementations for Edwards points.

These functions add two Edwards points via elliptic curve addition using the
extended twisted Edwards coordinates and the unified addition formulas.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
/-! ## Core addition: `&EdwardsPoint + &EdwardsPoint` -/

namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint

/-
natural language description:

• Takes two EdwardsPoints `self` and `other` (by reference)
• Returns their sum as an EdwardsPoint via elliptic curve group addition
• Implementation: converts `other` to projective niels form, performs addition
  in completed point coordinates, and converts the result back to extended coordinates
  (Section 3.1 in https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf)

natural language specs:

• The function always succeeds (no panic) for valid input Edwards points
• The result is a valid Edwards point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/

/-- **Spec and proof** concerning:
`Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint.add`:
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

/-! ## Wrapper: `EdwardsPoint + EdwardsPoint` -/

namespace curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddEdwardsPointEdwardsPoint

/-
natural language description:

• Takes two EdwardsPoints `self` and `other`
• Returns their sum as an EdwardsPoint via elliptic curve group addition
• Implementation: delegates to the core `&EdwardsPoint + &EdwardsPoint` addition

natural language specs:

• The function always succeeds (no panic) for valid input Edwards points
• The result is a valid Edwards point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/

/-- **Spec and proof concerning `edwards.AddEdwardsPointEdwardsPointEdwardsPoint.add`**:
• The function always succeeds (no panic) for valid inputs
• The result is a valid Edwards point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/
@[step]
theorem add_spec (self other : EdwardsPoint)
    (h_self_valid : self.IsValid) (h_other_valid : other.IsValid) :
    add self other ⦃ result =>
      result.IsValid ∧
      result.toPoint = self.toPoint + other.toPoint ⦄ := by
  unfold add
  step*

end curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddEdwardsPointEdwardsPoint
