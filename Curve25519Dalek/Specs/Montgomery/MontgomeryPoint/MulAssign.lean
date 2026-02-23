/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.Mul


/-! # Spec Theorem for `MontgomeryPoint::mul_assign`

Specification and proof for
`curve25519_dalek::montgomery::{core::ops::arith::MulAssign<&0 (curve25519_dalek::scalar::Scalar)> for curve25519_dalek::montgomery::MontgomeryPoint}::mul_assign`.

This function implements in-place scalar multiplication of a MontgomeryPoint by
delegating to the MontgomeryPoint * Scalar implementation (the Montgomery ladder
in the backend).

**Source**: curve25519-dalek/src/montgomery.rs, lines 454:4-456:5


-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar

/-
natural language description:

• Computes the scalar multiplication [s]P on the Montgomery curve, where s is a Scalar
  and P is a MontgomeryPoint (u-coordinate only), and returns the updated point.

• The implementation simply calls the MontgomeryPoint * Scalar routine, which uses the
  Montgomery ladder on the u-coordinate.

natural language specs:

• The function always succeeds (no panic)
• The result is exactly the output of `MontgomeryPoint * Scalar` for the given point
  and scalar
-/

/-- **Spec and proof concerning `montgomery.MulAssignMontgomeryPointShared0Scalar.mul_assign`**:
- No panic (always returns successfully)
- Delegates to `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`
- The returned MontgomeryPoint equals the Montgomery ladder result for the given scalar and point
-/
@[progress]
theorem mul_assign_spec (P : MontgomeryPoint) (scalar : scalar.Scalar) :
    mul_assign P scalar ⦃ res =>
    MontgomeryPoint.toPoint res = (U8x32_as_Nat scalar.bytes) • (MontgomeryPoint.toPoint P) ⦄
     := by
  unfold mul_assign
  progress*

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar
