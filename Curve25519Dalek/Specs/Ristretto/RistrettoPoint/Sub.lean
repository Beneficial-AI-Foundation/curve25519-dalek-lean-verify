/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation

/-! # Spec Theorem for `RistrettoPoint::sub`

Specification and proof for the `Sub` trait implementation for Ristretto points.

This function subtracts two Ristretto points via elliptic curve subtraction by delegating
to the underlying Edwards point subtraction.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint

/-
natural language description:

• Takes two RistrettoPoints `self` and `other`
• Returns their difference as a RistrettoPoint via elliptic curve group subtraction
• Implementation: unwraps both points to their underlying EdwardsPoint representations,
  performs Edwards subtraction, and wraps the result back as a RistrettoPoint

natural language specs:

• The function always succeeds (no panic) for valid input Ristretto points
• The result is a valid Ristretto point
• The result represents the difference of the inputs (in the context of elliptic curve subtraction)
-/

/-- **Spec and proof concerning `Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint.sub`**:
• The function always succeeds (no panic) for valid inputs
• The result is a valid Ristretto point
• The result represents the difference of the inputs (in the context of elliptic curve subtraction)
-/
@[progress]
theorem sub_spec (self other : RistrettoPoint) (h_self_valid : self.IsValid) (h_other_valid : other.IsValid) :
    sub self other ⦃ result =>
    result.IsValid ∧
    result.toPoint = self.toPoint - other.toPoint ⦄ := by
  sorry

end curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint
