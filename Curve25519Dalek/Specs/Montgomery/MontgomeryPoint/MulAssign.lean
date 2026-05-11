/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.Mul

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_assign`

Computes the scalar multiplication `[s]P` on the Montgomery curve in-place, where `s` is a
`Scalar` and `P` is a `MontgomeryPoint` (u-coordinate only). The implementation delegates to
the `MontgomeryPoint * Scalar` routine, which uses the Montgomery ladder on the u-coordinate.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_assign`**
• The function always succeeds (no panic)
• The result satisfies `MontgomeryPoint.mkPoint result = m • MontgomeryPoint.mkPoint self`,
  where `m = (U8x32_as_Nat scalar.bytes) % 2^255`
-/
@[step]
theorem mul_assign_spec (self : MontgomeryPoint) (scalar : scalar.Scalar)
    (hself_bound : U8x32_as_Nat self < 2 ^ 255) :
    mul_assign self scalar ⦃ (result : MontgomeryPoint) =>
      let m := (U8x32_as_Nat scalar.bytes) % 2^255
      MontgomeryPoint.mkPoint result = m • (MontgomeryPoint.mkPoint self) ⦄ := by
  unfold mul_assign
  step*

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar
