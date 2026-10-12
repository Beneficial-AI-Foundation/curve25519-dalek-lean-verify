/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Basepoint
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulBase
import Curve25519Dalek.Specs.Scalar.ClampInteger

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_base_clamped`

Performs scalar multiplication by the Edwards basepoint after clamping the
32-byte input to a valid scalar via `scalar.clamp_integer`. The computation
of the basepoint multiplication with the clamped scalar is delegated to
`EdwardsPoint.mul_base`.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.edwards curve25519_dalek.backend.serial.u64
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_base_clamped`**
• The function always succeeds (no panic)
• The returned `EdwardsPoint` is a valid Edwards point
• The returned point equals the scalar multiplication of the Edwards basepoint
  by `U8x32_as_Nat (clampBytes bytes)`, the input bytes clamped as in RFC 7748 §5
  (divisible by the cofactor `h` and in `[2^254, 2^255)`, see `ClampInteger.lean`)
-/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (result : EdwardsPoint) =>
      EdwardsPoint.IsValid result ∧
      result.toPoint = U8x32_as_Nat (clampBytes bytes) • _root_.Edwards.basepoint ⦄ := by
  unfold mul_base_clamped
  have := U8x32_as_Nat_clampBytes_lt bytes
  step*

end curve25519_dalek.edwards.EdwardsPoint
