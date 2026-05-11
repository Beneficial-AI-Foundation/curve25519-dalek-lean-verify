/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Mul
import Curve25519Dalek.Specs.Scalar.ClampInteger

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_clamped`

Performs scalar multiplication of an Edwards point after clamping the 32-byte input
to a valid scalar via `curve25519_dalek::scalar::clamp_integer`, then delegating to
the scalar–point multiplication `<Scalar as Mul<EdwardsPoint>>::mul`. The clamped
scalar is not necessarily reduced modulo the group order `L`, but clamping forces
it to be divisible by the cofactor `h = 8` and to lie in `[2^254, 2^255)`, which
suffices for correctness of variable-base scalar multiplication.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.edwards curve25519_dalek.backend.serial.u64
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_clamped`**
• The function always succeeds (no panic) for a valid input EdwardsPoint `self`
• The result is a valid EdwardsPoint
• There exists a clamped 32-byte scalar `c` (the bitwise-clamped form of `bytes`)
  such that `c` is divisible by the cofactor `h = 8`
• `c < 2^255`
• `2^254 ≤ c`
• `result.toPoint = c • self.toPoint`, i.e., scalar multiplication of `self.toPoint`
  by the natural number `c`
-/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint) (bytes : Array U8 32#usize)
    (h_self_valid : self.IsValid) :
    mul_clamped self bytes ⦃ (result : EdwardsPoint) =>
      result.IsValid ∧
      (∃ clamped_scalar,
        h ∣ U8x32_as_Nat clamped_scalar ∧
        U8x32_as_Nat clamped_scalar < 2 ^ 255 ∧
        2 ^ 254 ≤ U8x32_as_Nat clamped_scalar ∧
        result.toPoint = (U8x32_as_Nat clamped_scalar) • self.toPoint) ⦄ := by
  unfold mul_clamped
  step*

end curve25519_dalek.edwards.EdwardsPoint
