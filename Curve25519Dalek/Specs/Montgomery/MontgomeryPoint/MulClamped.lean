/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.Mul
import Curve25519Dalek.Specs.Scalar.ClampInteger

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_clamped`

This function clamps a 32-byte input to a scalar and performs Montgomery
scalar multiplication of the given point by the clamped scalar.

• Clamps the 32-byte input to a valid scalar using `scalar.clamp_integer`.
• Multiplies the MontgomeryPoint by the clamped scalar via
  `montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul`.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_clamped`**
• The function always succeeds (no panic) when `U8x32_as_Nat P < 2^255`
• The result satisfies `MontgomeryPoint.mkPoint result = m • (MontgomeryPoint.mkPoint P)`
  where `m = U8x32_as_Nat (clampBytes bytes)` is the input bytes clamped as in
  RFC 7748 §5 (`h ∣ m` and `2^254 ≤ m < 2^255`, see `ClampInteger.lean`)
-/
@[step]
theorem mul_clamped_spec (P : MontgomeryPoint) (bytes : Array U8 32#usize)
    (hP_bound : U8x32_as_Nat P < 2 ^ 255) :
    mul_clamped P bytes ⦃ (result : MontgomeryPoint) =>
      MontgomeryPoint.mkPoint result =
        U8x32_as_Nat (clampBytes bytes) • MontgomeryPoint.mkPoint P ⦄ := by
  unfold mul_clamped
  step*
  subst a_post
  rwa [Nat.mod_eq_of_lt (U8x32_as_Nat_clampBytes_lt bytes)] at result_post

end curve25519_dalek.montgomery.MontgomeryPoint
