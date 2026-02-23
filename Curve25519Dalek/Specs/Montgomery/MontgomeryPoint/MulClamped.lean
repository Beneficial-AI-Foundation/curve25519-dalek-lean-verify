/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.Mul
import Curve25519Dalek.Specs.Scalar.ClampInteger
/-! # Spec Theorem for `MontgomeryPoint::mul_clamped`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::MontgomeryPoint}::mul_clamped`.

This function clamps a 32-byte input to a scalar and performs Montgomery
scalar multiplication of the given point by the clamped scalar.

**Source**: curve25519-dalek/src/montgomery.rs, lines 134:4-146:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

• Clamps the 32-byte input to a valid scalar using `scalar.clamp_integer`.

• Multiplies the MontgomeryPoint by the clamped scalar via
  `montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul`.

natural language specs:

• The function always succeeds (no panic)
• The result is the Montgomery scalar multiplication by the clamped scalar
-/

/-- **Spec and proof concerning `montgomery.MontgomeryPoint.mul_clamped`**:
- No panic (always returns successfully)
- Clamps input bytes with `scalar.clamp_integer`
- Delegates to `montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul`
- The returned MontgomeryPoint matches the clamped scalar multiplication result
-/
@[progress]
theorem mul_clamped_spec (P : MontgomeryPoint) (bytes : Array U8 32#usize) :
    mul_clamped P bytes ⦃ res =>
    (∃ clamped_scalar,
    h ∣ U8x32_as_Nat clamped_scalar ∧
    U8x32_as_Nat clamped_scalar < 2 ^ 255 ∧
    2 ^ 254 ≤ U8x32_as_Nat clamped_scalar ∧
    MontgomeryPoint.toPoint res = (U8x32_as_Nat clamped_scalar) • (MontgomeryPoint.toPoint P)) ⦄ := by
      unfold mul_clamped
      progress*
      exact ⟨a, a_post_1, a_post_2, a_post_3, res_post⟩

end curve25519_dalek.montgomery.MontgomeryPoint
