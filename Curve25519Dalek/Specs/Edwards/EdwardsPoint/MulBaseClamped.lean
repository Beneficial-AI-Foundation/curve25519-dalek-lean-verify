/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulBase
import Curve25519Dalek.Specs.Scalar.ClampInteger

/-! # Spec Theorem for `EdwardsPoint::mul_base_clamped`

Specification and proof for
`curve25519_dalek::edwards::{curve25519_dalek::edwards::EdwardsPoint}::mul_base_clamped`.

This function performs scalar multiplication by the Edwards basepoint after
clamping the input bytes to a valid scalar, delegating to `EdwardsPoint.mul_base`.

**Source**: curve25519-dalek/src/edwards.rs, lines 906:4-914:5

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.edwards
open curve25519_dalek.backend.serial.u64

namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Clamps the 32-byte input to a valid scalar using `scalar.clamp_integer`.

• Computes the Edwards basepoint multiplication with the clamped scalar by
  delegating to `EdwardsPoint.mul_base`.

natural language specs:

• The function always succeeds (no panic)
• The result is the Edwards basepoint multiplication of the clamped scalar
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.mul_base_clamped`**:
- No panic (always returns successfully)
- Clamps input bytes with `scalar.clamp_integer`
- Delegates to `edwards.EdwardsPoint.mul_base` with the clamped scalar
- The returned EdwardsPoint matches the basepoint multiplication result
-/
@[progress]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    ∃ result,
    mul_base_clamped bytes = ok result ∧
    EdwardsPoint.IsValid result ∧
    (∃ clamped_scalar,
    scalar.clamp_integer bytes = ok clamped_scalar ∧
    result.toPoint = ((U8x32_as_Nat clamped_scalar) • constants.ED25519_BASEPOINT_POINT.toPoint)) := by
    unfold mul_base_clamped
    progress*

end curve25519_dalek.edwards.EdwardsPoint
