/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.MulBase
import Curve25519Dalek.Specs.Scalar.ClampInteger
/-! # Spec Theorem for `MontgomeryPoint::mul_base_clamped`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::MontgomeryPoint}::mul_base_clamped`.

This function performs scalar multiplication by the Montgomery basepoint after
clamping the input bytes to a valid scalar, delegating to `MontgomeryPoint.mul_base`.

**Source**: curve25519-dalek/src/montgomery.rs, lines 150:4-158:5
-/

open Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

• Clamps the 32-byte input to a valid scalar using `scalar.clamp_integer`.

• Computes the Montgomery basepoint multiplication with the clamped scalar by
  delegating to `MontgomeryPoint.mul_base`.

natural language specs:

• The function always succeeds (no panic)
• The result is the Montgomery basepoint multiplication of the clamped scalar
-/

/--
**Spec and proof concerning `montgomery.MontgomeryPoint.mul_base_clamped`**:
- No panic (always returns successfully)
- Clamps input bytes with `scalar.clamp_integer`
- Delegates to `montgomery.MontgomeryPoint.mul_base` with the clamped scalar
- The returned MontgomeryPoint matches the basepoint multiplication result
-/

@[progress]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    spec (mul_base_clamped bytes) (fun result =>
    (∃ clamped_scalar_nat,
    h ∣ clamped_scalar_nat ∧
    clamped_scalar_nat < 2 ^ 255 ∧
    2 ^ 254 ≤ clamped_scalar_nat ∧
    Montgomery.MontgomeryPoint.toPoint result = clamped_scalar_nat • (fromEdwards constants.ED25519_BASEPOINT_POINT.toPoint)))    := by
   unfold mul_base_clamped
   progress*
   exact ⟨U8x32_as_Nat a, a_post_1, a_post_2, a_post_3, res_post⟩

end curve25519_dalek.montgomery.MontgomeryPoint
