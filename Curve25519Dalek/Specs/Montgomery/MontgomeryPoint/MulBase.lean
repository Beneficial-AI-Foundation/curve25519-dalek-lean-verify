/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.MulBase
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.ToMontgomery
/-! # Spec Theorem for `MontgomeryPoint::mul_base`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::MontgomeryPoint}::mul_base`.

This function computes the Montgomery basepoint scalar multiplication by first
performing Edwards basepoint multiplication and then converting the resulting
EdwardsPoint to a MontgomeryPoint.

**Source**: curve25519-dalek/src/montgomery.rs, lines 128:4-130:5

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.curve_models.curve25519_dalek.montgomery
open curve25519_dalek.edwards
open curve25519_dalek.backend.serial.u64

namespace curve25519_dalek.montgomery.MontgomeryPoint

/-
natural language description:

• Computes the scalar multiplication [s]B for the Montgomery basepoint by
  delegating to EdwardsPoint::mul_base and then converting to Montgomery form.

• The implementation calls `edwards.EdwardsPoint.mul_base` and then
  `edwards.EdwardsPoint.to_montgomery` on the result.

natural language specs:

• The function always succeeds (no panic)
• The returned MontgomeryPoint is the Montgomery conversion of the Edwards
  basepoint multiplication result
-/

/-- **Spec and proof concerning `montgomery.MontgomeryPoint.mul_base`**:
- No panic (always returns successfully)
- Delegates to `edwards.EdwardsPoint.mul_base` and `edwards.EdwardsPoint.to_montgomery`
- The returned MontgomeryPoint is the Montgomery conversion of the Edwards basepoint result
-/
@[progress]
theorem mul_base_spec (scalar : scalar.Scalar) :
    ∃ result,
    mul_base scalar = ok result ∧
    MontgomeryPoint.IsValid result ∧
    (MontgomeryPoint.toPoint result).y = ((U8x32_as_Nat scalar.bytes) • constants.ED25519_BASEPOINT_POINT.toPoint).y
     := by
    unfold mul_base
    sorry


end curve25519_dalek.montgomery.MontgomeryPoint
