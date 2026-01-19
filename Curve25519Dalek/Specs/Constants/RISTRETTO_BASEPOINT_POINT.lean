/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `constants::RISTRETTO_BASEPOINT_POINT`

Specification and proof for the constant `RISTRETTO_BASEPOINT_POINT`.

This constant represents the Ristretto basepoint, which is the standard generator
point for the Ristretto group.

Source: curve25519-dalek/src/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.constants

/-
natural language description:

    • constants.RISTRETTO_BASEPOINT_POINT is the standard Ristretto basepoint, which serves
      as the generator point for the Ristretto group.
    • It is defined as RistrettoPoint(ED25519_BASEPOINT_POINT), wrapping the Ed25519 basepoint
      in the Ristretto point type.
    • This constant is used as the base point for scalar multiplication operations in the
      Ristretto group.

natural language specs:

    • constants.RISTRETTO_BASEPOINT_POINT equals backend.serial.u64.constants.ED25519_BASEPOINT_POINT
      when unwrapped from the RistrettoPoint type.
-/

/-- **Spec and proof concerning `constants.RISTRETTO_BASEPOINT_POINT`**:
- The Ristretto basepoint is equal to the Ed25519 basepoint
-/
@[progress]
theorem RISTRETTO_BASEPOINT_POINT_spec :
  constants.RISTRETTO_BASEPOINT_POINT = backend.serial.u64.constants.ED25519_BASEPOINT_POINT := by
  unfold constants.RISTRETTO_BASEPOINT_POINT
  unfold RISTRETTO_BASEPOINT_POINT_body
  sorry

end curve25519_dalek.constants
