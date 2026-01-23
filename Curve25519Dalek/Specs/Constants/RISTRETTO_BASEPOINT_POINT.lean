/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `constants::RISTRETTO_BASEPOINT_POINT`

Specification and proof for the constant `RISTRETTO_BASEPOINT_POINT`.

This constant represents the Ristretto basepoint, which is the standard generator
point for the Ristretto group.

Source: curve25519-dalek/src/constants.rs -/

open Aeneas.Std Result Edwards
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

    • constants.RISTRETTO_BASEPOINT_POINT is a valid Ristretto point (which implies that
      it fulfills the curve equation)
    • constants.RISTRETTO_BASEPOINT_POINT has the same representation as the Edwards basepoint
    • constants.RISTRETTO_BASEPOINT_POINT is not the identity point

  Note: As a consequence of Lagrange's theorem, every non-identity point in a
  prime order group generates the entire group.
-/

/-- **Spec and proof concerning `constants.RISTRETTO_BASEPOINT_POINT`**:
    • constants.RISTRETTO_BASEPOINT_POINT is a valid Ristretto point (which amongst other things
      implies that it fulfills the curve equation)
    • constants.RISTRETTO_BASEPOINT_POINT has the same representation as the Edwards basepoint
    • constants.RISTRETTO_BASEPOINT_POINT is not the identity point
-/
@[progress]
theorem RISTRETTO_BASEPOINT_POINT_spec :

  -- The point has the same representation as the Edwards basepoint
  RISTRETTO_BASEPOINT_POINT = backend.serial.u64.constants.ED25519_BASEPOINT_POINT ∧

  -- The point is a valid Ristretto point
  RISTRETTO_BASEPOINT_POINT.IsValid ∧

  -- The point is not the identity point
  math.compress_pure RISTRETTO_BASEPOINT_POINT.toPoint ≠ math.compress_pure (0 : Point Ed25519) := by

  sorry



end curve25519_dalek.constants
