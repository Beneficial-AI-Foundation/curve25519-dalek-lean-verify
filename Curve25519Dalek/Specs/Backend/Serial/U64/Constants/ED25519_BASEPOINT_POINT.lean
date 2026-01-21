/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `backend.serial.u64.constants.ED25519_BASEPOINT_POINT`

Specification and proof for the constant `ED25519_BASEPOINT_POINT`.

This constant represents the Ed25519 basepoint, which is the standard generator
point for the Ed25519 elliptic curve group.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result Edwards
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • backend.serial.u64.constants.ED25519_BASEPOINT_POINT is the standard Ed25519 basepoint,
      which serves as the generator point for the Ed25519 elliptic curve group.
    • It is defined with specific X, Y, Z, T coordinates in extended twisted Edwards form,
      representing the affine basepoint (Gx, Gy) where:
      - Gx = 15112221349535400772501151409588531511454012693041857206046113283949847762202
      - Gy = 46316835694926478169428394003475163141307993866256225615783033603165251855960
    • This constant is used as the base point for scalar multiplication operations in Ed25519.

natural language specs:

    • backend.serial.u64.constants.ED25519_BASEPOINT_POINT is a valid Edwards point (which
      implies that it fulfills the curve equation and coordinate bounds)
    • backend.serial.u64.constants.ED25519_BASEPOINT_POINT is not the identity point

  Note: As a consequence of Lagrange's theorem, every non-identity point in a
  prime order group generates the entire group.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.ED25519_BASEPOINT_POINT`**:
    • backend.serial.u64.constants.ED25519_BASEPOINT_POINT is a valid Edwards point
      (which amongst other things implies that it fulfills the curve equation)
    • backend.serial.u64.constants.ED25519_BASEPOINT_POINT is not the identity point
-/
@[progress]
theorem ED25519_BASEPOINT_POINT_spec :

  -- The point is a valid Edwards point
  ED25519_BASEPOINT_POINT.IsValid ∧

  -- The point is not the identity point.
  math.compress_pure ED25519_BASEPOINT_POINT.toPoint ≠ math.compress_pure (0 : Point Ed25519) := by

  sorry



end curve25519_dalek.backend.serial.u64.constants
