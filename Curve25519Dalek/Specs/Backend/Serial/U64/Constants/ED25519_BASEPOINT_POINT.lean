/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation

/-! # Spec Theorem for `constants::ED25519_BASEPOINT_POINT`

Specification and proof for the constant `ED25519_BASEPOINT_POINT`.

This constant represents the Ed25519 basepoint, which is the standard generator
point for the prime order subgroup of the Ed25519 elliptic curve group.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result Edwards
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • ED25519_BASEPOINT_POINT is the standard Ed25519 basepoint,
      which serves as the generator point for the prime order subgroup of the Ed25519 elliptic curve group.
    • This constant is used as the base point for scalar multiplication operations in Ed25519.

natural language specs:

    • ED25519_BASEPOINT_POINT is a valid Edwards point (which amongst other things implies that it fulfills the curve equation)
    • ED25519_BASEPOINT_POINT is of prime order L
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.ED25519_BASEPOINT_POINT`**:
    • ED25519_BASEPOINT_POINT is a valid Edwards point (which amongst other things implies that it fulfills the curve equation)
    • ED25519_BASEPOINT_POINT is of prime order L
-/
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT.IsValid ∧
    _root_.L • ED25519_BASEPOINT_POINT.toPoint = 0 ∧ ED25519_BASEPOINT_POINT.toPoint ≠ 0 := by
  have h_valid : ED25519_BASEPOINT_POINT.IsValid := by
    unfold ED25519_BASEPOINT_POINT
    decide
  constructor
  · exact h_valid
  constructor
  · sorry
  · intro h
    have h_X_zero : ED25519_BASEPOINT_POINT.X.toField = 0 := by
      have : ED25519_BASEPOINT_POINT.toPoint.x = 0 := by
        rw [h]
        rfl
      rw [(edwards.EdwardsPoint.toPoint_of_isValid h_valid).1] at this
      field_simp [h_valid.Z_ne_zero] at this
      simp only [mul_zero] at this
      exact this
    have h_X_nonzero : ED25519_BASEPOINT_POINT.X.toField ≠ 0 := by
      unfold ED25519_BASEPOINT_POINT
      decide
    exact h_X_nonzero h_X_zero

end curve25519_dalek.backend.serial.u64.constants
