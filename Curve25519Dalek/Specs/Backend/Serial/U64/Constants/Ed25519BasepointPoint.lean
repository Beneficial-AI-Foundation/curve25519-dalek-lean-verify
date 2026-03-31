/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Basepoint
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

set_option linter.style.nativeDecide false

/-!
# Spec theorem for `constants::ED25519_BASEPOINT_POINT`

Specification and proof for the constant `ED25519_BASEPOINT_POINT`.

This constant represents the Ed25519 basepoint, which is the standard generator
point for the prime order subgroup of the Ed25519 elliptic curve group.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • ED25519_BASEPOINT_POINT is the standard Ed25519 basepoint,
      which serves as the generator point for the prime order subgroup of the Ed25519 elliptic
      curve group.
    • This constant is used as the base point for scalar multiplication operations in Ed25519.

natural language specs:

    • ED25519_BASEPOINT_POINT is a valid Edwards point (which amongst other things implies that
      it fulfills the curve equation)
    • ED25519_BASEPOINT_POINT is of prime order L
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.ED25519_BASEPOINT_POINT`**:
    • ED25519_BASEPOINT_POINT is a valid Edwards point (which amongst other things implies that
      it fulfills the curve equation)
    • ED25519_BASEPOINT_POINT is of prime order L
-/
@[step]
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      _root_.L • result.toPoint = 0 ∧
      result.toPoint ≠ 0 ∧
      4 • result.toPoint ≠ 0 ∧
      result.Z.toField ^ 2 - result.Y.toField ^ 2 =
        34737626771194858627071295502606372355980995399692169211837275202373938891970 ^ 2 ∧
      result.toPoint = _root_.Edwards.basepoint ⦄ := by
  unfold ED25519_BASEPOINT_POINT
  step*
  set ep := ({ X := fe, Y := fe1, Z := fe2, T := fe3 } : edwards.EdwardsPoint)
  have h_valid : ep.IsValid := by simp only [ep, *]; decide
  have h_bp : ep.toPoint = _root_.Edwards.basepoint := by simp only [ep, *]; decide
  rw [h_bp]
  refine ⟨h_valid, ?_, ?_, ?_, ?_, rfl⟩
  · exact _root_.Edwards.basepoint_order_L
  · exact _root_.Edwards.basepoint_ne_zero
  · exact _root_.Edwards.four_nsmul_basepoint_ne_zero
  · simp only [*]; decide

end curve25519_dalek.backend.serial.u64.constants
