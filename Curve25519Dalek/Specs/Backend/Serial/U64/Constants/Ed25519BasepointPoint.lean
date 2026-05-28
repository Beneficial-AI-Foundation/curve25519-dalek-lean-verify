/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Basepoint
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_POINT`

This constant represents the Ed25519 basepoint, which is the standard generator point for
the prime order subgroup of the Ed25519 elliptic curve group.

Source: "curve25519-dalek/src/backend/serial/u64/constants.rs"
-/

-- nativeDecide is suppressed because `decide` in the proof elaborates via the native kernel
set_option linter.style.nativeDecide false

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.constants

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u64::constants::ED25519_BASEPOINT_POINT`**
• The function always succeeds (no panic)
• The result is a valid Edwards point (it satisfies the Edwards curve equation)
• It has prime order `L`, i.e. `L • result.toPoint = 0`
• It is non-zero, and so is `4 • result.toPoint`
• `result.Z^2 - result.Y^2` equals the square of a specific witness integer
• `result.toPoint` equals the canonical Ed25519 Edwards basepoint
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
