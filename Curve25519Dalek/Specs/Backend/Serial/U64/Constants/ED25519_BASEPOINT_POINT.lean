/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromLimbs

/-! # Spec Theorem for `constants::ED25519_BASEPOINT_POINT`

Specification and proof for the constant `ED25519_BASEPOINT_POINT`.

This constant represents the Ed25519 basepoint, which is the standard generator
point for the prime order subgroup of the Ed25519 elliptic curve group.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
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
@[progress]
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      _root_.L • result.toPoint = 0 ∧
      result.toPoint ≠ 0 ∧
      4 • result.toPoint ≠ 0 ∧
      result.Z.toField ^ 2 - result.Y.toField ^ 2 =
        34737626771194858627071295502606372355980995399692169211837275202373938891970 ^ 2 ⦄ := by
  unfold ED25519_BASEPOINT_POINT
  progress*
  set ep := ({ X := fe, Y := fe1, Z := fe2, T := fe3 } : edwards.EdwardsPoint)
  have h_valid : ep.IsValid := by simp only [ep, *]; decide
  have h_ne_zero : ep.toPoint ≠ 0 := by
    by_contra h
    have h : ep.X.toField = 0 := by
      have : ep.toPoint.x = 0 := by rw [h]; rfl
      have := edwards.EdwardsPoint.toPoint_of_isValid h_valid
      grind [h_valid.Z_ne_zero]
    exact absurd h (by simp only [*, ep]; decide)
  have h_L_mul : _root_.L • ep.toPoint = 0 := by
    -- ⊢ L • ED25519_BASEPOINT_POINT = 0
    sorry
  refine ⟨h_valid, h_L_mul, h_ne_zero, ?_, ?_⟩
  · intro h_contra
    have h_L_prime : Nat.Prime _root_.L := by unfold _root_.L; exact PrimeCert.prime_ed25519_order
    have h_order_eq_L : addOrderOf ep.toPoint = _root_.L :=
      (h_L_prime.eq_one_or_self_of_dvd _ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_L_mul)).resolve_left
        (fun h => h_ne_zero (AddMonoid.addOrderOf_eq_one_iff.mp h))
    exact absurd
      (Nat.le_of_dvd (by decide) (h_order_eq_L ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_contra))
      (by unfold _root_.L; decide)
  · simp only [*]
    decide

end curve25519_dalek.backend.serial.u64.constants
