/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.ED25519_BASEPOINT_POINT

/-! # Spec Theorem for `constants::RISTRETTO_BASEPOINT_POINT`

Specification and proof for the constant `RISTRETTO_BASEPOINT_POINT`.

This constant represents the Ristretto basepoint, which is the standard generator
point for the Ristretto group.

Source: curve25519-dalek/src/constants.rs -/

open Aeneas.Std Result Edwards
open curve25519_dalek.backend.serial.u64.field (FieldElement51.toField)
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

    • constants.RISTRETTO_BASEPOINT_POINT is a valid RistrettoPoint (which implies that
      it fulfills the curve equation)
    • constants.RISTRETTO_BASEPOINT_POINT has the same representation as the Edwards basepoint
    • constants.RISTRETTO_BASEPOINT_POINT is not the identity point (i.e., the EdwardsPoint representing the
      basepoint is not in the same Ristretto equivalence class as the EdwardsPoint identity point, which
      is equivalent to saying that the difference between both points is not in E[4])

  Note: As a consequence of Lagrange's theorem, every non-identity point in a
  prime order group generates the entire group.
-/

/-- **Spec and proof concerning `constants.RISTRETTO_BASEPOINT_POINT`**:
    • constants.RISTRETTO_BASEPOINT_POINT is a valid RistrettoPoint (which amongst other things
      implies that it fulfills the curve equation)
    • constants.RISTRETTO_BASEPOINT_POINT has the same representation as the Edwards basepoint
    • constants.RISTRETTO_BASEPOINT_POINT is not the identity point (i.e., the EdwardsPoint representing the
      basepoint is not in the same Ristretto equivalence class as the EdwardsPoint identity point, which
      is equivalent to saying that the difference between both points is not in E[4])
-/
@[progress]
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT = backend.serial.u64.constants.ED25519_BASEPOINT_POINT ∧
    RISTRETTO_BASEPOINT_POINT.IsValid ∧
    4 • RISTRETTO_BASEPOINT_POINT.toPoint ≠ 0 := by
  have h_eq : RISTRETTO_BASEPOINT_POINT = backend.serial.u64.constants.ED25519_BASEPOINT_POINT := by
    simp only [global_simps]
  constructor
  · exact h_eq
  constructor
  · rw [h_eq]
    constructor
    · exact backend.serial.u64.constants.ED25519_BASEPOINT_POINT_spec.1
    · use (34737626771194858627071295502606372355980995399692169211837275202373938891970 : CurveField)
      unfold backend.serial.u64.constants.ED25519_BASEPOINT_POINT
      rfl
  · rw [h_eq]
    intro h_contra
    have h_L_mul := backend.serial.u64.constants.ED25519_BASEPOINT_POINT_spec.2.1
    have h_ne_zero := backend.serial.u64.constants.ED25519_BASEPOINT_POINT_spec.2.2
    have h_L_prime : Nat.Prime L := Fact.out
    have h_order_eq_L : addOrderOf (backend.serial.u64.constants.ED25519_BASEPOINT_POINT.toPoint) = L :=
      (h_L_prime.eq_one_or_self_of_dvd _ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_L_mul)).resolve_left
      (fun h => h_ne_zero (AddMonoid.addOrderOf_eq_one_iff.mp h))
    exact absurd
      (Nat.le_of_dvd (by decide) (h_order_eq_L ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_contra))
      (by unfold L; decide)

end curve25519_dalek.constants
