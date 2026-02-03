/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation
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

    -- The point has the same representation as the Edwards basepoint
    RISTRETTO_BASEPOINT_POINT = backend.serial.u64.constants.ED25519_BASEPOINT_POINT ∧

    -- The point is a valid Ristretto point
    RISTRETTO_BASEPOINT_POINT.IsValid ∧

    -- The point is not the identity point
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

  · -- Prove 4 • RISTRETTO_BASEPOINT_POINT.toPoint ≠ 0

    rw [h_eq]
    intro h_contra

    have h_L_mul := backend.serial.u64.constants.ED25519_BASEPOINT_POINT_spec.2.1
    have h_ne_zero := backend.serial.u64.constants.ED25519_BASEPOINT_POINT_spec.2.2
    have h_L_prime : Nat.Prime L := by
      unfold L
      exact PrimeCert.prime_ed25519_order

    -- Since L is prime, L • P = 0, and P ≠ 0, we have addOrderOf P = L
    have h_order_eq_L : addOrderOf (backend.serial.u64.constants.ED25519_BASEPOINT_POINT.toPoint) = L := by
      cases h_L_prime.eq_one_or_self_of_dvd _ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_L_mul) with
      | inl h => exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) h_ne_zero
      | inr h => exact h

    -- Contradiction: 4 • P = 0 implies L ∣ 4, but L > 4
    exact absurd
      (Nat.le_of_dvd (by decide) (h_order_eq_L ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_contra))
      (by unfold L; decide)


end curve25519_dalek.constants
