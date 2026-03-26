/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.Ed25519BasepointPoint

/-! # Spec Theorem for `constants::RISTRETTO_BASEPOINT_POINT`

Specification and proof for the constant `RISTRETTO_BASEPOINT_POINT`.

This constant represents the Ristretto basepoint, which is the standard generator
point for the Ristretto group.

Source: curve25519-dalek/src/constants.rs -/

open Aeneas Aeneas.Std Result Edwards
open curve25519_dalek.backend.serial.u64.field (FieldElement51.toField)
open curve25519_dalek.ristretto
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
    RISTRETTO_BASEPOINT_POINT ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧ _root_.L • result.toPoint = 0 ∧
      result.toPoint ≠ 0 ∧ 4 • result.toPoint ≠ 0 ∧
      result.toPoint = _root_.Edwards.basepoint ⦄ := by
    unfold RISTRETTO_BASEPOINT_POINT RistrettoPoint.IsValid RistrettoPoint.toPoint
    progress*
    refine ⟨by grind, ?_, by grind, by grind, by grind, by grind⟩
    · use 34737626771194858627071295502606372355980995399692169211837275202373938891970
      grind

end curve25519_dalek.constants
