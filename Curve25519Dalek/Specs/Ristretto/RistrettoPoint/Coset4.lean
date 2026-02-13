/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EIGHT_TORSION
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Add

/-! # Spec Theorem for `RistrettoPoint::coset4`

Specification and proof for `RistrettoPoint::coset4`.

This function returns the 4-element coset self + E[4], where E[4] is the 4-torsion
subgroup of the Edwards curve. This is useful for debugging and understanding the
internal structure of Ristretto points.

If the Ristretto group is interpreted as the quotient 2E/E[4], then coset4 gives
the set of all valid EdwardsPoint representatives of the input RistrettoPoint equivalence class.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.constants
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a RistrettoPoint `self` (which is internally represented as an even EdwardsPoint)
  and returns an array of four even EdwardsPoints, constituting all four valid representatives
  of the input Ristretto equivalence class given by self.

• The 4 elements are computed as:

  - self + T₀ = self (where T₀ is the identity)
  - self + T₂ (where T₂ is EIGHT_TORSION[2])
  - self + T₄ (where T₄ is EIGHT_TORSION[4])
  - self + T₆ (where T₆ is EIGHT_TORSION[6])

• The EIGHT_TORSION array contains the eight torsion points contained in E[8] := {e in E | 8e = 0}
• By selecting elements at indices 2, 4, 6, we get representatives belonging to the
  the 4-torsion subgroup E[4]

natural language specs:

• The function always succeeds (no panic) for valid RistrettoPoint input self
• The four output Edwards points are all valid and are given by

  - self + T₀ = self (where T₀ is the identity)
  - self + T₂ (where T₂ is EIGHT_TORSION[2])
  - self + T₄ (where T₄ is EIGHT_TORSION[4])
  - self + T₆ (where T₆ is EIGHT_TORSION[6])
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.coset4`**:
• The function always succeeds (no panic) for valid RistrettoPoint input self
• The four output Edwards points are all valid and are given by

  - self + T₀ = self (where T₀ is the identity)
  - self + T₂ (where T₂ is EIGHT_TORSION[2])
  - self + T₄ (where T₄ is EIGHT_TORSION[4])
  - self + T₆ (where T₆ is EIGHT_TORSION[6])
-/
@[progress]
theorem coset4_spec (self : RistrettoPoint) (h_self_valid : self.IsValid) :
∃ result, coset4 self = ok result ∧
result.val[0].IsValid ∧ result.val[0].toPoint = self.toPoint + EIGHT_TORSION.val[0].toPoint ∧
result.val[1].IsValid ∧ result.val[1].toPoint = self.toPoint + EIGHT_TORSION.val[2].toPoint ∧
result.val[2].IsValid ∧ result.val[2].toPoint = self.toPoint + EIGHT_TORSION.val[4].toPoint ∧
result.val[3].IsValid ∧ result.val[3].toPoint = self.toPoint + EIGHT_TORSION.val[6].toPoint := by


  unfold coset4

  progress

  · exact ⟨EIGHT_TORSION.val[0]⟩

  · progress

    · sorry

    · sorry

    · progress

      · sorry

      · progress

        · sorry

        · sorry

        · progress

          · sorry

          · progress

            · sorry

            · sorry

            · constructor

              · sorry

              · constructor

                · sorry

                · constructor

                  · sorry

                  · constructor

                    · sorry

                    · constructor

                      · sorry

                      · constructor

                        · sorry

                        · constructor

                          · sorry

                          · sorry



end curve25519_dalek.ristretto.RistrettoPoint
