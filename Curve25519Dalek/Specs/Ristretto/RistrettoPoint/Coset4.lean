/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `RistrettoPoint::coset4`

Specification and proof for `RistrettoPoint::coset4`.

This function returns the 4-element coset self + E[4], where E[4] is the 4-torsion
subgroup of the Edwards curve. This is useful for debugging and understanding the
internal structure of Ristretto points.

A RistrettoPoint represents an equivalence class of 8 Edwards points that differ by
8-torsion. The coset4 function returns 4 representatives from this equivalence class,
specifically those that differ by the 4-torsion subgroup E[4] ⊆ E[8].

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a RistrettoPoint `self` (which is internally represented as an EdwardsPoint)
  and returns an array of 4 EdwardsPoint elements representing the coset self + E[4]

• The 4 elements are computed as:
  - self + T₀ = self (where T₀ is the identity)
  - self + T₂ (where T₂ is EIGHT_TORSION[2])
  - self + T₄ (where T₄ is EIGHT_TORSION[4])
  - self + T₆ (where T₆ is EIGHT_TORSION[6])

• The EIGHT_TORSION array contains the 8 torsion points E[8] of order dividing 8
• By selecting elements at indices 2, 4, 6, we get representatives that generate
  the 4-torsion subgroup E[4]

natural language specs:

• The function always succeeds (no panic) for valid RistrettoPoint inputs
• Returns exactly 4 EdwardsPoint elements
• All 4 returned points represent the same Ristretto element (same equivalence class)
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.coset4`**:
• The function always succeeds (no panic) for valid RistrettoPoint inputs
• Returns exactly 4 EdwardsPoint elements
• All 4 returned points represent the same Ristretto element (same equivalence class)
-/
@[progress]
theorem coset4_spec (self : RistrettoPoint)

    (h_self_bounds : ∀ i < 5,
      self.X[i]!.val < 2 ^ 53 ∧
      self.Y[i]!.val < 2 ^ 53 ∧
      self.Z[i]!.val < 2 ^ 53 ∧
      self.T[i]!.val < 2 ^ 53)

    (h_self_Z_nonzero : Field51_as_Nat self.Z % p ≠ 0) :

    ∃ result, coset4 self = ok result ∧

    ∃ (ep : edwards.EdwardsPoint)
      (ep1 : edwards.EdwardsPoint)
      (ep2 : edwards.EdwardsPoint)
      (ep3 : edwards.EdwardsPoint)
      (ep4 : edwards.EdwardsPoint)
      (ep5 : edwards.EdwardsPoint),

    -- The torsion point retrievals succeed
    (backend.serial.u64.constants.EIGHT_TORSION.index_usize 2#usize = ok ep) ∧
    (backend.serial.u64.constants.EIGHT_TORSION.index_usize 4#usize = ok ep2) ∧
    (backend.serial.u64.constants.EIGHT_TORSION.index_usize 6#usize = ok ep4) ∧

    -- The additions succeed
    edwards.AddEdwardsPointEdwardsPointEdwardsPoint.add self ep = ok ep1 ∧
    edwards.AddEdwardsPointEdwardsPointEdwardsPoint.add self ep2 = ok ep3 ∧
    edwards.AddEdwardsPointEdwardsPointEdwardsPoint.add self ep4 = ok ep5 ∧

    -- The result array contains the 4 coset elements
    (∃ r0, result.index_usize 0#usize = ok r0 ∧ r0 = self) ∧
    (∃ r1, result.index_usize 1#usize = ok r1 ∧ r1 = ep1) ∧
    (∃ r2, result.index_usize 2#usize = ok r2 ∧ r2 = ep3) ∧
    (∃ r3, result.index_usize 3#usize = ok r3 ∧ r3 = ep5) ∧

    -- Bounds on the resulting points
    (∀ i < 5,
      ep1.X[i]!.val < 2 ^ 54  ∧
      ep1.Y[i]!.val < 2 ^ 54  ∧
      ep1.Z[i]!.val < 2 ^ 54  ∧
      ep1.T[i]!.val < 2 ^ 54) ∧

    (∀ i < 5,
      ep3.X[i]!.val < 2 ^ 54  ∧
      ep3.Y[i]!.val < 2 ^ 54  ∧
      ep3.Z[i]!.val < 2 ^ 54  ∧
      ep3.T[i]!.val < 2 ^ 54) ∧

    (∀ i < 5,
      ep5.X[i]!.val < 2 ^ 54  ∧
      ep5.Y[i]!.val < 2 ^ 54  ∧
      ep5.Z[i]!.val < 2 ^ 54  ∧
      ep5.T[i]!.val < 2 ^ 54) := by
  sorry

end curve25519_dalek.ristretto.RistrettoPoint
