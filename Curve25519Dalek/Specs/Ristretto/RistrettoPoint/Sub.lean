/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Sub

/-! # Spec Theorem for `RistrettoPoint::sub`

Specification and proof for the `Sub` trait implementation for Ristretto points.

This function subtracts two Ristretto points via elliptic curve subtraction by delegating
to the underlying Edwards point subtraction.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint

/-
natural language description:

• Takes two RistrettoPoints `self` and `other`
• Returns their difference as a RistrettoPoint via elliptic curve group subtraction
• Implementation: unwraps both points to their underlying EdwardsPoint representations,
  performs Edwards subtraction, and wraps the result back as a RistrettoPoint

natural language specs:

• The function always succeeds (no panic) for valid input Ristretto points
• The result is a valid Ristretto point
• The result represents the difference of the inputs (in the mathematical context of elliptic curve subtraction)
-/

/-- **Spec and proof concerning `Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint.sub`**:
• The function always succeeds (no panic) for valid inputs
• The result is a valid Ristretto point
• The result represents the difference of the inputs (in the context of elliptic curve subtraction)
-/
@[progress]
theorem sub_spec
    (self other : RistrettoPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    sub self other ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint - other.toPoint ⦄ := by
  unfold sub edwards.EdwardsPoint.Insts.CoreOpsArithSubEdwardsPointEdwardsPoint.sub
  progress
  · exact h_self_valid.1
  · exact h_other_valid.1
  · rename_i ep h_ep_valid h_ep_toPoint
    have h_toPoint : ep.toPoint = self.toPoint - other.toPoint := by
      unfold RistrettoPoint.toPoint; exact h_ep_toPoint
    have h_even : ∀ r : RistrettoPoint, r.IsValid → IsEven r.toPoint := fun r hr => by
      unfold RistrettoPoint.toPoint; exact (EdwardsPoint_IsSquare_iff_IsEven r hr.1).mp hr.2
    refine ⟨⟨h_ep_valid, ?_⟩, h_toPoint⟩
    rw [EdwardsPoint_IsSquare_iff_IsEven ep h_ep_valid, h_toPoint, sub_eq_add_neg]
    apply even_add_closure_Ed25519
    · exact h_even self h_self_valid
    · obtain ⟨Q, hQ⟩ := (IsEven_iff_in_doubling_image _).mp (h_even other h_other_valid)
      exact (IsEven_iff_in_doubling_image _).mpr ⟨-Q, by rw [hQ]; abel⟩

end curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint
