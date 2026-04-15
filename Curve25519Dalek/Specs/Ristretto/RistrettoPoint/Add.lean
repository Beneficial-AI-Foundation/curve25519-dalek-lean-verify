/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Add

/-!
# Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::add`

Adds two Ristretto points via elliptic curve group addition. The implementation unwraps both
points to their underlying `EdwardsPoint` representations, performs Edwards addition, and
wraps the result back as a `RistrettoPoint`.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.Shared0RistrettoPoint.Insts
namespace CoreOpsArithAddSharedARistrettoPointRistrettoPoint

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::add`**
• The function always succeeds (no panic) for valid inputs
• The result is a valid Ristretto point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/
@[step]
theorem add_spec (self other : RistrettoPoint) (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    add self other ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint + other.toPoint ⦄ := by
  unfold add
  step*
  · constructor
    · constructor
      · exact ep_post1
      · have h_self_even : IsEven (self.toPoint) := by
          unfold RistrettoPoint.toPoint
          rw [← EdwardsPoint_IsSquare_iff_IsEven self h_self_valid.1]
          exact h_self_valid.2
        have h_other_even : IsEven (other.toPoint) := by
          unfold RistrettoPoint.toPoint
          rw [← EdwardsPoint_IsSquare_iff_IsEven other h_other_valid.1]
          exact h_other_valid.2
        have h_eq_points : ep.toPoint = self.toPoint + other.toPoint := by
          unfold RistrettoPoint.toPoint
          exact ep_post2
        rw [EdwardsPoint_IsSquare_iff_IsEven ep ep_post1, h_eq_points]
        exact even_add_closure_Ed25519 _ _ h_self_even h_other_even
    · exact ep_post2

end CoreOpsArithAddSharedARistrettoPointRistrettoPoint
end curve25519_dalek.Shared0RistrettoPoint.Insts
