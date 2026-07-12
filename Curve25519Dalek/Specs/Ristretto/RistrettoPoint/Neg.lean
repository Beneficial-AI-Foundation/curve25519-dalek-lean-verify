/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Neg

/-!
# Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::neg`

Negates a Ristretto point via elliptic curve negation. The implementation unwraps the
point to its underlying `EdwardsPoint` representation, performs Edwards negation (negating
the X and T coordinates while keeping Y and Z unchanged), and wraps the result back as a
`RistrettoPoint`.

This file covers two Lean extraction variants: the core implementation
(`Shared0RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint`) from `ristretto.rs` which
takes the operand by reference (`-&RistrettoPoint`), and a by-value wrapper
(`ristretto.RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint`) which delegates
directly to the core implementation.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::neg`**
• The function always succeeds (no panic) for valid inputs
• The result is a valid Ristretto point
• The result represents the negation of the input (in the context of elliptic curve negation)
-/
@[step]
theorem neg_spec (self : RistrettoPoint) (h_self_valid : self.IsValid) :
    neg self ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = -self.toPoint ⦄ := by
  unfold neg
  step*
  · have h_toPoint : RistrettoPoint.toPoint ep = -self.toPoint := by
      unfold RistrettoPoint.toPoint; exact ep_post2
    have h_even : ∀ r : RistrettoPoint, r.IsValid → IsEven r.toPoint := fun r hr => by
      unfold RistrettoPoint.toPoint; exact (EdwardsPoint_IsSquare_iff_IsEven r hr.1).mp hr.2
    refine ⟨⟨ep_post1, ?_⟩, h_toPoint⟩
    rw [EdwardsPoint_IsSquare_iff_IsEven ep ep_post1]
    unfold RistrettoPoint.toPoint at h_toPoint
    rw [h_toPoint]
    obtain ⟨Q, hQ⟩ := (IsEven_iff_in_doubling_image _).mp (h_even self h_self_valid)
    exact (IsEven_iff_in_doubling_image _).mpr ⟨-Q, by
      unfold RistrettoPoint.toPoint at hQ; rw [hQ]; abel⟩

end curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint

/-! ## Wrapper: `-RistrettoPoint` (by-value)

The following variant wraps the core `-&RistrettoPoint` implementation by
delegating directly to `Shared0RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint.neg`.
In the Lean extraction, `self` is passed by value (corresponding to the Rust
`RistrettoPoint` value). Source: ristretto.rs, lines 954:4-956:5.
-/

namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::neg`**
• The function always succeeds (no panic) for valid inputs
• The result is a valid Ristretto point
• The result represents the negation of the input (in the context of elliptic curve negation)
-/
@[step]
theorem neg_spec (self : RistrettoPoint) (h_self_valid : self.IsValid) :
    neg self ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = -self.toPoint ⦄ := by
  unfold neg
  step*

end curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint
