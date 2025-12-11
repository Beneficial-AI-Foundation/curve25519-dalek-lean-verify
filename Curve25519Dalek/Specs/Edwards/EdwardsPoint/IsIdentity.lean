/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq


open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-! # Spec for `traits::IsIdentity::is_identity` -/

/-- **Spec and proof concerning `traits.IsIdentity.Blanket.is_identity` specialized to
`EdwardsPoint`**:
- Always succeeds
- Returns `true` iff the constant-time equality check with the identity point succeeds -/
@[progress]
theorem is_identity_spec (e : EdwardsPoint) :
    ∃ b id eq_choice,
      traits.IsIdentity.Blanket.is_identity
          subtle.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint
          traits.Identitycurve25519_dalekedwardsEdwardsPoint e = ok b ∧
      Identitycurve25519_dalekedwardsEdwardsPoint.identity = ok id ∧
      ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint.ct_eq e id = ok eq_choice ∧
      (b = true ↔ eq_choice = Choice.one) := by
  unfold traits.IsIdentity.Blanket.is_identity
  progress*
  sorry

end curve25519_dalek.edwards.EdwardsPoint
