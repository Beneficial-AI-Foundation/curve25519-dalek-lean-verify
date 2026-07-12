/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::traits::IsIdentity::is_identity`

Blanket implementation of `IsIdentity` for any type `T` that implements both
`ConstantTimeEq` and `Identity`.

Given a value `self : T`, the function:
1. Constructs the identity element via `T::identity()`.
2. Performs a constant-time equality check `self.ct_eq(&identity)`, obtaining a `Choice`.
3. Converts the `Choice` to `Bool` (`Choice::one → true`, `Choice::zero → false`).

This is the generic trait implementation that underlies `EdwardsPoint::is_small_order`,
`EdwardsPoint::is_torsion_free`, and similar identity‐checking routines throughout the
library.

Source: "curve25519-dalek/src/traits.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.traits.IsIdentity.Blanket

/-- **Spec theorem for `curve25519_dalek::traits::IsIdentity::is_identity`**
• The function succeeds whenever `identity` and `ct_eq` succeed
• The returned `Bool` is `true` if and only if `ct_eq self (identity)` yields `Choice.one`
• Postconditions `P` (on the identity element) and `Q` (on the ct_eq result) are
  forwarded from the caller's hypotheses into the conclusion
-/
@[step]
theorem is_identity_spec
    {T : Type} {P : T → Prop} {Q : T → subtle.Choice → Prop}
    (subtleConstantTimeEqInst : subtle.ConstantTimeEq T)
    (IdentityInst : traits.Identity T)
    (self : T)
    (h_id : IdentityInst.identity ⦃ P ⦄)
    (h_ct : ∀ t, P t → subtleConstantTimeEqInst.ct_eq self t ⦃ Q t ⦄) :
    is_identity subtleConstantTimeEqInst IdentityInst self ⦃ (result : Bool) =>
      ∃ t c, P t ∧ Q t c ∧ (result ↔ c = Choice.one) ⦄ := by
  unfold is_identity
  have ⟨t₀, ht₀, hP⟩ := spec_imp_exists h_id
  have ⟨c₀, hc₀, hQ⟩ := spec_imp_exists (h_ct t₀ hP)
  simp only [ht₀, bind_tc_ok, hc₀, core.convert.IntoFrom.into,
    Bool.Insts.CoreConvertFromChoice.from, spec_ok]
  refine ⟨t₀, c₀, hP, hQ, ?_⟩
  simp only [decide_eq_true_eq]
  constructor
  · intro h; cases c₀; simp_all [Choice.one]
  · intro h; subst h; rfl

end curve25519_dalek.traits.IsIdentity.Blanket
