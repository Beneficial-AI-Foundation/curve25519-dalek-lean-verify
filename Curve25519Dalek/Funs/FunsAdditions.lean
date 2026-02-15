import Curve25519Dalek.Funs

namespace curve25519_dalek

open Aeneas.Std Result

/-- Implementation of `montgomery.ConditionallySelectableMontgomeryPoint.conditional_assign`:
   Conditionally assign b to a if choice(1); otherwise leave a unchanged -/
noncomputable def montgomery.ConditionallySelectableMontgomeryPoint.conditional_assign_impl
  (a : montgomery.MontgomeryPoint) (b : montgomery.MontgomeryPoint)
  (choice : subtle.Choice) :
  Result montgomery.MontgomeryPoint :=
  montgomery.ConditionallySelectableMontgomeryPoint.conditional_select a b choice

/-- **Spec theorem for `montgomery.ConditionallySelectableMontgomeryPoint.conditional_assign_impl`**:
- No panic (if conditional_select succeeds)
- Returns the result of conditional_select(a, b, choice)
-/
@[progress]
theorem montgomery.ConditionallySelectableMontgomeryPoint.conditional_assign_impl_spec
  (a b : montgomery.MontgomeryPoint) (choice : subtle.Choice)
  (h : ∃ res, montgomery.ConditionallySelectableMontgomeryPoint.conditional_select a b choice = ok res) :
  ∃ res,
    montgomery.ConditionallySelectableMontgomeryPoint.conditional_assign_impl a b choice = ok res ∧
    montgomery.ConditionallySelectableMontgomeryPoint.conditional_select a b choice = ok res := by
  unfold montgomery.ConditionallySelectableMontgomeryPoint.conditional_assign_impl
  obtain ⟨res, h_eq⟩ := h
  use res

/-- Implementation of `montgomery.ConditionallySelectableMontgomeryPoint.conditional_swap`:
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
noncomputable def montgomery.ConditionallySelectableMontgomeryPoint.conditional_swap_impl
  (a : montgomery.MontgomeryPoint) (b : montgomery.MontgomeryPoint)
  (choice : subtle.Choice) :
  Result (montgomery.MontgomeryPoint × montgomery.MontgomeryPoint) := do
  let a_new ← montgomery.ConditionallySelectableMontgomeryPoint.conditional_select a b choice
  let b_new ← montgomery.ConditionallySelectableMontgomeryPoint.conditional_select b a choice
  ok (a_new, b_new)

/-- **Spec theorem for `montgomery.ConditionallySelectableMontgomeryPoint.conditional_swap_impl`**:
- No panic (if conditional_select succeeds)
- Returns (a_new, b_new) where:
  - a_new = conditional_select(a, b, choice)
  - b_new = conditional_select(b, a, choice)
- If choice = Choice.one: swaps a and b
- If choice = Choice.zero: leaves them unchanged
-/
@[progress]
theorem montgomery.ConditionallySelectableMontgomeryPoint.conditional_swap_impl_spec
  (a b : montgomery.MontgomeryPoint) (choice : subtle.Choice)
  (h_a : ∃ res, montgomery.ConditionallySelectableMontgomeryPoint.conditional_select a b choice = ok res)
  (h_b : ∃ res, montgomery.ConditionallySelectableMontgomeryPoint.conditional_select b a choice = ok res) :
  ∃ c,
    montgomery.ConditionallySelectableMontgomeryPoint.conditional_swap_impl a b choice = ok c ∧
    montgomery.ConditionallySelectableMontgomeryPoint.conditional_select a b choice = ok c.1 ∧
    montgomery.ConditionallySelectableMontgomeryPoint.conditional_select b a choice = ok c.2 := by
  unfold montgomery.ConditionallySelectableMontgomeryPoint.conditional_swap_impl
  obtain ⟨a_new, h_a_eq⟩ := h_a
  obtain ⟨b_new, h_b_eq⟩ := h_b
  use (a_new, b_new)
  simp [h_a_eq, h_b_eq]

/-- Implementation of `montgomery.PartialEqMontgomeryPointMontgomeryPoint.ne`:
   Returns true if and only if the two MontgomeryPoint values are not equal -/
noncomputable def montgomery.PartialEqMontgomeryPointMontgomeryPoint.ne_impl
  (self : montgomery.MontgomeryPoint) (other : montgomery.MontgomeryPoint) :
  Result Bool := do
  let eq_result ← montgomery.PartialEqMontgomeryPointMontgomeryPoint.eq self other
  ok (!eq_result)

/-- **Spec theorem for `montgomery.PartialEqMontgomeryPointMontgomeryPoint.ne_impl`**:
- No panic (if eq succeeds)
- Returns true if and only if the two MontgomeryPoint values are not equal
- Equivalent to negation of eq
-/
@[progress]
theorem montgomery.PartialEqMontgomeryPointMontgomeryPoint.ne_impl_spec
  (self other : montgomery.MontgomeryPoint)
  (h : ∃ res, montgomery.PartialEqMontgomeryPointMontgomeryPoint.eq self other = ok res) :
  ∃ ne_res,
    montgomery.PartialEqMontgomeryPointMontgomeryPoint.ne_impl self other = ok ne_res ∧
    ∃ eq_res, montgomery.PartialEqMontgomeryPointMontgomeryPoint.eq self other = ok eq_res ∧
    ne_res = !eq_res := by
  unfold montgomery.PartialEqMontgomeryPointMontgomeryPoint.ne_impl
  obtain ⟨eq_res, h_eq⟩ := h
  use !eq_res
  constructor
  · simp [h_eq]
  · use eq_res

/-- Implementation of `montgomery.EqMontgomeryPoint.assert_receiver_is_total_eq`:
   Returns Unit (no-op assertion that Eq is properly implemented) -/
def montgomery.EqMontgomeryPoint.assert_receiver_is_total_eq_impl
  (_self : montgomery.MontgomeryPoint) : Result Unit :=
  ok ()

/-- **Spec theorem for `montgomery.EqMontgomeryPoint.assert_receiver_is_total_eq_impl`**:
- No panic (always returns successfully)
- Returns Unit (no-op assertion that Eq is properly implemented)
-/
@[progress]
theorem montgomery.EqMontgomeryPoint.assert_receiver_is_total_eq_impl_spec
  (self : montgomery.MontgomeryPoint) :
  montgomery.EqMontgomeryPoint.assert_receiver_is_total_eq_impl self = ok () := by
  unfold montgomery.EqMontgomeryPoint.assert_receiver_is_total_eq_impl
  rfl

/-- Implementation of `montgomery.ConditionallySelectableProjectivePoint.conditional_assign`:
   Conditionally assign b to a if choice(1); otherwise leave a unchanged -/
def montgomery.ConditionallySelectableProjectivePoint.conditional_assign_impl
  (a : montgomery.ProjectivePoint) (b : montgomery.ProjectivePoint)
  (choice : subtle.Choice) :
  Result montgomery.ProjectivePoint :=
  montgomery.ConditionallySelectableProjectivePoint.conditional_select a b choice

/-- **Spec theorem for `montgomery.ConditionallySelectableProjectivePoint.conditional_assign_impl`**:
- No panic (if conditional_select succeeds)
- Returns the result of conditional_select(a, b, choice)
-/
@[progress]
theorem montgomery.ConditionallySelectableProjectivePoint.conditional_assign_impl_spec
  (a b : montgomery.ProjectivePoint) (choice : subtle.Choice)
  (h : ∃ res, montgomery.ConditionallySelectableProjectivePoint.conditional_select a b choice = ok res) :
  ∃ res,
    montgomery.ConditionallySelectableProjectivePoint.conditional_assign_impl a b choice = ok res ∧
    montgomery.ConditionallySelectableProjectivePoint.conditional_select a b choice = ok res := by
  unfold montgomery.ConditionallySelectableProjectivePoint.conditional_assign_impl
  obtain ⟨res, h_eq⟩ := h
  use res

/-- Implementation of `montgomery.ConditionallySelectableProjectivePoint.conditional_swap`:
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
def montgomery.ConditionallySelectableProjectivePoint.conditional_swap_impl
  (a : montgomery.ProjectivePoint) (b : montgomery.ProjectivePoint)
  (choice : subtle.Choice) :
  Result (montgomery.ProjectivePoint × montgomery.ProjectivePoint) := do
  let a_new ← montgomery.ConditionallySelectableProjectivePoint.conditional_select a b choice
  let b_new ← montgomery.ConditionallySelectableProjectivePoint.conditional_select b a choice
  ok (a_new, b_new)

/-- **Spec theorem for `montgomery.ConditionallySelectableProjectivePoint.conditional_swap_impl`**:
- No panic (if conditional_select succeeds)
- Returns (a_new, b_new) where:
  - a_new = conditional_select(a, b, choice)
  - b_new = conditional_select(b, a, choice)
- If choice = Choice.one: swaps a and b
- If choice = Choice.zero: leaves them unchanged
-/
@[progress]
theorem montgomery.ConditionallySelectableProjectivePoint.conditional_swap_impl_spec
  (a b : montgomery.ProjectivePoint) (choice : subtle.Choice)
  (h_a : ∃ res, montgomery.ConditionallySelectableProjectivePoint.conditional_select a b choice = ok res)
  (h_b : ∃ res, montgomery.ConditionallySelectableProjectivePoint.conditional_select b a choice = ok res) :
  ∃ c,
    montgomery.ConditionallySelectableProjectivePoint.conditional_swap_impl a b choice = ok c ∧
    montgomery.ConditionallySelectableProjectivePoint.conditional_select a b choice = ok c.1 ∧
    montgomery.ConditionallySelectableProjectivePoint.conditional_select b a choice = ok c.2 := by
  unfold montgomery.ConditionallySelectableProjectivePoint.conditional_swap_impl
  obtain ⟨a_new, h_a_eq⟩ := h_a
  obtain ⟨b_new, h_b_eq⟩ := h_b
  use (a_new, b_new)
  simp [h_a_eq, h_b_eq]

end curve25519_dalek
