/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
/-!
# Spec theorem for `ProjectiveNielsPoint::conditional_assign`

This function conditionally assigns the value of another ProjectiveNielsPoint
to self based on a Choice value. It is a constant-time operation used in
cryptographic implementations to avoid timing side-channels.

Given:
- a ProjectiveNielsPoint `self` with coordinates (Y_plus_X, Y_minus_X, Z, T2d),
- a ProjectiveNielsPoint `other` with coordinates (Y_plus_X', Y_minus_X', Z', T2d'),
- a Choice `choice` (which is either 0 or 1),

it updates `self` such that:
- if choice == 1: self = other (all coordinates are replaced)
- if choice == 0: self remains unchanged

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 305:4-310:5"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models
namespace curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable

/-
natural language description:

• Takes a ProjectiveNielsPoint self = (Y_plus_X, Y_minus_X, Z, T2d) and another
  ProjectiveNielsPoint other = (Y_plus_X', Y_minus_X', Z', T2d'), along with a
  Choice value, and conditionally assigns other to self in constant time.

natural language specs:

• The function always succeeds (no panic)
• Given inputs self = (Y_plus_X, Y_minus_X, Z, T2d), other = (Y_plus_X', Y_minus_X', Z', T2d'),
  and choice, the output self' = (Y_plus_X'', Y_minus_X'', Z'', T2d'') satisfies:
  - If choice represents 1 (true):
    Y_plus_X'' = Y_plus_X', Y_minus_X'' = Y_minus_X', Z'' = Z', T2d'' = T2d'
  - If choice represents 0 (false):
    Y_plus_X'' = Y_plus_X, Y_minus_X'' = Y_minus_X, Z'' = Z, T2d'' = T2d
  - The operation is constant-time (execution time does not depend on choice value)
-/

/-- **Spec theorem for
`backend.serial.curve_models.ConditionallySelectableProjectiveNielsPoint.conditional_assign`**
- No panic (always returns successfully)
- Given inputs:
  • a ProjectiveNielsPoint `self` with coordinates (Y_plus_X, Y_minus_X, Z, T2d),
  • a ProjectiveNielsPoint `other` with coordinates (Y_plus_X', Y_minus_X', Z', T2d'),
  • a Choice `choice`,
the output ProjectiveNielsPoint computed by `conditional_assign self other choice` satisfies:
- Each coordinate is conditionally selected:
  if choice is 1, output = other; if choice is 0, output = self
- The operation is performed in constant time for all field elements -/
@[step]
theorem conditional_assign_spec
    (self other : backend.serial.curve_models.ProjectiveNielsPoint)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (result : ProjectiveNielsPoint) =>
      (∀ i < 5, result.Y_plus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_plus_X[i]!.val else self.Y_plus_X[i]!.val) ∧
      (∀ i < 5, result.Y_minus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_minus_X[i]!.val else self.Y_minus_X[i]!.val) ∧
      (∀ i < 5, result.Z[i]!.val =
        if choice.val = 1#u8 then other.Z[i]!.val else self.Z[i]!.val) ∧
      (∀ i < 5, result.T2d[i]!.val =
        if choice.val = 1#u8 then other.T2d[i]!.val else self.T2d[i]!.val) ⦄ := by
  unfold conditional_assign
  step*
  -- grind closes the remaining four conditional-equality goals after step*
  grind

/-- **Point-level wrapper for `ProjectiveNielsPoint::conditional_assign`**:
Given valid `self` and `other` and a `Choice`, the output is a valid `ProjectiveNielsPoint`
whose `toPoint` equals `other.toPoint` if `choice.val = 1#u8`, otherwise `self.toPoint`.

Derived from the Field51-level `conditional_assign_spec` by lifting per-limb val equality
to term equality via `UScalar.eq_of_val_eq` + `fe_eq_of_limbs`, then case-splitting on
the `Choice`'s `valid` field. -/
@[step]
theorem conditional_assign_point
    (self other : ProjectiveNielsPoint)
    (h_self : self.IsValid) (h_other : other.IsValid)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (result : ProjectiveNielsPoint) =>
      result.IsValid ∧
      result.toPoint = (if choice.val = 1#u8 then other.toPoint else self.toPoint) ⦄ := by
  let* ⟨ r, r_post1, r_post2, r_post3, r_post4 ⟩ ← conditional_assign_spec
  -- Case-split on the Choice's `valid` field: choice.val ∈ {0#u8, 1#u8}.
  rcases choice.valid with hc0 | hc1
  · -- choice.val = 0#u8 → result = self.
    have hne : ¬ (choice.val = 1#u8) := by rw [hc0]; decide
    simp only [hne, if_false] at r_post1 r_post2 r_post3 r_post4 ⊢
    have h_ypx : r.Y_plus_X = self.Y_plus_X := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post1 i hi))
    have h_ymx : r.Y_minus_X = self.Y_minus_X := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post2 i hi))
    have h_z : r.Z = self.Z := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post3 i hi))
    have h_t2d : r.T2d = self.T2d := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post4 i hi))
    have hr_eq : r = self := by
      cases r; cases self; simp_all
    rw [hr_eq]
    exact ⟨h_self, rfl⟩
  · -- choice.val = 1#u8 → result = other.
    simp only [hc1, if_true] at r_post1 r_post2 r_post3 r_post4 ⊢
    have h_ypx : r.Y_plus_X = other.Y_plus_X := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post1 i hi))
    have h_ymx : r.Y_minus_X = other.Y_minus_X := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post2 i hi))
    have h_z : r.Z = other.Z := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post3 i hi))
    have h_t2d : r.T2d = other.T2d := fe_eq_of_limbs
      (fun i hi => UScalar.eq_of_val_eq (r_post4 i hi))
    have hr_eq : r = other := by
      cases r; cases other; simp_all
    rw [hr_eq]
    exact ⟨h_other, rfl⟩

end curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable
