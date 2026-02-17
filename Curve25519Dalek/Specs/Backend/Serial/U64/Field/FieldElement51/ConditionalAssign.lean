/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
/-! # ConditionalAssign

Specification for `FieldElement51::conditional_assign`.

This function conditionally assigns the limbs from `other` into `self`
depending on the constant-time `Choice` flag. At the limb level, it uses
`u64`'s `ConditionallySelectable::conditional_assign`, which is just a
conditional select: it returns the second operand when `choice = 1`, and
returns the first operand when `choice = 0`.

Source: curve25519-dalek/src/backend/serial/u64/field.rs (lines 250:4-256:5)
-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable

/-! ## Spec for `conditional_assign` -/

/--
**Spec for `backend.serial.u64.field.FieldElement51.conditional_assign`**:
- No panic (always returns successfully)
- For each limb i, the result limb equals `other[i]` when `choice = 1`,
  and equals `self[i]` when `choice = 0` (constant-time conditional select)
- Consequently, when `choice = Choice.one`, the whole result equals `other`;
  when `choice = Choice.zero`, the result equals `self`.
-/
@[progress]
theorem conditional_assign_spec
    (self other : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    spec (conditional_assign self other choice) (fun res =>
      (∀ i < 5,
        res[i]! = (if choice.val = 1#u8 then other[i]! else self[i]!))) := by
  unfold conditional_assign
  unfold U64.Insts.SubtleConditionallySelectable.conditional_assign
  unfold U64.Insts.SubtleConditionallySelectable.conditional_select
  sorry
  /- OLD PROOF (needs updating for WP spec form):
  by_cases h: choice.val = 1#u8
  · simp only [h, reduceIte, bind_tc_ok, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
    progress*
    intro i _
    interval_cases i; all_goals simp_all
  · simp only [h, reduceIte, bind_tc_ok, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
    progress*
  -/

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
