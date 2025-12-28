/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs

/-! # ConditionalSelect

Specification for `FieldElement51::conditional_select`.

This function returns, limb-wise, either `a` or `b` depending on the
constant-time `Choice` flag. At the limb level, it uses `u64`'s
`ConditionallySelectable::conditional_select`, which returns the first
operand when `choice = 0` and the second operand when `choice = 1`.

Source: curve25519-dalek/src/backend/serial/u64/field.rs (lines 228:4-240:5)
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.ConditionalSelect

/-! ## Spec for `conditional_select` -/

/--
**Spec for `backend.serial.u64.field.FieldElement51.conditional_select`**:
- No panic (always returns successfully)
- For each limb i, the result limb equals `b[i]` when `choice = 1`,
  and equals `a[i]` when `choice = 0` (constant-time conditional select)
- Consequently, when `choice = Choice.one`, the whole result equals `b`;
  when `choice = Choice.zero`, the result equals `a`.
-/
@[progress]
theorem conditional_select_spec
    (a b : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    ∃ res,
      backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select
        a b choice = ok res ∧
      (∀ i < 5,
        res[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!)) := by
  unfold backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select
  unfold subtle.ConditionallySelectableU64.conditional_select
  by_cases h: choice.val = 1#u8
  · simp only [h, reduceIte, bind_tc_ok, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
    progress*
    intro i _
    interval_cases i; all_goals simp_all [Array.make]
  · simp only [h, reduceIte, bind_tc_ok, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
    progress*
    intro i _
    interval_cases i; all_goals simp_all [Array.make]

end curve25519_dalek.backend.serial.u64.field.FieldElement51.ConditionalSelect
