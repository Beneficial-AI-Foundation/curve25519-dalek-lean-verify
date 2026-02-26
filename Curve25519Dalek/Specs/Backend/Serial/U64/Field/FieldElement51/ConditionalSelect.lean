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

open Aeneas Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable

/-! ## Spec for `conditional_select` -/

/--
**Spec for `backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable.conditional_select`**:
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
    conditional_select a b choice ⦃ res =>
      ∀ i < 5,
        res[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!) ⦄ := by
  unfold conditional_select
  unfold U64.Insts.SubtleConditionallySelectable.conditional_select
  by_cases h: choice.val = 1#u8
  · simp only [h, ite_true, bind_tc_ok]
    progress*
    intro i hi
    subst_vars
    simp only [Array.getElem!_Nat_eq, Array.make, List.getElem!_eq_getElem?_getD]
    rcases i with _ | _ | _ | _ | _ | n <;> simp_all; omega
  · simp only [h, ite_false, bind_tc_ok]
    progress*
    intro i hi
    subst_vars
    simp only [Array.getElem!_Nat_eq, Array.make, List.getElem!_eq_getElem?_getD]
    rcases i with _ | _ | _ | _ | _ | n <;> simp_all; omega

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable
