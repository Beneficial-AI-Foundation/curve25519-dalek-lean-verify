/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Mathlib.Tactic.IntervalCases

/-! # Spec theorem

Specification for
`curve25519_dalek::backend::serial::u64::field::FieldElement51::conditional_assign`.

This function conditionally assigns the limbs from `other` into `self` depending on the
constant-time `Choice` flag. At the limb level it uses `u64`'s
`ConditionallySelectable::conditional_assign`, which is simply a conditional select returning
the second operand when `choice = 1` and the first when `choice = 0`.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs#L250-L256"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable

/-- **Spec theorem**

Specification for
`curve25519_dalek::backend::serial::u64::field::FieldElement51::conditional_assign`.
• The function always succeeds (no panic)
• For each limb `i`, the result limb equals `other[i]` when `choice = 1`, and `self[i]`
  when `choice = 0` (constant-time conditional select)
• Consequently, when `choice = Choice.one`, the whole result equals `other`;
  when `choice = Choice.zero`, the result equals `self`.
-/
@[step]
theorem conditional_assign_spec (self other : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (res : FieldElement51) =>
      (∀ i < 5, res[i]! = (if choice.val = 1#u8 then other[i]! else self[i]!)) ⦄ := by
  unfold conditional_assign
  unfold U64.Insts.SubtleConditionallySelectable.conditional_assign
  by_cases hc : choice.val = 1#u8
  · simp only [hc, reduceIte]
    step*
    intro i _
    interval_cases i <;> simp [*]
  · simp only [hc, reduceIte]
    step*
    simp [*]

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
