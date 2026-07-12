/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Mathlib.Tactic

/-!
# Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::conditional_swap`

Conditionally swaps two `FieldElement51` values in constant time. If `choice = 1`, swaps `a`
and `b`; otherwise leaves them unchanged. The implementation swaps each of the five `u64` limbs
independently via `u64::conditional_swap`, which is itself built on two `conditional_select`
calls.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs", lines 242–248
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace SubtleConditionallySelectable

/-- **Spec theorem for
`curve25519_dalek::backend::serial::u64::field::FieldElement51::conditional_swap`**
• The function always succeeds (no panic)
• For each limb `i`, `res.1[i]` equals `b[i]` when `choice = 1` and `a[i]` when `choice = 0`
• For each limb `i`, `res.2[i]` equals `a[i]` when `choice = 1` and `b[i]` when `choice = 0`
• Consequently, when `choice = Choice.one` the result is `(b, a)`;
  when `choice = Choice.zero` the result is `(a, b)`.
-/
@[step]
theorem conditional_swap_spec
    (a b : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    conditional_swap a b choice ⦃
      (res : FieldElement51 × FieldElement51) =>
      (∀ i < 5, res.1[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!)) ∧
      (∀ i < 5, res.2[i]! = (if choice.val = 1#u8 then a[i]! else b[i]!)) ⦄ := by
  unfold conditional_swap
  unfold U64.Insts.SubtleConditionallySelectable.conditional_swap
  unfold U64.Insts.SubtleConditionallySelectable.conditional_select
  by_cases hc : choice.val = 1#u8
  · simp only [hc, reduceIte, bind_tc_ok]
    step*
    constructor
    · intro i hi; interval_cases i <;> simp [*]
    · intro i hi; interval_cases i <;> simp [*]
  · simp only [hc, reduceIte, bind_tc_ok]
    step*
    constructor
    · intro i hi; interval_cases i <;> simp [*]
    · intro i hi; interval_cases i <;> simp [*]

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
