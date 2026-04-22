/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::conditional_select`

This function returns, byte-wise, either `a` or `b` depending on the
constant-time `Choice` flag. At the byte level, it uses the array's
`ConditionallySelectable::conditional_select`, which returns the first
operand when `choice = 0` and the second operand when `choice = 1`.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::conditional_select`**
• No panic (always returns successfully)
• For each byte i, the result byte equals `b[i]` when `choice = 1`,
  and equals `a[i]` when `choice = 0` (constant-time conditional select)
-/
@[step]
theorem conditional_select_spec (a b : MontgomeryPoint) (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : MontgomeryPoint) =>
      ∀ i < 32,
        result[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!) ⦄ := by
  unfold conditional_select
  step*
  by_cases h : choice.val = 1#u8 <;> simp_all

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable
