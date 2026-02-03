/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs

/-! # ConditionalSelect

Specification for `MontgomeryPoint::conditional_select`.

This function returns, byte-wise, either `a` or `b` depending on the
constant-time `Choice` flag. At the byte level, it uses the array's
`ConditionallySelectable::conditional_select`, which returns the first
operand when `choice = 0` and the second operand when `choice = 1`.

**Source**: curve25519-dalek/src/montgomery.rs:L88-L90
-/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery.ConditionallySelectableMontgomeryPoint

/--
**Spec for `montgomery.ConditionallySelectableMontgomeryPoint.conditional_select`**:
- No panic (always returns successfully)
- For each byte i, the result byte equals `b[i]` when `choice = 1`,
  and equals `a[i]` when `choice = 0` (constant-time conditional select)
- Consequently, when `choice = Choice.one` (value 1), the whole result equals `b`;
  when `choice = Choice.zero` (value 0), the result equals `a`.

This implements constant-time conditional selection for Montgomery curve points,
where the points are represented as 32-byte arrays containing the u-coordinate.
-/
@[progress]
theorem conditional_select_spec
    (a b : montgomery.MontgomeryPoint)
    (choice : subtle.Choice) :
    ∃ res,
      conditional_select a b choice = ok res ∧
      (∀ i < 32,
        res[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!)) := by
  unfold conditional_select
  progress*
  grind

end curve25519_dalek.montgomery.ConditionallySelectableMontgomeryPoint
