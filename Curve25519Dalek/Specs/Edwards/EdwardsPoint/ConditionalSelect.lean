/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect

/-! # Spec Theorem for `EdwardsPoint::conditional_select`

Specification and proof for the `ConditionallySelectable` trait implementation for `EdwardsPoint`.

This function conditionally selects between two Edwards points based on a `Choice` value
by applying `FieldElement51::conditional_select` component-wise to the coordinates (X, Y, Z, T).

Returns `b` when `choice = 1` and `a` when `choice = 0`, in constant time.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.EdwardsPoint.Insts.SubtleConditionallySelectable

/-
natural language description:

- Takes two EdwardsPoints `a` and `b` and a `Choice` value
- Returns one of the two points based on the choice, in constant time
- Implementation: applies `FieldElement51::conditional_select` component-wise
  to the coordinates (X, Y, Z, T)

natural language specs:

- The function always succeeds (no panic)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/

/--
**Spec and proof concerning `edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_select`**:
- No panic (always returns successfully)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/
@[progress]
theorem conditional_select_spec
    (a b : EdwardsPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : EdwardsPoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by
  sorry

end curve25519_dalek.edwards.EdwardsPoint.Insts.SubtleConditionallySelectable
