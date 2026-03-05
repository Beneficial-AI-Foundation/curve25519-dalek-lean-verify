/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.ConditionalSelect

/-! # Spec Theorem for `RistrettoPoint::conditional_select`

Specification and proof for the `ConditionallySelectable` trait implementation for `RistrettoPoint`.

This function conditionally selects between two Ristretto points based on a `Choice` value
by delegating to the underlying Edwards point conditional selection, which in turn applies
`FieldElement51::conditional_select` component-wise to the coordinates (X, Y, Z, T).

Returns `b` when `choice = 1` and `a` when `choice = 0`, in constant time.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable

/-
natural language description:

- Takes two RistrettoPoints `a` and `b` and a `Choice` value
- Returns one of the two points based on the choice, in constant time
- Implementation: delegates to `EdwardsPoint::conditional_select`, which applies
  `FieldElement51::conditional_select` component-wise to the coordinates (X, Y, Z, T)

natural language specs:

- The function always succeeds (no panic)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/

/--
**Spec and proof concerning `ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable.conditional_select`**:
- No panic (always returns successfully)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/
@[progress]
theorem conditional_select_spec
    (a b : RistrettoPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : RistrettoPoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by
  unfold conditional_select
  progress
  assumption

end curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable
