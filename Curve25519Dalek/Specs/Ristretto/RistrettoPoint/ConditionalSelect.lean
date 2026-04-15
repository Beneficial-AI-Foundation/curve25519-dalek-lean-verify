/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.ConditionalSelect

/-!
# Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::conditional_select`

This function conditionally selects between two Ristretto points based on a `Choice` value
by delegating to the underlying Edwards point conditional selection, which in turn applies
`FieldElement51::conditional_select` component-wise to the coordinates (X, Y, Z, T).

Returns `b` when `choice = 1` and `a` when `choice = 0`, in constant time.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::conditional_select`**
• No panic (always returns successfully)
• Returns `b` when `choice = 1` and `a` when `choice = 0`
-/
@[step]
theorem conditional_select_spec (a b : RistrettoPoint) (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : RistrettoPoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by
  unfold conditional_select
  step
  assumption

end curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable
