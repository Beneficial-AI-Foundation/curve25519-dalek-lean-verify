/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect

/-! # Spec Theorem for `RistrettoPoint::conditional_select`

Specification and proof for the `ConditionallySelectable` trait implementation for `RistrettoPoint`.

This function conditionally selects between two Ristretto points based on a `Choice` value
by delegating to the underlying Edwards point conditional selection, which in turn applies
`FieldElement51::conditional_select` component-wise to the coordinates (X, Y, Z, T).

Returns `b` when `choice = 1` and `a` when `choice = 0`, in constant time.

**Source**: curve25519-dalek/src/ristretto.rs, lines 1192:4-1198:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable

/--
**Spec and proof concerning `ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable.conditional_select`**:
- No panic (always returns successfully)
- Given inputs:
  - RistrettoPoint `a` with coordinates (X, Y, Z, T),
  - RistrettoPoint `b` with coordinates (X', Y', Z', T'),
  - a Choice `choice`,
  the output RistrettoPoint has coordinates selected component-wise:
  - If choice = 1, each coordinate equals the corresponding one of `b`
  - If choice = 0, each coordinate equals the corresponding one of `a`
  - The operation is constant-time (does not branch on choice)
-/
@[progress]
theorem conditional_select_spec
    (a b : ristretto.RistrettoPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ result =>
    (∀ i < 5, result.X[i]! = (if choice.val = 1#u8 then b.X[i]! else a.X[i]!)) ∧
    (∀ i < 5, result.Y[i]! = (if choice.val = 1#u8 then b.Y[i]! else a.Y[i]!)) ∧
    (∀ i < 5, result.Z[i]! = (if choice.val = 1#u8 then b.Z[i]! else a.Z[i]!)) ∧
    (∀ i < 5, result.T[i]! = (if choice.val = 1#u8 then b.T[i]! else a.T[i]!)) ⦄ := by
  unfold conditional_select
  unfold edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_select
  progress*

end curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable
