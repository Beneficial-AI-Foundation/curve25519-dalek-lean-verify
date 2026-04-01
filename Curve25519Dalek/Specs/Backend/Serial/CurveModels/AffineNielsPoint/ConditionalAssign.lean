/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
/-! # Spec Theorem for `AffineNielsPoint::conditional_assign`

Specification and proof for `AffineNielsPoint::conditional_assign`.

This function conditionally assigns the value of another AffineNielsPoint
to self based on a Choice value. It is a constant-time operation used in
cryptographic implementations to avoid timing side-channels.

Given:
- an AffineNielsPoint `self` with coordinates (y_plus_x, y_minus_x, xy2d),
- an AffineNielsPoint `other` with coordinates (y_plus_x', y_minus_x', xy2d'),
- a Choice `choice` (which is either 0 or 1),

it updates `self` such that:
- if choice == 1: self = other (all coordinates are replaced)
- if choice == 0: self remains unchanged

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 322:4-326:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace SubtleConditionallySelectable

/-- **Spec and proof concerning
`backend.serial.curve_models.ConditionallySelectableAffineNielsPoint.conditional_assign`**:
- No panic (always returns successfully)
- Given inputs:
  • an AffineNielsPoint `self` with coordinates (y_plus_x, y_minus_x, xy2d),
  • an AffineNielsPoint `other` with coordinates (y_plus_x', y_minus_x', xy2d'),
  • a Choice `choice`,
the output AffineNielsPoint computed by `conditional_assign self other choice` satisfies:
- Each coordinate is conditionally selected: if choice is 1, output = other;
  if choice is 0, output = self
- The operation is performed in constant time for all field elements
-/
theorem conditional_assign_spec
    (self other : backend.serial.curve_models.AffineNielsPoint)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ result =>
    (∀ i < 5, result.y_plus_x[i]!.val =
      if choice.val = 1#u8 then other.y_plus_x[i]!.val else self.y_plus_x[i]!.val) ∧
    (∀ i < 5, result.y_minus_x[i]!.val =
      if choice.val = 1#u8 then other.y_minus_x[i]!.val else self.y_minus_x[i]!.val) ∧
    (∀ i < 5, result.xy2d[i]!.val =
      if choice.val = 1#u8 then other.xy2d[i]!.val else self.xy2d[i]!.val) ⦄ := by
  unfold conditional_assign
  step*
  grind

end SubtleConditionallySelectable
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
