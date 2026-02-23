/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect




/-! # Spec Theorem for `AffineNielsPoint::conditional_select`

Specification and proof for `AffineNielsPoint::conditional_select`.

This function conditionally selects between two AffineNielsPoint values
based on a Choice flag. It is implemented by applying
`FieldElement51::conditional_select` component-wise to the coordinates
(y_plus_x, y_minus_x, xy2d), returning `b` when choice = 1 and `a` when
choice = 0, in constant time.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 315:4-321:5
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable

/--
**Spec and proof concerning `backend.serial.curve_models.AffineNielsPoint.conditional_select`**:
- No panic (always returns successfully)
- Given inputs:
  • AffineNielsPoint `a` with coordinates (y_plus_x, y_minus_x, xy2d),
  • AffineNielsPoint `b` with coordinates (y_plus_x', y_minus_x', xy2d'),
  • a Choice `choice`,
  the output AffineNielsPoint has coordinates selected component-wise:
  - If choice = 1, each coordinate equals the corresponding one of `b`
  - If choice = 0, each coordinate equals the corresponding one of `a`
  - The operation is constant-time (does not branch on choice)
-/
theorem conditional_select_spec
    (a b : backend.serial.curve_models.AffineNielsPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ result =>
    (∀ i < 5, result.y_plus_x[i]!.val =
      if choice.val = 1#u8 then b.y_plus_x[i]!.val else a.y_plus_x[i]!.val) ∧
    (∀ i < 5, result.y_minus_x[i]!.val =
      if choice.val = 1#u8 then b.y_minus_x[i]!.val else a.y_minus_x[i]!.val) ∧
    (∀ i < 5, result.xy2d[i]!.val =
      if choice.val = 1#u8 then b.xy2d[i]!.val else a.xy2d[i]!.val) ⦄ := by
  unfold conditional_select
  progress*
  grind

end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable
