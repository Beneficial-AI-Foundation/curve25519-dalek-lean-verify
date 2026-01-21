/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq

/-! # Spec Theorem for `AffineNielsPoint::eq`

Specification and proof for
`curve25519_dalek::backend::serial::curve_models::{core::cmp::PartialEq<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint> for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::eq`.

This function compares two AffineNielsPoint values component-wise using
`FieldElement51` equality, short-circuiting on the first mismatch.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 182:26-182:35
-/

open Aeneas.Std Result


/-
natural language description:

• Compares two AffineNielsPoint values by checking equality of
  y_plus_x, y_minus_x, and xy2d in that order.

• Uses FieldElement51 equality and returns false as soon as any comparison fails.

natural language specs:

• The function always succeeds (no panic)
• The result is true iff all three coordinate comparisons return true
-/

namespace curve25519_dalek.backend.serial.curve_models.PartialEqAffineNielsPointAffineNielsPoint

/-- **Spec and proof concerning `PartialEqAffineNielsPointAffineNielsPoint.eq`**:
- No panic (always returns successfully)
- Returns true iff all three coordinate comparisons return true
- Short-circuits to false as soon as a comparison fails
-/
@[progress]
theorem eq_spec
    (self other : backend.serial.curve_models.AffineNielsPoint) :
    ∃ b, eq self other = ok b ∧
    (b = true ↔
      field.PartialEqFieldElement51FieldElement51.eq self.y_plus_x other.y_plus_x = ok true ∧
      field.PartialEqFieldElement51FieldElement51.eq self.y_minus_x other.y_minus_x = ok true ∧
      field.PartialEqFieldElement51FieldElement51.eq self.xy2d other.xy2d = ok true) := by
  unfold eq field.PartialEqFieldElement51FieldElement51.eq
  progress*
  unfold subtle.FromBoolChoice.from
  progress*
  by_cases h0 : c.val = 1#u8
  all_goals simp_all

end curve25519_dalek.backend.serial.curve_models.PartialEqAffineNielsPointAffineNielsPoint
