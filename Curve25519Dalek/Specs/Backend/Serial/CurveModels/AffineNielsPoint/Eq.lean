/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq

/-! # Spec Theorem for `AffineNielsPoint::eq`

Specification and proof for
`curve25519_dalek::backend::serial::curve_models::{core::cmp::PartialEq<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint> for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::eq`.

This function compares two AffineNielsPoint values component-wise using
`FieldElement51` equality, short-circuiting on the first mismatch.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 182:26-182:35
-/

open Aeneas.Std Result Aeneas.Std.WP


/-
natural language description:

• Compares two AffineNielsPoint values by checking equality of
  y_plus_x, y_minus_x, and xy2d in that order.

• Uses FieldElement51 equality and returns false as soon as any comparison fails.

natural language specs:

• The function always succeeds (no panic)
• The result is true iff all three coordinate comparisons return true
-/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51

/-- Helper: the Bool `eq` returns true iff the canonical byte encodings are equal. -/
@[progress]
theorem eq_spec_aux (a b : backend.serial.u64.field.FieldElement51) :
    spec (eq a b) (fun r =>
    (r = true ↔ a.to_bytes = b.to_bytes)) := by
  unfold eq
  progress*
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp only [spec, theta, wp_return]
  have key : decide (c.val = 1#u8) = true ↔ c = Choice.one := by
    cases c with | mk val valid => simp [Choice.one]
  rw [key]
  exact c_post

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51

namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreCmpPartialEqAffineNielsPoint

/-- **Spec and proof concerning `AffineNielsPoint.Insts.CoreCmpPartialEqAffineNielsPoint.eq`**:
- No panic (always returns successfully)
- Returns true iff all three coordinate comparisons return true
- Short-circuits to false as soon as a comparison fails
-/
@[progress]
theorem eq_spec
    (self other : backend.serial.curve_models.AffineNielsPoint) :
    spec (eq self other) (fun b =>
    (b = true ↔
      self.y_plus_x.to_bytes = other.y_plus_x.to_bytes ∧
      self.y_minus_x.to_bytes = other.y_minus_x.to_bytes ∧
      self.xy2d.to_bytes = other.xy2d.to_bytes)) := by
  unfold eq
  progress as ⟨b, b_post⟩
  split
  · progress as ⟨b1, b1_post⟩
    split
    · progress as ⟨res, res_post⟩
      constructor
      · intro h; exact ⟨b_post.mp ‹_›, b1_post.mp ‹_›, res_post.mp h⟩
      · intro ⟨_, _, h3⟩; exact res_post.mpr h3
    · rename_i hb1
      simp only [spec_ok]
      constructor
      · intro h; exact absurd h Bool.false_ne_true
      · intro ⟨_, h2, _⟩; exact absurd (b1_post.mpr h2) (by omega)
  · rename_i hb
    simp only [spec_ok]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · intro ⟨h1, _⟩; exact absurd (b_post.mpr h1) (by omega)

end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreCmpPartialEqAffineNielsPoint
