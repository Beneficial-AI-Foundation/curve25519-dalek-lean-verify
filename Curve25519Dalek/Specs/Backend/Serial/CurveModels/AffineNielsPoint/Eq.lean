/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
/-!
# Spec theorem for `AffineNielsPoint::eq`

Specification and proof for
`curve25519_dalek::backend::serial::curve_models::{core::cmp::PartialEq<
curve25519_dalek::backend::serial::curve_models::AffineNielsPoint> for
curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::eq`.

This function compares two AffineNielsPoint values component-wise using
`FieldElement51` equality, short-circuiting on the first mismatch.

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
namespace CoreCmpPartialEqFieldElement51

/-- Helper: the Bool `eq` returns true iff the canonical byte encodings are equal. -/
@[step]
theorem eq_spec_aux (a b : backend.serial.u64.field.FieldElement51) :
    eq a b ⦃ (r : Bool) =>
      r = true ↔ a.to_bytes = b.to_bytes ⦄ := by
  unfold eq
  step*
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp only [spec, theta, wp_return]
  have key : decide (c.val = 1#u8) = true ↔ c = Choice.one := by
    cases c with | mk val valid => simp [Choice.one]
  rw [key]
  exact c_post

end CoreCmpPartialEqFieldElement51
end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts

namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
namespace CoreCmpPartialEqAffineNielsPoint

/-- **Spec theorem for `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::eq`**
- No panic (always returns successfully)
- Returns true iff all three coordinate comparisons return true
- Short-circuits to false as soon as a comparison fails -/
@[step]
theorem eq_spec
    (self other : backend.serial.curve_models.AffineNielsPoint) :
    eq self other ⦃ (b : Bool) =>
      b = true ↔
        self.y_plus_x.to_bytes = other.y_plus_x.to_bytes ∧
        self.y_minus_x.to_bytes = other.y_minus_x.to_bytes ∧
        self.xy2d.to_bytes = other.xy2d.to_bytes ⦄ := by
  unfold eq
  let* ⟨ b, b_post ⟩ ← u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq_spec_aux
  spec_split
  · let* ⟨ b1, b1_post ⟩ ← u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq_spec_aux
    spec_split
    · let* ⟨ b, b_post ⟩ ← u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51.eq_spec_aux
      agrind
    · simp only [step_simps]
      agrind
  · simp only [step_simps]
    agrind

end CoreCmpPartialEqAffineNielsPoint
end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts
