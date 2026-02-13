/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `AffineNielsPoint::assert_receiver_is_total_eq`

Specification and proof for
`curve25519_dalek::backend::serial::curve_models::{core::cmp::Eq for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::assert_receiver_is_total_eq`.

This function is the totality assertion required by Rust's `Eq` trait. For
`AffineNielsPoint`, it is a no-op and always succeeds.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs, lines 182:22-182:24
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.curve_models.EqAffineNielsPoint

/-(
natural language description:

• Takes an AffineNielsPoint and returns unit. This is the `Eq`-trait totality
  assertion and has no computational effect.

natural language specs:

• The function always succeeds (no panic)
• The output is Unit (no additional constraints)
-/

/-- **Spec and proof concerning `EqAffineNielsPoint.assert_receiver_is_total_eq`**:
- No panic (always returns successfully)
- The result is `()`
- This is the `Eq`-trait totality assertion for `AffineNielsPoint`
-/
@[progress]
theorem assert_receiver_is_total_eq_spec
    (self : backend.serial.curve_models.AffineNielsPoint) :
    ∃ result, assert_receiver_is_total_eq self = ok result ∧ result = () := by
  unfold assert_receiver_is_total_eq
  simp

end curve25519_dalek.backend.serial.curve_models.EqAffineNielsPoint
