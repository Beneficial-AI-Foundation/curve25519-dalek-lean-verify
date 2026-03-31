/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Scalar.Scalar.CtEq
/-! # Spec Theorem for `Scalar::eq`

Specification and proof for the `eq` (PartialEq) trait implementation for Scalar.

This function performs equality comparison for two Scalars by delegating
to constant-time equality (`ct_eq`) and converting the resulting `Choice` to `Bool`.
Two Scalars are considered equal when they have the same byte representation,
i.e., `self.bytes = other.bytes`.

**Source**: curve25519-dalek/src/scalar.rs (lines 295:4-297:5)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar

/-
natural language description:

• Takes two Scalars `self` and `other`
• Returns `true` if they have the same byte representation, `false` otherwise
• Implementation: delegates to `ct_eq` (constant-time equality) which compares
  the byte arrays of both scalars, then converts the `Choice` to `Bool`

natural language specs:

• The function always succeeds (no panic) for any input Scalars
• The result is `true` if and only if the two scalars have the same byte representation
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.CoreCmpPartialEqScalar.eq`**:
• The function always succeeds (no panic)
• The result is `true` if and only if the two scalars have the same byte representation
-/
@[step]
theorem eq_spec (self other : scalar.Scalar) :
    eq self other ⦃ result =>
    result = true ↔ self.bytes = other.bytes ⦄ := by
  unfold eq
  step*
  unfold Bool.Insts.CoreConvertFromChoice.from
  simp only [spec, theta, wp_return]
  have key : decide (c.val = 1#u8) = true ↔ c = Choice.one := by
    cases c with | mk val valid => simp [Choice.one]
  rw [key]
  exact c_post

end curve25519_dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar
