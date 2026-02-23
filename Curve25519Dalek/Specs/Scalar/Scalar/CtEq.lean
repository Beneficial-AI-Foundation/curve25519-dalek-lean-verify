/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `Scalar.Insts.SubtleConstantTimeEq.ct_eq`

Specification and proof for `Scalar.Insts.SubtleConstantTimeEq.ct_eq`.

This function performs constant-time equality comparison.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.SubtleConstantTimeEq

/-
natural language description:

    • Compares two scalar types s and s' to determine whether they are equal or not.

    • Crucially does so in constant time irrespective of the inputs as to avoid security liabilities.

natural language specs:

    • s.bytes = s'.bytes \iff Choice = True
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully)
- Returns `Choice` representing equality in constant time
- The result is Choice.one (true) if and only if the two scalars are equal (same byte representation)
-/
@[progress]
theorem ct_eq_spec (s s' : scalar.Scalar) :
    ct_eq s s' ⦃ c =>
    c = Choice.one ↔ s.bytes = s'.bytes ⦄ := by
  unfold ct_eq
  repeat progress
  constructor
  · -- BEGIN TASK
    intro _
    have : s.bytes.to_slice = s'.bytes.to_slice := by grind
    simp only [Array.to_slice, Slice.eq_iff] at *
    exact Subtype.eq this
    -- END TASK
  · -- BEGIN TASK
    grind
    -- END TASK

end curve25519_dalek.scalar.Scalar.Insts.SubtleConstantTimeEq
