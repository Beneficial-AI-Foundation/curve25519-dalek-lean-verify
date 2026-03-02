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

private theorem Array.to_slice_injective {self : Type} {n : Usize} {A B : Array self n}
    (h : A.to_slice = B.to_slice) : A = B := by
  grind [Subtype.ext]

/-- **Spec and proof concerning `scalar.Scalar.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully)
- Returns `Choice` representing equality in constant time
- The result is Choice.one (true) if and only if the two scalars are equal (same byte representation)
-/
@[progress]
theorem ct_eq_spec (self other : scalar.Scalar) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c = Choice.one ↔ self.bytes = other.bytes ⦄ := by
  unfold ct_eq
  progress*
  constructor
  · grind [Array.to_slice_injective]
  · grind

end curve25519_dalek.scalar.Scalar.Insts.SubtleConstantTimeEq
