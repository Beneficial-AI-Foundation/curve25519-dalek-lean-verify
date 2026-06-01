/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::ct_eq`

• Compares two scalars `self` and `other` to determine whether they are equal.
• Operates in constant time regardless of the input values, preventing timing side-channel attacks.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.SubtleConstantTimeEq

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::ct_eq`**
• No panic (always returns successfully)
• The result is `Choice.one` iff the two scalars have identical byte representations
-/
@[step]
theorem ct_eq_spec (self other : scalar.Scalar) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c = Choice.one ↔ self.bytes = other.bytes ⦄ := by
  unfold ct_eq
  step*
  constructor
  · grind [Subtype.ext]
  · grind

end curve25519_dalek.scalar.Scalar.Insts.SubtleConstantTimeEq
