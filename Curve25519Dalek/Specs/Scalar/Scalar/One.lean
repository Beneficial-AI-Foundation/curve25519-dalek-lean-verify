/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::ONE`

This constant represents the scalar value 1.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::ONE`**
• `ONE` is a compile-time constant; no panic is possible
• `ONE` encodes the scalar value 1
-/
@[simp]
theorem ONE_spec : U8x32_as_Nat ONE.bytes = 1 := by
  unfold ONE
  decide

end curve25519_dalek.scalar.Scalar
