/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::ZERO`

This constant represents the scalar value 0.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::ZERO`**
• `U8x32_as_Nat ZERO.bytes = 0`
-/
@[simp]
theorem ZERO_spec : U8x32_as_Nat ZERO.bytes = 0 := by
  unfold ZERO
  decide

end curve25519_dalek.scalar.Scalar
