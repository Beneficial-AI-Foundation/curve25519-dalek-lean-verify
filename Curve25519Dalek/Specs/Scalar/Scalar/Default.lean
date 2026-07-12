/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Scalar.Scalar.Zero

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::default`

Returns the default value for a `Scalar`, which is `Scalar::ZERO` (the additive identity).

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreDefaultDefault

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::default`**
• The function always succeeds (no panic)
• The result satisfies `U8x32_as_Nat result.bytes = 0`
-/
@[step]
theorem default_spec :
    default ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes = 0 ⦄ := by
  unfold default
  step*
  exact Scalar.ZERO_spec

end curve25519_dalek.scalar.Scalar.Insts.CoreDefaultDefault
