/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Proofs.Defs

/-! # ZERO

Specification and proof for `Scalar::ZERO`.

This constant represents the scalar value 0.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas.Std Result

namespace curve25519_dalek.scalar.Scalar

/-! ## Spec for `ZERO` -/

/-- **Spec for `scalar.Scalar.ZERO`**:

The ZERO constant represents the scalar 0.
-/
@[simp]
theorem ZERO_spec : U8x32_as_Nat ZERO.bytes = 0 := by
  unfold ZERO ZERO_body
  decide

end curve25519_dalek.scalar.Scalar
