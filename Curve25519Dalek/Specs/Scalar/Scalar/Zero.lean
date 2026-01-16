/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs

/-! # ZERO

Specification and proof for `Scalar::ZERO`.

This constant represents the scalar value 0.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result

namespace curve25519_dalek.scalar.Scalar

/-! ## Spec for `ZERO` -/

/-- **Spec for `scalar.Scalar.ZERO`**:

The ZERO constant represents the scalar 0.
-/
@[progress]
theorem ZERO_spec : ok ZERO ⦃ s => U8x32_as_Nat s.bytes = 0 ⦄ := by
  simp [ZERO, ZERO_body]

end curve25519_dalek.scalar.Scalar
