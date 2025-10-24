/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Defs

/-! # ZERO

Specification and proof for `Scalar52::ZERO`.

This constant represents the scalar value 0.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-! ## Spec for `ZERO` -/

/-- **Spec for `backend.serial.u64.scalar.Scalar52.ZERO`**:

The ZERO constant represents the scalar 0.
-/
@[simp]
theorem ZERO_spec : U64x5_as_Nat ZERO = 0 := by
  unfold ZERO ZERO_body
  decide

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
