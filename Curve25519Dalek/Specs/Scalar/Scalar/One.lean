/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Defs

/-! # ONE

Specification and proof for `Scalar::ONE`.

This constant represents the scalar value 1.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas.Std Result

namespace curve25519_dalek.scalar.Scalar

/-! ## Spec for `ONE` -/

/-- **Spec for `scalar.Scalar.ONE`**:

The ONE constant represents the scalar 1.
-/
theorem ONE_spec : U8x32_as_Nat ONE.bytes = 1 := by
  unfold ONE ONE_body
  decide

end curve25519_dalek.scalar.Scalar
