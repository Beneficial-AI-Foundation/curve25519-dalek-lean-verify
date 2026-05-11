/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::ZERO`

This constant represents the scalar value 0.

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::ZERO`**
• The natural-number interpretation of the ZERO constant equals 0.
-/
@[simp]
theorem ZERO_spec : Scalar52_as_Nat ZERO = 0 := by
  unfold ZERO
  decide

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
