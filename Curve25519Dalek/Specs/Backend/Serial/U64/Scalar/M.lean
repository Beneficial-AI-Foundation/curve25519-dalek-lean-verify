/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Theodore Ehrenborg, Liao Zhang
-/
import Curve25519Dalek.Funs

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::m`

This helper widens two `u64` operands to `u128` and multiplies them, providing a non-truncating
multiplication primitive used throughout the Scalar52 routines.

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
open backend.serial.u64.scalar
namespace curve25519_dalek.backend.serial.u64.scalar

attribute [-simp] Int.reducePow Nat.reducePow

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::m`**
• The function always succeeds (no panic)
• `result.val = x.val * y.val`, i.e. the exact `u128` product of `x` and `y`
-/
@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (result : U128) => result.val = x.val * y.val ⦄ := by
  unfold m
  step*

end curve25519_dalek.backend.serial.u64.scalar
