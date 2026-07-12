/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.GetSelectedBackend
import Curve25519Dalek.Specs.Backend.Serial.ScalarMul.VariableBase.Mul

/-!
# Spec theorem for `curve25519_dalek::backend::variable_base_mul`

Performs constant-time, variable-base scalar multiplication `[s]P` on the Ed25519 curve,
where `s` is a `Scalar` and `P` is an `EdwardsPoint`. The implementation dispatches to the
selected backend; in the serial-only build (no SIMD features), this unconditionally delegates
to `backend::serial::scalar_mul::variable_base::mul`.

Source: "curve25519-dalek/src/backend/mod.rs", lines 253–263
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend

/-- **Spec theorem for `curve25519_dalek::backend::variable_base_mul`**
• The function always succeeds (no panic) for a valid input `EdwardsPoint` and a
  `Scalar` whose top byte satisfies `scalar.bytes[31] ≤ 127`
• The result is a valid `EdwardsPoint`
• `result.toPoint` equals `(U8x32_as_Nat scalar.bytes) • point.toPoint`, i.e., scalar
  multiplication of `point.toPoint` by the natural number encoded by `scalar.bytes`
-/
@[step]
theorem variable_base_mul_spec
    (point : edwards.EdwardsPoint) (scalar : scalar.Scalar)
    (h_point_valid : point.IsValid)
    (h_top : (scalar.bytes[31]!).val ≤ 127) :
    variable_base_mul point scalar ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = ((U8x32_as_Nat scalar.bytes : ℕ) : ℤ) • point.toPoint ⦄ := by
  unfold variable_base_mul
  step*

end curve25519_dalek.backend
