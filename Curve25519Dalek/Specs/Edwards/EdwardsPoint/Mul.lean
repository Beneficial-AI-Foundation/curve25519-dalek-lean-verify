/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.ScalarMul.VariableBase.Mul

/-!
# Spec theorems for `EdwardsPoint::mul` and `Scalar::mul`

Scalar multiplication on Edwards points: given a valid Edwards point `P` and a
canonical scalar `s` (i.e., `s` represents a natural number less than `2^255`), the
result is `[s] P`, the elliptic curve group element obtained by adding `P` to itself
`s` times.

The Rust source defines four trait implementations of `core::ops::Mul` producing an
`EdwardsPoint`:

- `Mul<&Scalar> for &EdwardsPoint`: the core implementation, performing variable-base
  scalar multiplication via the selected backend.
- `Mul<&EdwardsPoint> for &Scalar`: the commutative variant, delegating to the core
  implementation with the operands swapped.
- `Mul<Scalar> for &EdwardsPoint`: a non-borrow variant on the right-hand operand,
  delegating to the core implementation.
- `Mul<EdwardsPoint> for Scalar`: the fully non-borrow variant, delegating to the
  commutative variant.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul`**
(trait impl `Mul<&Scalar> for &EdwardsPoint`).
• The function always succeeds (no panic) for a valid input EdwardsPoint `self` and a
  canonical Scalar `scalar`
• The result is a valid EdwardsPoint
• `result.toPoint` equals `(U8x32_as_Nat scalar.bytes) • self.toPoint`, i.e., scalar
  multiplication of `self.toPoint` by the natural number encoded by `scalar.bytes`
-/
@[step]
theorem mul_spec
    (self : edwards.EdwardsPoint) (scalar : scalar.Scalar)
    (h_scalar_canonical : U8x32_as_Nat scalar.bytes < 2 ^ 255)
    (h_self_valid : self.IsValid) :
    mul self scalar ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat scalar.bytes) • self.toPoint ⦄ := by
  -- `U8x32_as_Nat < 2^255` forces the top byte to have a clear high bit
  -- (i.e., `scalar.bytes[31].val ≤ 127`), which is the precondition of
  -- `variable_base.mul_spec`.
  have h_top : (scalar.bytes[31]!).val ≤ 127 := by
    -- If `bytes[31] ≥ 128` then the top byte alone contributes `≥ 2^248 * 128 = 2^255`,
    -- contradicting `U8x32_as_Nat < 2^255`.
    by_contra h_neg
    push Not at h_neg
    unfold U8x32_as_Nat at h_scalar_canonical
    rw [Finset.sum_range_succ] at h_scalar_canonical
    have h_high_ge : 2 ^ 255 ≤ 2 ^ (8 * 31) * (scalar.bytes[31]!).val := by
      calc 2 ^ 255 = 2 ^ (8 * 31) * 128 := by norm_num
        _ ≤ 2 ^ (8 * 31) * (scalar.bytes[31]!).val := Nat.mul_le_mul_left _ h_neg
    omega
  unfold mul backend.variable_base_mul backend.get_selected_backend
  simp only [step_simps]
  let* ⟨ result, result_valid, result_point ⟩ ←
    backend.serial.scalar_mul.variable_base.mul_spec self h_self_valid scalar h_top
  refine ⟨result_valid, ?_⟩
  rw [result_point, natCast_zsmul]

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint

namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::mul`**
(trait impl `Mul<&EdwardsPoint> for &Scalar`).
• The function always succeeds (no panic) for a canonical input Scalar `self` and a
  valid input EdwardsPoint `point`
• The result is a valid EdwardsPoint
• `result.toPoint` equals `(U8x32_as_Nat self.bytes) • point.toPoint`, i.e., scalar
  multiplication of `point.toPoint` by the natural number encoded by `self.bytes`
-/
@[step]
theorem mul_spec
    (self : scalar.Scalar) (point : edwards.EdwardsPoint)
    (h_self_canonical : U8x32_as_Nat self.bytes < 2 ^ 255)
    (h_point_valid : point.IsValid) :
    mul self point ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat self.bytes) • point.toPoint ⦄ := by
  exact Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul_spec
    point self h_self_canonical h_point_valid

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint

namespace curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul`**
(trait impl `Mul<Scalar> for &EdwardsPoint`).
• The function always succeeds (no panic) for a valid input EdwardsPoint `self` and a
  canonical Scalar `rhs`
• The result is a valid EdwardsPoint
• `result.toPoint` equals `(U8x32_as_Nat rhs.bytes) • self.toPoint`, i.e., scalar
  multiplication of `self.toPoint` by the natural number encoded by `rhs.bytes`
-/
@[step]
theorem mul_spec
    (self : edwards.EdwardsPoint) (rhs : scalar.Scalar)
    (h_rhs_canonical : U8x32_as_Nat rhs.bytes < 2 ^ 255)
    (h_self_valid : self.IsValid) :
    mul self rhs ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat rhs.bytes) • self.toPoint ⦄ := by
  exact Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul_spec
    rhs self h_rhs_canonical h_self_valid

end curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::mul`**
(trait impl `Mul<EdwardsPoint> for Scalar`).
• The function always succeeds (no panic) for a canonical input Scalar `self` and a
  valid input EdwardsPoint `rhs`
• The result is a valid EdwardsPoint
• `result.toPoint` equals `(U8x32_as_Nat self.bytes) • rhs.toPoint`, i.e., scalar
  multiplication of `rhs.toPoint` by the natural number encoded by `self.bytes`
-/
@[step]
theorem mul_spec
    (self : scalar.Scalar) (rhs : edwards.EdwardsPoint)
    (h_self_canonical : U8x32_as_Nat self.bytes < 2 ^ 255)
    (h_rhs_valid : rhs.IsValid) :
    mul self rhs ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat self.bytes) • rhs.toPoint ⦄ := by
  exact SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul_spec
    rhs self h_self_canonical h_rhs_valid

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint
