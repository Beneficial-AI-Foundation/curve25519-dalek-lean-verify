/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.ScalarMul.VariableBase.Mul
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorems for `EdwardsPoint::mul`

Specifications and proofs for scalar multiplication of Edwards points.

Three trait implementations are covered here:

- `Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul` —
  the core implementation:
  `&EdwardsPoint * &Scalar → EdwardsPoint`, delegating to
  `backend::variable_base_mul`.

- `Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul` —
  the commutative variant: `&Scalar * &EdwardsPoint → EdwardsPoint`,
  delegating to the above with swapped arguments.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint

/-
natural language description:

• Takes a valid Edwards point (self : edwards.EdwardsPoint) and a canonical
  scalar (scalar : scalar.Scalar)
• Returns the scalar multiple [scalar]self, i.e., the point added to itself
  scalar times
• Delegates to backend.variable_base_mul

natural language specs:

• The function always succeeds (no panic) for valid input EdwardsPoints e
  and canonical Scalars s
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/

/-- **Spec and proof concerning
`Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul`**:
• The function always succeeds (no panic) for valid input EdwardsPoints e
  and canonical Scalars s
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/
@[step]
theorem mul_spec (e : edwards.EdwardsPoint) (s : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255)
    (h_e_valid : e.IsValid) :
    mul e s ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint ⦄ := by
  -- `U8x32_as_Nat < 2^255` forces the top byte to have a clear high bit
  -- (i.e., `s.bytes[31].val ≤ 127`), which is the precondition of
  -- `variable_base.mul_spec`.
  have h_top : (s.bytes[31]!).val ≤ 127 := by
    -- If `bytes[31] ≥ 128` then the top byte alone contributes `≥ 2^248 * 128 = 2^255`,
    -- contradicting `U8x32_as_Nat < 2^255`.
    by_contra h_neg
    push_neg at h_neg
    unfold U8x32_as_Nat at h_s_canonical
    rw [Finset.sum_range_succ] at h_s_canonical
    have h_high_ge : 2 ^ 255 ≤ 2 ^ (8 * 31) * (s.bytes[31]!).val := by
      calc 2 ^ 255 = 2 ^ (8 * 31) * 128 := by norm_num
        _ ≤ 2 ^ (8 * 31) * (s.bytes[31]!).val := Nat.mul_le_mul_left _ h_neg
    omega
  unfold mul backend.variable_base_mul backend.get_selected_backend
  simp only [step_simps]
  let* ⟨ result, result_valid, result_point ⟩ ←
    curve25519_dalek.backend.serial.scalar_mul.variable_base.mul_spec e h_e_valid s h_top
  refine ⟨result_valid, ?_⟩
  rw [result_point, natCast_zsmul]

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint

namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint

/-
natural language description:

• Takes a canonical scalar (self : scalar.Scalar) and a valid Edwards point
  (point : edwards.EdwardsPoint)
• Returns the scalar multiple [self]point, i.e., the point added to itself
  self times
• This is the commutative variant (Scalar * Point rather than Point * Scalar);
  it simply delegates to
  Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul
  with arguments swapped, so no independent computation takes place

natural language specs:

• The function always succeeds (no panic) for canonical input Scalars s and
  valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/

/-- **Spec and proof concerning
`Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul`**:
• The function always succeeds (no panic) for canonical input Scalars s and
  valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/
@[step]
theorem mul_spec (s : scalar.Scalar) (e : edwards.EdwardsPoint)
    (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255)
    (h_e_valid : e.IsValid) :
    mul s e ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint ⦄ := by
  exact Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul_spec
    e s h_s_canonical h_e_valid

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint

namespace curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint

/-
natural language description:

• Takes a valid Edwards point (self : edwards.EdwardsPoint) and a canonical
  scalar (rhs : scalar.Scalar)
• Returns the scalar multiple [rhs]self, i.e., the point added to itself rhs
  times
• This is the non-borrow variant (`&'a EdwardsPoint * Scalar` rather than
  `&EdwardsPoint * &Scalar`); it simply delegates to
  Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul
  with the same arguments, so no independent computation takes place

natural language specs:

• The function always succeeds (no panic) for valid input EdwardsPoints e
  and canonical Scalars s
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/

/-- **Spec and proof concerning
`SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul`**:
• The function always succeeds (no panic) for valid input EdwardsPoints e
  and canonical Scalars s
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/
@[step]
theorem mul_spec (e : edwards.EdwardsPoint) (s : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255)
    (h_e_valid : e.IsValid) :
      mul e s ⦃ result =>
      result.IsValid ∧
      result.toPoint = ((U8x32_as_Nat s.bytes)) • e.toPoint ⦄ := by
  exact curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul_spec
    s e h_s_canonical h_e_valid

end curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint

/-
natural language description:

• Takes a canonical scalar (self : scalar.Scalar) and a valid Edwards point
  (rhs : edwards.EdwardsPoint)
• Returns the scalar multiple [self]rhs, i.e., the point added to itself
  self times
• This is the fully non-borrow variant (`Scalar * EdwardsPoint` rather than
  `&Scalar * &EdwardsPoint`); it simply delegates to
  Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul
  with the same arguments, so no independent computation takes place

natural language specs:

• The function always succeeds (no panic) for canonical input Scalars s and
  valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/

/-- **Spec and proof concerning
`scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul`**:
• The function always succeeds (no panic) for canonical input Scalars s and
  valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e.,
  result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/
@[step]
theorem mul_spec (s : scalar.Scalar) (e : edwards.EdwardsPoint)
    (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255)
    (h_e_valid : e.IsValid) :
    mul s e ⦃ result =>
      result.IsValid ∧
      result.toPoint = ((U8x32_as_Nat s.bytes)) • e.toPoint ⦄ := by
  exact SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul_spec
    e s h_s_canonical h_e_valid


end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint
