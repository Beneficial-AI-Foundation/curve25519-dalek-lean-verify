/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation

/-! # Spec Theorems for `EdwardsPoint::mul`

Specifications and proofs for scalar multiplication of Edwards points.

Two trait implementations are covered here:

- `MulShared0EdwardsPointSharedAScalarEdwardsPoint.mul` — the core implementation:
  `&EdwardsPoint * &Scalar → EdwardsPoint`, delegating to `backend::variable_base_mul`.

- `MulShared0ScalarSharedAEdwardsPointEdwardsPoint.mul` — the commutative variant:
  `&Scalar * &EdwardsPoint → EdwardsPoint`, delegating to the above with swapped arguments.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.MulShared0EdwardsPointSharedAScalarEdwardsPoint

/-
natural language description:

• Takes a valid Edwards point (self : EdwardsPoint) and a canonical scalar (scalar : Scalar)
• Returns the scalar multiple [scalar]self, i.e., the point added to itself scalar times
• Delegates to backend.variable_base_mul

natural language specs:

• The function always succeeds (no panic) for valid input EdwardsPoints e and canonical Scalars s
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e., result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/

/-- **Spec and proof concerning `edwards.MulShared0EdwardsPointSharedAScalarEdwardsPoint.mul`**:
• The function always succeeds (no panic) for valid input EdwardsPoints e and canonical Scalars s
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e., result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/
@[progress]
theorem mul_spec (e : EdwardsPoint) (s : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat s.bytes < L)
    (h_e_valid : e.IsValid) :
    ∃ result, mul e s = ok result ∧
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint := by
  sorry

end curve25519_dalek.edwards.MulShared0EdwardsPointSharedAScalarEdwardsPoint

namespace curve25519_dalek.edwards.MulShared0ScalarSharedAEdwardsPointEdwardsPoint

/-
natural language description:

• Takes a canonical scalar (self : Scalar) and a valid Edwards point (point : EdwardsPoint)
• Returns the scalar multiple [self]point, i.e., the point added to itself self times
• This is the commutative variant (Scalar * Point rather than Point * Scalar);
  it simply delegates to MulShared0EdwardsPointSharedAScalarEdwardsPoint.mul
  with arguments swapped, so no independent computation takes place

natural language specs:

• The function always succeeds (no panic) for canonical input Scalars s and valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e., result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/

/-- **Spec and proof concerning `edwards.MulShared0ScalarSharedAEdwardsPointEdwardsPoint.mul`**:
• The function always succeeds (no panic) for canonical input Scalars s and valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result is mathematically correct, i.e., result.toPoint = e.toPoint + .. + e.toPoint (s-times)
-/
@[progress]
theorem mul_spec (s : scalar.Scalar) (e : EdwardsPoint)
    (h_s_canonical : U8x32_as_Nat s.bytes < L)
    (h_e_valid : e.IsValid) :
    ∃ result, mul s e = ok result ∧
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint :=
  curve25519_dalek.edwards.MulShared0EdwardsPointSharedAScalarEdwardsPoint.mul_spec e s h_s_canonical h_e_valid

end curve25519_dalek.edwards.MulShared0ScalarSharedAEdwardsPointEdwardsPoint
