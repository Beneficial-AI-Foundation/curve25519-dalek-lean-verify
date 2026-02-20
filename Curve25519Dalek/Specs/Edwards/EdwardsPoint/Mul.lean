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

**Source**: curve25519-dalek/src/edwards.rs, lines 848-869
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.MulShared0EdwardsPointSharedAScalarEdwardsPoint

/-
natural language description:

• Takes a valid Edwards point (self : EdwardsPoint) and a canonical scalar (scalar : Scalar)
• Returns the scalar multiple [scalar]self, i.e., the point added to itself scalar times
• Delegates directly to backend.variable_base_mul, which implements variable-base
  scalar multiplication using a sliding-window lookup table and a double-and-add loop
  over the NAF (Non-Adjacent Form) representation of the scalar

natural language specs:

• The function always succeeds (no panic) for valid input EdwardsPoints e and canonical Scalars s
• The result is a valid EdwardsPoint
• The result equals [s]e, i.e., the mathematical scalar multiple of e by the integer
  s = U8x32_as_Nat s.bytes on the Ed25519 elliptic curve group

-/

/-- **Spec and proof concerning `edwards.MulShared0EdwardsPointSharedAScalarEdwardsPoint.mul`**:
• The function always succeeds (no panic) for canonical input Scalars s and valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result represents the scalar multiple [s]e on the Ed25519 curve
-/
@[progress]
theorem mul_spec (e : EdwardsPoint) (s : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat s.bytes < L)
    (h_e_valid : e.IsValid) :
    ∃ result, mul e s = ok result ∧
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint := by
  sorry

/-

Note on EdwardsPoint representation:

An EdwardsPoint is stored in extended homogeneous coordinates (X : Y : Z : T) with
the convention T = XY/Z, representing the affine point (X/Z, Y/Z) on the twisted
Edwards curve -x² + y² = 1 + dx²y².

The function e.toPoint maps an EdwardsPoint to its corresponding affine mathematical
Point Ed25519 via (X/Z, Y/Z), and returns the identity (= 0) if the point is invalid.

The postcondition

  result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint

thus asserts that the affine coordinates of the output point are exactly those of the
s-fold sum of the input point, where the group operation is addition on Ed25519.

-/

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
• The result equals [s]e, identical to the point-on-left variant

-/

/-- **Spec and proof concerning `edwards.MulShared0ScalarSharedAEdwardsPointEdwardsPoint.mul`**:
• The function always succeeds (no panic) for canonical input Scalars s and valid input EdwardsPoints e
• The result is a valid EdwardsPoint
• The result represents the scalar multiple [s]e on the Ed25519 curve,
  identical to the point-on-left variant since scalar multiplication is independent
  of argument order
-/
@[progress]
theorem mul_spec (s : scalar.Scalar) (e : EdwardsPoint)
    (h_s_canonical : U8x32_as_Nat s.bytes < L)
    (h_e_valid : e.IsValid) :
    ∃ result, mul s e = ok result ∧
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint := by
  unfold mul
  progress [MulShared0EdwardsPointSharedAScalarEdwardsPoint.mul_spec]

end curve25519_dalek.edwards.MulShared0ScalarSharedAEdwardsPointEdwardsPoint
