/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar * RistrettoPoint`

Specification and proof for scalar multiplication of Ristretto points.

This function performs scalar multiplication on a Ristretto point by a scalar value.
It computes [scalar]P where P is a RistrettoPoint.

The function delegates to the underlying Edwards point scalar multiplication.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.MulShared0ScalarSharedARistrettoPointRistrettoPoint

/-
natural language description:

• Takes a scalar value (self : Scalar) and a Ristretto point (point : RistrettoPoint)
• Returns the scalar multiple [self]point, i.e., the point added to itself self times
• Delegates to edwards.MulSharedAScalarEdwardsPointEdwardsPoint.mul since RistrettoPoint
  is represented as an underlying EdwardsPoint

natural language specs:

• The function always succeeds (no panic) for valid scalar and point inputs
• Returns a valid RistrettoPoint that is the result of adding the input point self times to itself via
  elliptic curve addition
-/

/-- **Spec and proof concerning `ristretto.MulShared0ScalarSharedARistrettoPointRistrettoPoint.mul`**:
• The function always succeeds (no panic) for valid scalar and point inputs
• Returns a valid RistrettoPoint that is the result of adding the input point self times to itself via
  elliptic curve addition
-/
@[progress]
theorem mul_spec (self : scalar.Scalar) (point : ristretto.RistrettoPoint)

    (h_scalar_bounds : ∀ i < 5,
      self.bytes[i]!.val < 2 ^ 52)

    (h_point_bounds : ∀ i < 5,
      point.X[i]!.val < 2 ^ 53 ∧
      point.Y[i]!.val < 2 ^ 53 ∧
      point.Z[i]!.val < 2 ^ 53 ∧
      point.T[i]!.val < 2 ^ 53)

    (h_point_Z_nonzero : Field51_as_Nat point.Z % p ≠ 0) :

    ∃ result, mul self point = ok result ∧

    -- The computation delegates to Edwards point scalar multiplication
    ∃ ep_result,
      edwards.MulSharedAScalarEdwardsPointEdwardsPoint.mul self point = ok ep_result ∧
      result = ep_result ∧

    -- Bounds on the resulting point
    (∀ i < 5,
      result.X[i]!.val < 2 ^ 54  ∧
      result.Y[i]!.val < 2 ^ 54  ∧
      result.Z[i]!.val < 2 ^ 54  ∧
      result.T[i]!.val < 2 ^ 54) ∧

    -- The result Z coordinate is non-zero (valid projective point)
    Field51_as_Nat result.Z % p ≠ 0 := by
  sorry

end curve25519_dalek.ristretto.MulShared0ScalarSharedARistrettoPointRistrettoPoint
