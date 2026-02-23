/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation

/-! # Spec Theorem for `RistrettoPoint::mul`

Specification and proof for scalar multiplication of Ristretto points.

This function performs scalar multiplication on a Ristretto point by a scalar value.
It computes [scalar]P where P is a RistrettoPoint.

The function delegates to the underlying Edwards point scalar multiplication.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint

/-
natural language description:

• Takes a scalar value (self : Scalar) and a Ristretto point (point : RistrettoPoint)
• Returns the scalar multiple [self]point, i.e., the point added to itself self times
• Delegates to edwards.MulSharedAScalarEdwardsPointEdwardsPoint.mul since RistrettoPoint
  is represented as an underlying EdwardsPoint

natural language specs:

• The function always succeeds (no panic) for canonical input Scalars s and valid input RistrettoPoints r
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times

-/

/-- **Spec and proof concerning `ristretto.MulShared0ScalarSharedARistrettoPointRistrettoPoint.mul`**:
• The function always succeeds (no panic) for canonical input Scalars s and valid input RistrettoPoints r
• The result is a valid RistrettoPoint
• The result = r + ... + r represents the input RistrettoPoint r added to itself s-times
-/
@[progress]
theorem mul_spec (s : scalar.Scalar) (r : ristretto.RistrettoPoint)
    (h_s_canonical : U8x32_as_Nat s.bytes < L)
    (h_rist_valid : r.IsValid) :
    mul s r ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • r.toPoint ⦄ := by
  sorry

/-

Note:

One RistrettoPoint r corresponds to an equivalence class of several
mathematical curve points.

The command r.toPoint thus maps r to one of these concrete representatives on the curve (to the representative
that currently just so happens to represent r).

The equation

result.toPoint = (U8x32_as_Nat s.bytes) • r.toPoint

thus assures that the concrete representative of the input RistrettoPoints r on the curve sums up to
the concrete representative of the output Ristretto point on the curve if mathematically added to itself s times.
Since the addition on RistrettoPoints is mathematically well-defined (i.e., it does not depend on the choice of representatives), the condition

result.toPoint = (U8x32_as_Nat s.bytes) • r.toPoint

thus indeed implies that the output RistrettoPoint (seen as an equivalence class) is the mathematically correct sum
of r + ... + r (s-times), even though we are only working at the level of (fairly arbitrary) representatives.

The fact that the addition of RistrettoPoints is indeed well-defined and does not depend on the chosen
representatives follows from standard results in abstract algebra: in any set of left cosets G/N, the product

(aN)(bN)=(ab)N

constitutes a well-defined operation that does not depend on the chosen representatives a, b iff N is a normal subgroup;
and in an Abelian group (our elliptic curve group is Abelian), every subgroup is normal.

-/

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint
