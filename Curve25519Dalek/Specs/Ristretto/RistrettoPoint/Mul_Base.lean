/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Ristretto.RistrettoPoint.Mul
import Curve25519Dalek.Specs.Constants.RISTRETTO_BASEPOINT_POINT

/-! # Spec Theorem for `RistrettoPoint::mul_base`

Specification and proof for `RistrettoPoint::mul_base`.

This function performs fixed-base scalar multiplication by the Ristretto base point.
It computes [scalar]b where b is the Ristretto basepoint (RISTRETTO_BASEPOINT_POINT).

The function is a specialized version of scalar multiplication that is optimized for
the case where the point being multiplied is the standard Ristretto generator.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a scalar value s and multiplies it by the Ristretto basepoint
• Mathematically computes b + ... + b (s-times) where b = constants.RISTRETTO_BASEPOINT_POINT
• This is equivalent to scalar multiplication: s * RISTRETTO_BASEPOINT_POINT
• The operation delegates to the generic scalar multiplication trait implementation
  (MulSharedAScalarRistrettoPointRistrettoPoint.mul)

natural language specs:

• The function always succeeds (no panic) for canonical input Scalars s
• The result is a valid RistrettoPoint
• The result = b + ... + b represents the Ristretto basepoint b added to itself s-times
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.mul_base`**:
• The function always succeeds (no panic) for canonical input Scalars s
• The result is a valid RistrettoPoint
• The result = b + ... + b represents the Ristretto basepoint b added to itself s-times
-/
@[progress]
theorem mul_base_spec (s : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat s.bytes < L) :
    mul_base s ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • constants.RISTRETTO_BASEPOINT_POINT.toPoint ⦄ := by
  unfold mul_base SharedAScalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint.mul
  have h_basepoint_valid := constants.RISTRETTO_BASEPOINT_POINT_spec.2.1
  progress*

end curve25519_dalek.ristretto.RistrettoPoint
