/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Math.Edwards.Basepoint
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Ristretto.RistrettoPoint.Mul
import Curve25519Dalek.Specs.Constants.RISTRETTO_BASEPOINT_POINT

/-!
# Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::mul_base`

This function performs fixed-base scalar multiplication by the Ristretto base point.
It computes [scalar]b where b is the Ristretto basepoint (RISTRETTO_BASEPOINT_POINT).

The function is a specialized version of scalar multiplication that is optimized for
the case where the point being multiplied is the standard Ristretto generator. The
implementation delegates to the generic scalar multiplication trait
(`MulSharedAScalarRistrettoPointRistrettoPoint.mul`).

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.ristretto.RistrettoPoint

/-- **Spec theorem for `curve25519_dalek::ristretto::RistrettoPoint::mul_base`**
• The function always succeeds (no panic) for canonical input Scalars s
• The result is a valid RistrettoPoint
• result.toPoint equals the scalar multiple of the Edwards basepoint by U8x32_as_Nat s.bytes
-/
@[step]
theorem mul_base_spec (s : scalar.Scalar) (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255) :
    mul_base s ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat s.bytes) • _root_.Edwards.basepoint ⦄ := by
  unfold mul_base
    SharedAScalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint.mul
  let* ⟨ rp, rp_post1, rp_post2, rp_post3, rp_post4, rp_post5 ⟩ ←
    constants.RISTRETTO_BASEPOINT_POINT_spec
  step
  refine ⟨ by assumption , by grind ⟩

end curve25519_dalek.ristretto.RistrettoPoint
