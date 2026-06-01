/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Basepoint
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.Ed25519BasepointPoint
import Curve25519Dalek.ExternallyVerified

/-!
# Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_base`

Computes the scalar multiplication `[s]B` where `B` is the Edwards basepoint. The
implementation delegates to scalar-point multiplication on the constant basepoint
`backend.serial.u64.constants.ED25519_BASEPOINT_POINT`.

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64
namespace curve25519_dalek.edwards.EdwardsPoint

/-- **Spec theorem for `curve25519_dalek::edwards::EdwardsPoint::mul_base`**
• Given a canonically-encoded scalar (`U8x32_as_Nat scalar.bytes < 2 ^ 255`),
  the function always succeeds (no panic).
• The returned `EdwardsPoint` is a valid Edwards point.
• The returned `EdwardsPoint` represents `[s]B`, the scalar multiplication of
  the input `scalar` with the Edwards basepoint.
-/
@[step]
theorem mul_base_spec (scalar : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat scalar.bytes < 2 ^ 255) :
    mul_base scalar ⦃ (res : EdwardsPoint) =>
      EdwardsPoint.IsValid res ∧
      res.toPoint = (U8x32_as_Nat scalar.bytes) • _root_.Edwards.basepoint ⦄ := by
  unfold mul_base SharedAScalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul
  let* ⟨ ep, ep_post1, ep_post2, ep_post3, ep_post4, ep_post5, ep_post6 ⟩
    ← constants.ED25519_BASEPOINT_POINT_spec
  let* ⟨ res, res_post1, res_post2 ⟩
    ← Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul_spec
  exact ⟨res_post1, by rw [res_post2, ep_post6]⟩

end curve25519_dalek.edwards.EdwardsPoint
