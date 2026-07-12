/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.Affine.AffinePoint.ToEdwards
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Mul

/-!
# Spec theorems for `AffinePoint` scalar multiplication

Scalar multiplication on affine Edwards points: given a valid affine Edwards point
`P` and a canonical scalar `s` (i.e., `s` represents a natural number less than
`2^255`), the result is `[s] P`, the elliptic curve group element obtained by adding
`P` to itself `s` times. The result is an `EdwardsPoint` in extended coordinates.

The Rust source defines two trait implementations of `core::ops::Mul` producing an
`EdwardsPoint` from a `Scalar` and an `AffinePoint`:

- `Mul<&AffinePoint> for Scalar`: the core implementation, converting the affine
  point to extended coordinates via `to_edwards` and then delegating to the
  `EdwardsPoint` scalar multiplication.
- `Mul<AffinePoint> for Scalar`: the non-borrow variant, delegating to the core
  implementation.

Source: "curve25519-dalek/src/edwards/affine.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulShared0AffinePointEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::mul`**
(trait impl `Mul<&AffinePoint> for Scalar`).
• The function always succeeds (no panic) for a canonical Scalar `self` and a valid
  AffinePoint `rhs` with limbs < 2^53
• The result is a valid EdwardsPoint
• `result.toPoint` equals `(U8x32_as_Nat self.bytes) • rhs.toPoint`, i.e., scalar
  multiplication of `rhs.toPoint` by the natural number encoded by `self.bytes`
-/
@[step]
theorem mul_spec
    (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint)
    (h_self_canonical : U8x32_as_Nat self.bytes < 2 ^ 255)
    (h_rhs_valid : rhs.IsValid)
    (hx53 : ∀ i < 5, rhs.x[i]!.val < 2 ^ 53)
    (hy53 : ∀ i < 5, rhs.y[i]!.val < 2 ^ 53) :
    mul self rhs ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat self.bytes) • rhs.toPoint ⦄ := by
  unfold mul edwards.EdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul
  let* ⟨ep, _, _, ep_valid, ep_point⟩ ←
    edwards.affine.AffinePoint.to_edwards_spec rhs h_rhs_valid hx53 hy53
  let* ⟨result, result_valid, result_point⟩ ←
    Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul_spec
      ep self h_self_canonical ep_valid
  refine ⟨result_valid, ?_⟩
  rw [result_point, ep_point]

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulShared0AffinePointEdwardsPoint

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAffinePointEdwardsPoint

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::mul`**
(trait impl `Mul<AffinePoint> for Scalar`).
• The function always succeeds (no panic) for a canonical Scalar `self` and a valid
  AffinePoint `rhs` with limbs < 2^53
• The result is a valid EdwardsPoint
• `result.toPoint` equals `(U8x32_as_Nat self.bytes) • rhs.toPoint`, i.e., scalar
  multiplication of `rhs.toPoint` by the natural number encoded by `self.bytes`
-/
@[step]
theorem mul_spec
    (self : scalar.Scalar) (rhs : edwards.affine.AffinePoint)
    (h_self_canonical : U8x32_as_Nat self.bytes < 2 ^ 255)
    (h_rhs_valid : rhs.IsValid)
    (hx53 : ∀ i < 5, rhs.x[i]!.val < 2 ^ 53)
    (hy53 : ∀ i < 5, rhs.y[i]!.val < 2 ^ 53) :
    mul self rhs ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat self.bytes) • rhs.toPoint ⦄ := by
  exact CoreOpsArithMulShared0AffinePointEdwardsPoint.mul_spec
    self rhs h_self_canonical h_rhs_valid hx53 hy53

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAffinePointEdwardsPoint
