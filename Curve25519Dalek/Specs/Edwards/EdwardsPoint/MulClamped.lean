/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Mul
import Curve25519Dalek.Specs.Scalar.ClampInteger

/-! # Spec Theorem for `EdwardsPoint::mul_clamped`

Specification and proof for
`curve25519_dalek::edwards::{curve25519_dalek::edwards::EdwardsPoint}::mul_clamped`.

This function performs scalar multiplication of an Edwards point after
clamping the input bytes to a valid scalar, delegating to `Scalar * EdwardsPoint`
multiplication.

Note: The clamped scalar is **not** necessarily reduced modulo the group order `L`,
which means the usual scalar canonicity invariant (`< L`) does not hold. However,
clamping guarantees `< 2^255`, which suffices for correctness of variable-base
scalar multiplication (see the Rust source comment at line 892).

**Source**: curve25519-dalek/src/edwards.rs, lines 891:4-903:5

## TODO
- Complete proof (the intermediate `mul_spec` currently requires a canonical scalar `< L`,
  but clamping only guarantees `< 2^255`; a relaxed variable-base mul spec is needed)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.edwards
open curve25519_dalek.backend.serial.u64



namespace curve25519_dalek.edwards.EdwardsPoint



/-
natural language description:

• Clamps the 32-byte input to a valid scalar using `scalar.clamp_integer`.

• Computes the scalar multiplication of `self` with the clamped scalar by
  delegating to `Scalar * EdwardsPoint` multiplication
  (`scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul`).

natural language specs:

• The function always succeeds (no panic)
• The result is a valid Edwards point
• The result is the scalar multiplication of the clamped scalar with `self`
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.mul_clamped`**:
- No panic (always returns successfully)
- Clamps input bytes with `scalar.clamp_integer`
- Delegates to `Scalar * EdwardsPoint` multiplication with the clamped scalar
- The returned EdwardsPoint matches the scalar multiplication result
-/
@[step]
theorem mul_clamped_spec (self : EdwardsPoint) (bytes : Array U8 32#usize)
    (h_self_valid : self.IsValid) :
    mul_clamped self bytes ⦃ (result : EdwardsPoint) =>
      EdwardsPoint.IsValid result ∧
      (∃ clamped_scalar,
      h ∣ U8x32_as_Nat clamped_scalar ∧
      U8x32_as_Nat clamped_scalar < 2 ^ 255 ∧
      2 ^ 254 ≤ U8x32_as_Nat clamped_scalar ∧
      result.toPoint = (((U8x32_as_Nat clamped_scalar)) • self.toPoint)) ⦄ := by
    unfold mul_clamped
    step*
    · simp_all[scalar.U8x32_as_Nat_eq_foldr']
    · simp only [result_post1, Nat.reducePow, true_and]
      simp_all only [Nat.reducePow, scalar.U8x32_as_Nat_eq_foldr']
      use a

end curve25519_dalek.edwards.EdwardsPoint
