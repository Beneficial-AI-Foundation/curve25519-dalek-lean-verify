/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation

/-! # Spec Theorem for `MontgomeryPoint::mul`

Specification and proof for
`curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::scalar::Scalar), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::montgomery::MontgomeryPoint)}::mul`.

This function performs scalar multiplication of a Montgomery point using the Montgomery ladder
algorithm. It implements constant-time scalar multiplication by processing scalar bits from
most significant to least significant.

**Source**: curve25519-dalek/src/montgomery.rs, lines 413:4-450:5

## TODO
- Complete proof
--/

open Aeneas.Std Result
open Montgomery

namespace curve25519_dalek.montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint

/-
Natural language description:

    • Interprets the MontgomeryPoint's 32-byte encoding as a field element u using
      `FieldElement51.from_bytes`.

    • Initializes two projective points:
      - x0 = (1 : 0) representing the identity (point at infinity)
      - x1 = (u : 1) representing the input point in projective coordinates

    • Processes scalar bits from most significant (bit 254) to least significant (bit 0)
      using the Montgomery ladder (Algorithm 8 from Costello-Smith 2017):
      - By scalar invariant #1, the MSB (bit 255) is always 0, so we start from bit 254
      - For each bit, conditionally swaps x0 and x1 based on bit transitions
      - Applies differential add-and-double operation
      - Maintains constant-time execution through conditional operations

    • After processing all bits, performs a final conditional swap based on the LSB

    • Converts the projective result x0 back to affine coordinates using `ProjectivePoint.as_affine`

Natural language specs:

    • The function always succeeds (no panic) given valid inputs
    • Returns a 32-byte MontgomeryPoint encoding the scalar multiplication result
    • The computation is constant-time with respect to the scalar value
    • The result represents the u-coordinate of [scalar]P on the Montgomery curve
-/

/-
Natural language description for loop:

    • The loop iterates from i = 254 down to i = 0 (inclusive)
    • For each iteration:
      - Extracts the i-th bit from the scalar_bytes array
      - Compares current bit with previous bit to determine if swap is needed
      - Conditionally swaps x0 and x1 based on bit transition
      - Applies differential_add_and_double operation with affine_u
      - Updates prev_bit for next iteration

    • Loop invariant: x0 and x1 represent points such that x1 - x0 = P (the base point)
    • This maintains the Montgomery ladder property throughout execution

Natural language specs for loop:

    • The loop always terminates when i reaches -1
    • Maintains constant-time execution by performing operations independent of bit values
    • Returns the final states of x0, x1, and prev_bit
    • Preserves the differential property: x1 - x0 equals the original input point
-/

/-- **Spec and proof concerning the Montgomery ladder loop** (loop 0 in mul function):
- No panic (always returns successfully given valid inputs)
- Iterates through scalar bits from bit i down to bit 0
- Mathematical properties:
  * Loop invariant: At each step, x0 and x1 represent projective points on the Montgomery curve
    such that the difference x1 - x0 (in affine coordinates) equals the input point P
  * The loop processes bits in big-endian order (most significant to least significant)
  * Conditional swaps ensure constant-time execution independent of scalar bit values
  * The differential_add_and_double operation maintains the ladder invariant:
    - Given x0 = [k]P and x1 = [k+1]P at iteration i
    - After processing bit b_i, we have x0 = [2k+b_i]P and x1 = [2k+b_i+1]P
  * Upon completion (when i = -1), x0 encodes the scalar multiple [n]P where n is
    the integer value of bits [254:0] of the scalar
  * The prev_bit output is the LSB (bit 0) of the scalar, needed for final swap
-/

@[progress]
theorem mul_loop_spec (affine_u : backend.serial.u64.field.FieldElement51)
    (x0 : ProjectivePoint) (x1 : ProjectivePoint)
    (scalar_bytes : Array U8 32#usize) (prev_bit : Bool) (i : Isize) :
    ∃ res_x0 res_x1 res_prev_bit,
    mul_loop affine_u x0 x1 scalar_bytes prev_bit i =
      ok (res_x0, res_x1, res_prev_bit) ∧
    (i<= 0#isize →  res_x0 = x0 ∧ res_x1= x1 ∧ res_prev_bit = prev_bit) ∧
    (i> 0#isize →
      let P := MontgomeryPoint.u_affine_toPoint (Field51_as_Nat x0.U / Field51_as_Nat x0.W)
      let P1 := MontgomeryPoint.u_affine_toPoint (Field51_as_Nat x1.U / Field51_as_Nat x1.W)
      P=P1)
    := by
    sorry


/-- **Spec and proof concerning `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements the Montgomery ladder for constant-time scalar multiplication
- Processes scalar bits from bit 254 down to bit 0 using Algorithm 8 (Costello-Smith 2017)
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]P
  * If P has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]P), the u-coordinate of the n-fold sum of P on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by P throughout the computation
  * When the scalar is reduced modulo the group order L, the result corresponds to
    scalar multiplication in the prime-order subgroup
  * The result is computed via projective arithmetic and converted back to affine form
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
  * The computation maintains constant-time guarantees: the sequence of operations
    executed is independent of the scalar bit values (only conditional swaps and
    unconditional arithmetic operations are performed)
-/

@[progress]
theorem mul_spec (P : MontgomeryPoint) (scalar : scalar.Scalar) :
    ∃ res,
    mul P scalar = ok res ∧
    MontgomeryPoint.toPoint res = (U8x32_as_Nat scalar.bytes) • (MontgomeryPoint.toPoint P)
     := by
    sorry


end curve25519_dalek.montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint

namespace curve25519_dalek.montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint

/- [curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::montgomery::MontgomeryPoint), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::scalar::Scalar)}::mul]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 462:4-464:5
-/

/-
Natural language description:

    • This is the commutative variant of scalar multiplication: Scalar * MontgomeryPoint.

    • Simply delegates to the MontgomeryPoint * Scalar implementation by swapping arguments.

Natural language specs:

    • The function always succeeds (no panic) given valid inputs
    • Returns the same result as the reverse multiplication (point * scalar)
    • Inherits all mathematical properties from MontgomeryPoint::mul
-/
/-- **Spec and proof concerning `montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the reverse operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MontgomeryPoint::mul with swapped arguments
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/

@[progress]
theorem mul_spec (scalar : scalar.Scalar) (P : MontgomeryPoint) :
    ∃ res,
    mul scalar P = ok res ∧
    MontgomeryPoint.toPoint res = (U8x32_as_Nat scalar.bytes) • (MontgomeryPoint.toPoint P)
    :=by
  unfold mul
  progress*

end curve25519_dalek.montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint

namespace curve25519_dalek.montgomery.MulMontgomeryPointSharedBScalarMontgomeryPoint

/- [curve25519_dalek::montgomery::{core::ops::arith::Mul<&'b (curve25519_dalek::scalar::Scalar), curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::mul]:
   Source: 'curve25519-dalek/src/macros.rs', lines 93:12-95:13
-/

/-
Natural language description:

    • This is another variant of scalar multiplication: MontgomeryPoint * &'b Scalar.

    • Delegates to the core MontgomeryPoint * Scalar implementation.

Natural language specs:

    • The function always succeeds (no panic) given valid inputs
    • Returns the same result as the underlying scalar multiplication
    • Inherits all mathematical properties from MontgomeryPoint::mul
-/
/-- **Spec and proof concerning `montgomery.MulMontgomeryPointSharedBScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the underlying operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by point throughout the computation
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/

@[progress]
theorem mul_spec (P : MontgomeryPoint) (rhs : scalar.Scalar) :
    ∃ res,
    mul P rhs = ok res ∧
    MontgomeryPoint.toPoint res = (U8x32_as_Nat rhs.bytes) • (MontgomeryPoint.toPoint P)
 := by
  unfold mul
  progress*

end curve25519_dalek.montgomery.MulMontgomeryPointSharedBScalarMontgomeryPoint

namespace curve25519_dalek.montgomery.MulScalarMontgomeryPointMontgomeryPoint

/-
Natural language description:

    • This is the non-borrow variant of scalar multiplication: Scalar * MontgomeryPoint.

    • Delegates to the shared reference implementation
      MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul.

Natural language specs:

    • The function always succeeds (no panic) given valid inputs
    • Returns the same result as the underlying scalar multiplication
    • Inherits all mathematical properties from the core Montgomery ladder implementation
-/
/-- **Spec and proof concerning `montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the underlying operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by point throughout the computation
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/

@[progress]
theorem mul_spec (scalar : scalar.Scalar) (P : MontgomeryPoint) :
    ∃ res,
    mul scalar P = ok res ∧
    MontgomeryPoint.toPoint res = (U8x32_as_Nat scalar.bytes) • (MontgomeryPoint.toPoint P)
 := by
  unfold mul
  progress*

end curve25519_dalek.montgomery.MulScalarMontgomeryPointMontgomeryPoint
