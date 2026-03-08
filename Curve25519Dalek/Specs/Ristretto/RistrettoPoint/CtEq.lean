/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `RistrettoPoint::ct_eq`

Specification and proof for the `ConstantTimeEq` trait implementation for `RistrettoPoint`.

This function performs constant-time equality comparison of two Ristretto points by checking
whether X1·Y2 == Y1·X2 or X1·X2 == Y1·Y2 on the underlying extended coordinates, and
returning the bitwise OR of the two comparisons as a `Choice`.

Two Ristretto points (represented as extended twisted Edwards coordinates) are considered
equal if they represent the same element in the Ristretto quotient group 2E/E[4]. The
two cross-product checks capture this equivalence relation. Only X and Y coordinates are
used because the Z coordinates cancel out in the projective ratios.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51

namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq

/-
natural language description:

    Compares two RistrettoPoint values for equality in constant time.
    RistrettoPoint is a type alias for EdwardsPoint (extended twisted Edwards coordinates
    with fields X, Y, Z, T). Two Ristretto points are considered equal if they represent
    the same element in the Ristretto quotient group 2E/E[4].

    The implementation computes four field multiplications:
      X1Y2 = r1.X * r2.Y,  Y1X2 = r1.Y * r2.X,
      X1X2 = r1.X * r2.X,  Y1Y2 = r1.Y * r2.Y,
    then checks:
      c  = FE51.ct_eq(X1Y2, Y1X2)   -- X1·Y2 == Y1·X2 (mod p)?
      c1 = FE51.ct_eq(X1X2, Y1Y2)   -- X1·X2 == Y1·Y2 (mod p)?
    and returns bitor(c, c1), i.e., Choice.one if either condition holds (as either is sufficient for equality)

    Note: only X and Y coordinates are used because the Z coordinates cancel out
    in the projective cross-product ratios.

natural language specs:

    The result is Choice.one if and only if
      Field51_as_Nat(r1.X) * Field51_as_Nat(r2.Y) ≡ Field51_as_Nat(r1.Y) * Field51_as_Nat(r2.X) (mod p)
    OR
      Field51_as_Nat(r1.X) * Field51_as_Nat(r2.X) ≡ Field51_as_Nat(r1.Y) * Field51_as_Nat(r2.Y) (mod p)
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully given valid inputs)
- The result is Choice.one iff the two points satisfy the multiplicative Ristretto equivalence condition:
  X1·Y2 ≡ Y1·X2 (mod p) or X1·X2 ≡ Y1·Y2 (mod p)
-/
@[progress]
theorem ct_eq_spec
    (self other : RistrettoPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔
        (Field51_as_Nat self.X * Field51_as_Nat other.Y) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.X) [MOD p] ∨
        (Field51_as_Nat self.X * Field51_as_Nat other.X) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.Y) [MOD p] ⦄ := by
  sorry

end curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq
