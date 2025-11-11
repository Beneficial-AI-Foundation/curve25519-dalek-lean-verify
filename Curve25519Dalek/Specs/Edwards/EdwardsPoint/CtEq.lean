/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `EdwardsPoint::ct_eq`

Specification and proof for `EdwardsPoint::ct_eq`.

This function performs constant-time equality comparison for Edwards points.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint

/-
Natural language description:

    • Compares two EdwardsPoint types to determine whether they represent the same point

    • Checks equality of affine coordinates (x,y) = (X/Z, Y/Z) and (x',y') = (X'/Z', Y'/Z') without
      actually converting to affine coordinates by comparing (X·Z', Y·Z') with (X'·Z, Y'·Z)

    • Crucially does so in constant time irrespective of the inputs to avoid security liabilities

Natural language specs:

    • Requires: Z coordinates must be non-zero mod p (maintained as invariant for valid EdwardsPoints)
    • (e1.X · e2.Z, e1.Y · e2.Z) = (e2.X · e1.Z, e2.Y · e1.Z) ⟺ Choice = True
-/

/-- **Spec and proof concerning `edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint.ct_eq`**:
- No panic (always returns successfully)
- The result is Choice.one (true) if and only if the two points are equal (mod p) in affine coordinates
-/
@[progress]
theorem ct_eq_spec (e1 e2 : EdwardsPoint)
    (h_Z1_nonzero : Field51_as_Nat e1.Z % p ≠ 0)
    (h_Z2_nonzero : Field51_as_Nat e2.Z % p ≠ 0) :
    ∃ c u u' v v',
      backend.serial.u64.field.FieldElement51.Mul.mul e1.X e2.Z = ok u ∧
      backend.serial.u64.field.FieldElement51.Mul.mul e2.X e1.Z = ok u' ∧
      backend.serial.u64.field.FieldElement51.Mul.mul e1.Y e2.Z = ok v ∧
      backend.serial.u64.field.FieldElement51.Mul.mul e2.Y e1.Z = ok v' ∧
      ct_eq e1 e2 = ok c ∧
      (c = Choice.one ↔
        Field51_as_Nat u % p = Field51_as_Nat u' % p ∧
        Field51_as_Nat v % p = Field51_as_Nat v' % p) := by
  sorry

end curve25519_dalek.edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint
