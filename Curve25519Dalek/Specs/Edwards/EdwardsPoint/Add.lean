/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `EdwardsPoint::add`

Specification and proof for `EdwardsPoint::add`.

This function adds two Edwards points using elliptic curve point addition.

**Source**: curve25519-dalek/src/edwards.rs

## TODO
- Complete proof
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.edwards.AddEdwardsPointEdwardsPointEdwardsPoint

/-
natural language description:

• Takes two EdwardsPoints `self` and `other` and returns their sum via elliptic curve
point addition (i.e., computes P + Q where P = self and Q = other)

natural language specs:

• The function always succeeds (no panic)
• The result is mathematically equivalent to the standard twisted Edwards addition formula
  (see Section 3.1 in https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf)
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.add`**:
- No panic (always returns successfully)
- Returns the sum P + Q (in elliptic curve addition) where P = self and Q = other
- The resulting point's coordinates satisfy the twisted Edwards addition formulas modulo
 (see Section 3.1 in https://www.iacr.org/archive/asiacrypt2008/53500329/53500329.pdf)
-/
@[progress]
theorem add_spec (self other : EdwardsPoint)

    (h_self_bounds : ∀ i < 5,
      self.X[i]!.val < 2 ^ 53 ∧
      self.Y[i]!.val < 2 ^ 53 ∧
      self.Z[i]!.val < 2 ^ 53 ∧
      self.T[i]!.val < 2 ^ 53)

    (h_other_bounds : ∀ i < 5,
      other.X[i]!.val < 2 ^ 53 ∧
      other.Y[i]!.val < 2 ^ 53 ∧
      other.Z[i]!.val < 2 ^ 53 ∧
      other.T[i]!.val < 2 ^ 53)

    (h_self_Z_nonzero : Field51_as_Nat self.Z % p ≠ 0)
    (h_other_Z_nonzero : Field51_as_Nat other.Z % p ≠ 0) :
    add self other ⦃ result =>
      (∀ i < 5,
        result.X[i]!.val < 2 ^ 54  ∧
        result.Y[i]!.val < 2 ^ 54  ∧
        result.Z[i]!.val < 2 ^ 54  ∧
        result.T[i]!.val < 2 ^ 54) ∧
      (let X₁ := Field51_as_Nat self.X;
       let Y₁ := Field51_as_Nat self.Y;
       let Z₁ := Field51_as_Nat self.Z;
       let T₁ := Field51_as_Nat self.T;
       let X₂ := Field51_as_Nat other.X;
       let Y₂ := Field51_as_Nat other.Y;
       let Z₂ := Field51_as_Nat other.Z;
       let T₂ := Field51_as_Nat other.T;
       let X₃ := Field51_as_Nat result.X;
       let Y₃ := Field51_as_Nat result.Y;
       let Z₃ := Field51_as_Nat result.Z;
       let T₃ := Field51_as_Nat result.T;
       X₃ % p = ((X₁ * Y₂ + Y₁ * X₂) * (Z₁ * Z₂ - d * T₁ * T₂)) % p ∧
       Y₃ % p = ((Y₁ * Y₂ - a * X₁ * X₂) * (Z₁ * Z₂ + d * T₁ * T₂)) % p ∧
       T₃ % p = ((Y₁ * Y₂ - a * X₁ * X₂) * (X₁ * Y₂ + Y₁ * X₂)) % p ∧
       Z₃ % p = ((Z₁ * Z₂ - d * T₁ * T₂) * (Z₁ * Z₂ + d * T₁ * T₂)) % p) ⦄ := by
  sorry

end curve25519_dalek.edwards.AddEdwardsPointEdwardsPointEdwardsPoint
