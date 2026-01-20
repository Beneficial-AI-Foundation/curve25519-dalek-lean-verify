/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `RistrettoPoint::add`

Specification and proof for the `add` trait implementation for Ristretto points.

This function adds two Ristretto points by delegating to the underlying Edwards point addition.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.AddShared0RistrettoPointSharedARistrettoPointRistrettoPoint

/-
natural language description:

• Takes two RistrettoPoints `self` and `other`
• Returns their sum as a RistrettoPoint via elliptic curve group addition
• Implementation: unwraps both points to their underlying EdwardsPoint representations,
  performs Edwards addition, and wraps the result back as a RistrettoPoint

Given two Ristretto points P and Q represented in extended twisted Edwards coordinates:

- P = (X₁ : Y₁ : Z₁ : T₁) where T₁ = X₁Y₁/Z₁
- Q = (X₂ : Y₂ : Z₂ : T₂) where T₂ = X₂Y₂/Z₂

The sum R = P + Q = (X₃ : Y₃ : Z₃ : T₃) is computed using the complete twisted Edwards
addition formulas (Hisil-Wong-Carter-Dawson, https://eprint.iacr.org/2008/522):

- X₃ = (X₁Y₂ + Y₁X₂)(Z₁Z₂ - dT₁T₂)
- Y₃ = (Y₁Y₂ - aX₁X₂)(Z₁Z₂ + dT₁T₂)
- Z₃ = (Z₁Z₂ - dT₁T₂)(Z₁Z₂ + dT₁T₂)
- T₃ = (X₁Y₂ + Y₁X₂)(Y₁Y₂ - aX₁X₂)

where:
- a = -1 (curve parameter for Curve25519)
- d = -121665/121666 (curve parameter)
- p = 2²⁵⁵ - 19 (the field prime)
- All operations are performed modulo p

natural language specs:

• The function always succeeds (no panic) for valid inputs
• The result satisfies the twisted Edwards addition formulas modulo p
-/

/-- **Spec and proof concerning `ristretto.AddShared0RistrettoPointSharedARistrettoPointRistrettoPoint.add`**:
- The function always succeeds (no panic) for valid inputs
- The result satisfies the twisted Edwards addition formulas modulo p
-/
@[progress]
theorem add_spec (self other : RistrettoPoint)

    -- Precondition: coordinates of self are bounded by 2⁵³
    (h_self_bounds : ∀ i < 5,
      self.X[i]!.val < 2 ^ 53 ∧
      self.Y[i]!.val < 2 ^ 53 ∧
      self.Z[i]!.val < 2 ^ 53 ∧
      self.T[i]!.val < 2 ^ 53)

    -- Precondition: coordinates of other are bounded by 2⁵³
    (h_other_bounds : ∀ i < 5,
      other.X[i]!.val < 2 ^ 53 ∧
      other.Y[i]!.val < 2 ^ 53 ∧
      other.Z[i]!.val < 2 ^ 53 ∧
      other.T[i]!.val < 2 ^ 53)

    -- Precondition: Z-coordinate of self is non-zero mod p (valid projective point)
    (h_self_Z_nonzero : Field51_as_Nat self.Z % p ≠ 0)

    -- Precondition: Z-coordinate of other is non-zero mod p (valid projective point)
    (h_other_Z_nonzero : Field51_as_Nat other.Z % p ≠ 0) :

    -- Postcondition: function succeeds and returns a result
    ∃ result, add self other = ok result ∧

    -- Postcondition: coordinates of result are bounded by 2⁵⁴
    (∀ i < 5,
      result.X[i]!.val < 2 ^ 54  ∧
      result.Y[i]!.val < 2 ^ 54  ∧
      result.Z[i]!.val < 2 ^ 54  ∧
      result.T[i]!.val < 2 ^ 54) ∧

    -- Extract the mathematical values (as natural numbers mod p)
    let X₁ := Field51_as_Nat self.X
    let Y₁ := Field51_as_Nat self.Y
    let Z₁ := Field51_as_Nat self.Z
    let T₁ := Field51_as_Nat self.T

    let X₂ := Field51_as_Nat other.X
    let Y₂ := Field51_as_Nat other.Y
    let Z₂ := Field51_as_Nat other.Z
    let T₂ := Field51_as_Nat other.T

    let X₃ := Field51_as_Nat result.X
    let Y₃ := Field51_as_Nat result.Y
    let Z₃ := Field51_as_Nat result.Z
    let T₃ := Field51_as_Nat result.T

    -- Postcondition: mathematical correctness (twisted Edwards addition formulas)
    -- These formulas implement the complete addition law on the twisted Edwards curve
    -- -x² + y² = 1 + dx²y² over F_p where p = 2²⁵⁵ - 19
    X₃ % p = ((X₁ * Y₂ + Y₁ * X₂) * (Z₁ * Z₂ - d * T₁ * T₂)) % p ∧
    Y₃ % p = ((Y₁ * Y₂ - a * X₁ * X₂) * (Z₁ * Z₂ + d * T₁ * T₂)) % p ∧
    T₃ % p = ((Y₁ * Y₂ - a * X₁ * X₂) * (X₁ * Y₂ + Y₁ * X₂)) % p ∧
    Z₃ % p = ((Z₁ * Z₂ - d * T₁ * T₂) * (Z₁ * Z₂ + d * T₁ * T₂)) % p ∧

    -- Postcondition: result is a valid projective point (non-zero Z-coordinate)
    Z₃ % p ≠ 0

    := by
  sorry

end curve25519_dalek.ristretto.AddShared0RistrettoPointSharedARistrettoPointRistrettoPoint
