/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul

/-! # Spec Theorem for `EdwardsPoint::to_affine`

Specification and proof for `EdwardsPoint::to_affine`.

This function converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to affine coordinates (x, y) by dehomogenizing: x = X/Z, y = Y/Z.

**Source**: curve25519-dalek/src/edwards.rs

## TODO
- Complete proof
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to affine coordinates (x, y), where:
  - x ≡ X/Z ≡ X * Z^(-1) (mod p)
  - y ≡ Y/Z ≡ Y * Z^(-1) (mod p)

• Special case: when Z ≡ 0 (mod p) (a point at infinity in projective coordinates),
  since 0.invert() = 0 in this implementation, the result will be x ≡ 0, y ≡ 0 (mod p).
  However, in practice, valid EdwardsPoints should have Z ≢ 0 (mod p).

natural language specs:

• The function always succeeds (no panic) when input limbs satisfy bounds
• For the input Edwards point (X, Y, Z, T), it holds for the resulting AffinePoint:
  - If Z ≢ 0 (mod p): x * Z ≡ X (mod p) and y * Z ≡ Y (mod p)
  - If Z ≡ 0 (mod p): x ≡ 0 (mod p) and y ≡ 0 (mod p)
where p = 2^255 - 19
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.to_affine`**:
- No panic (always returns successfully)
- For the input Edwards point (X, Y, Z, T), the resulting AffinePoint has coordinates:
  - If Z ≢ 0 (mod p): x * Z ≡ X (mod p) and y * Z ≡ Y (mod p)
  - If Z ≡ 0 (mod p): x ≡ 0 (mod p) and y ≡ 0 (mod p)
where p = 2^255 - 19
-/
@[progress]
theorem to_affine_spec (e : EdwardsPoint)
    (hX : ∀ i < 5, e.X[i]!.val < 2 ^ 54)
    (hY : ∀ i < 5, e.Y[i]!.val < 2 ^ 54)
    (hZ : ∀ i < 5, e.Z[i]!.val < 2 ^ 54) :
    to_affine e ⦃ ap =>
      let X := Field51_as_Nat e.X
      let Y := Field51_as_Nat e.Y
      let Z := Field51_as_Nat e.Z
      let x := Field51_as_Nat ap.x
      let y := Field51_as_Nat ap.y
      (if Z % p = 0 then
        x % p = 0 ∧ y % p = 0
      else
        (x * Z) % p = X % p ∧
        (y * Z) % p = Y % p) ∧
        (∀ i < 5, ap.x[i]!.val < 2 ^ 52) ∧
        (∀ i < 5, ap.y[i]!.val < 2 ^ 52) ⦄ := by
  sorry

end curve25519_dalek.edwards.EdwardsPoint
