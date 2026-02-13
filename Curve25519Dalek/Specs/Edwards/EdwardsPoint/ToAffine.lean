/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
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
    ∃ ap,
    to_affine e = ok ap ∧

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
      (∀ i < 5, ap.y[i]!.val < 2 ^ 52) := by

      unfold to_affine
      progress*

      · intro i hi
        have := recip_post i hi
        omega

      · intro i hi
        have := recip_post i hi
        omega

      · rename_i Z_inv _ h_recip_nonzero _
        constructor

        · split_ifs

          · rename_i h_Z_zero
            have h_inv_zero : Field51_as_Nat Z_inv % p = 0 := recip h_Z_zero
            constructor

            · rw [x_post_1, Nat.mul_mod, h_inv_zero, mul_zero, Nat.zero_mod]

            · rw [y_post_1, Nat.mul_mod, h_inv_zero, mul_zero, Nat.zero_mod]

          · rename_i h_Z_nonzero
            have h_inv_nonzero : Field51_as_Nat Z_inv % p * (Field51_as_Nat e.Z % p) % p = 1 := h_recip_nonzero h_Z_nonzero
            rw [Nat.mul_mod] at h_inv_nonzero
            constructor

            · rw [Nat.mul_mod, x_post_1]
              simp only [Nat.mul_mod_mod, Nat.mod_mul_mod, mul_assoc]
              simp only [dvd_refl, Nat.mod_mod_of_dvd, Nat.mul_mod_mod, Nat.mod_mul_mod] at h_inv_nonzero
              simp [Nat.mul_mod, h_inv_nonzero]

            · rw [Nat.mul_mod, y_post_1]
              simp only [Nat.mul_mod_mod, Nat.mod_mul_mod, mul_assoc]
              simp only [dvd_refl, Nat.mod_mod_of_dvd, Nat.mul_mod_mod, Nat.mod_mul_mod] at h_inv_nonzero
              simp [Nat.mul_mod, h_inv_nonzero]

        · constructor

          · intro i hi
            have := x_post_2 i hi
            omega

          · intro i hi
            have := y_post_2 i hi
            omega

end curve25519_dalek.edwards.EdwardsPoint
