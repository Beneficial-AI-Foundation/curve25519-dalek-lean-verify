/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # Spec Theorem for `EdwardsPoint::to_montgomery`

Specification and proof for `EdwardsPoint::to_montgomery`.

This function converts an EdwardsPoint from the twisted Edwards curve to the
corresponding MontgomeryPoint (only the u-coordinate) on the Montgomery curve, using the birational map
u = (1+y)/(1-y) = (Z+Y)/(Z-Y).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to a MontgomeryPoint (u-coordinate only), using the birational map:
  - u ≡ (1+y)/(1-y) ≡ (Z+Y)/(Z-Y) (mod p)

• Special case: when Y = Z (affine y = 1, the identity point on Edwards curve),
  the denominator is zero. Since 0.invert() = 0 in this implementation,
  this yields u = 0.

• The output u is represented as an U8x32 array (a type alias for MontgomeryPoint)

natural language specs:

• The function always succeeds (no panic)
• For the input Edwards point (X, Y, Z, T), the resulting MontgomeryPoint has u-coordinate:
  - If Z ≢ Y (mod p): u ≡ (Z+Y) * (Z-Y)^(-1) (mod p)
  - If Z ≡ Y (mod p): u ≡ 0 (mod p)
where p = 2^255 - 19
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.to_montgomery`**:
- No panic (always returns successfully)
- For the input Edwards point (X, Y, Z, T), the resulting MontgomeryPoint has u-coordinate:
  - If Z ≢ Y (mod p): u ≡ (Z+Y) * (Z-Y)^(-1) (mod p)
  - If Z ≡ Y (mod p): u ≡ 0 (mod p)
where p = 2^255 - 19
-/
@[progress]
theorem to_montgomery_spec (e : EdwardsPoint)
    (h_Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53)
    (h_Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53) :
    ∃ mp,
    to_montgomery e = ok mp ∧

    let Y := Field51_as_Nat e.Y
    let Z := Field51_as_Nat e.Z
    let u := U8x32_as_Nat mp

    if Z % p = Y % p then
      u % p = 0
    else
      (u * Z) % p = (u * Y + (Z + Y)) % p := by

      unfold to_montgomery
      progress*

      · intro i hi
        have := h_Z_bounds i hi
        omega

      · intro i hi
        have := h_Y_bounds i hi
        omega

      · intro i hi
        have := W_post_1 i hi
        omega

      · intro i hi
        have := fe_post i hi
        omega

      · split_ifs

        · rename_i h_zy_zero
          have h_W_zero : Field51_as_Nat W % p = 0 := by
            change Field51_as_Nat W ≡ 0 [MOD p]
            rw [h_zy_zero, ← Nat.ModEq] at W_post_2
            conv_rhs at W_post_2 => rw [← Nat.zero_add (Field51_as_Nat e.Y)]
            exact Nat.ModEq.add_right_cancel' (Field51_as_Nat e.Y) W_post_2
          rw [a_post_1, u_post_1, Nat.mul_mod, fe h_W_zero, mul_zero, Nat.zero_mod]

        · rename_i W_inv _ h_W_impl _ h_zy_nonzero

          have h_W_neq_zero : Field51_as_Nat W % p ≠ 0 := by sorry

          have h_W_inv := h_W_impl h_W_neq_zero
          conv at h_W_inv => change Field51_as_Nat W_inv % p * (Field51_as_Nat W % p) % p = 1

          sorry

end curve25519_dalek.edwards.EdwardsPoint
