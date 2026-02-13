/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Math.Montgomery.Representation
/-! # Spec Theorem for `EdwardsPoint::to_montgomery`

Specification and proof for `EdwardsPoint::to_montgomery`.

This function converts an EdwardsPoint from the twisted Edwards curve to the
corresponding MontgomeryPoint (only the u-coordinate) on the Montgomery curve, using the birational map
u = (1+y)/(1-y) = (Z+Y)/(Z-Y).

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
open Montgomery
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
    (h_Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53) (h_Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53) :
    ∃ mp, to_montgomery e = ok mp ∧
    (let Y := Field51_as_Nat e.Y
    let Z := Field51_as_Nat e.Z
    let u := U8x32_as_Nat mp
    if Z % p = Y % p then
      u % p = 0
    else
      (u * Z) % p = (u * Y + (Z + Y)) % p) ∧
    (∀ n : ℕ, fromEdwards.toPoint (n • e.toPoint) = n • (MontgomeryPoint.toPoint mp))

       := by
  unfold to_montgomery
  progress*
  · grind
  · grind
  · grind
  · grind
  · constructor
    · split_ifs
      · rename_i h_zy
        have h_W_zero : Field51_as_Nat W % p = 0 := by
          rw [h_zy, ← Nat.ModEq] at W_post_2
          conv_rhs at W_post_2 => rw [← Nat.zero_add (Field51_as_Nat e.Y)]
          exact Nat.ModEq.add_right_cancel' (Field51_as_Nat e.Y) W_post_2
        rw [a_post_1, u_post_1, Nat.mul_mod, fe h_W_zero, mul_zero, Nat.zero_mod]

      · rename_i W_inv _ h_W_impl _ h_zy
        have h_W_neq_zero : Field51_as_Nat W % p ≠ 0 := by
          intro h_contra
          rw [Nat.add_mod, h_contra, Nat.zero_add, Nat.mod_mod] at W_post_2
          exact h_zy W_post_2.symm
        have h_W_inv := h_W_impl h_W_neq_zero
        simp at h_W_inv
        ring_nf at h_W_inv
        rw [Nat.mul_mod, ← W_post_2, Nat.add_mod, ← Nat.mul_mod, Nat.mul_add, ← Nat.ModEq]
        ring_nf
        have h_sum : U8x32_as_Nat a * (Field51_as_Nat W % p) + U8x32_as_Nat a * (Field51_as_Nat e.Y % p)
          ≡ U8x32_as_Nat a * Field51_as_Nat W + U8x32_as_Nat a * Field51_as_Nat e.Y [MOD p] :=
          (Nat.ModEq.mul_left (U8x32_as_Nat a) (Nat.mod_modEq (Field51_as_Nat W) p)).add
          (Nat.ModEq.mul_left (U8x32_as_Nat a) (Nat.mod_modEq (Field51_as_Nat e.Y) p))
        refine h_sum.trans ?_
        rw [Nat.add_comm]
        have h_elim : U8x32_as_Nat a * Field51_as_Nat W ≡ Field51_as_Nat e.Y + Field51_as_Nat e.Z [MOD p] := by
          calc
            U8x32_as_Nat a * Field51_as_Nat W ≡
                Field51_as_Nat u * Field51_as_Nat W [MOD p] := by
                  simpa using a_post_1.mul_right (Field51_as_Nat W)
            _ ≡ (Field51_as_Nat U * Field51_as_Nat W_inv) * Field51_as_Nat W [MOD p] := by
                  simpa using u_post_1.mul_right (Field51_as_Nat W)
            _ ≡ Field51_as_Nat U [MOD p] := by
                  rw [Nat.mul_assoc]
                  simpa using @Nat.ModEq.mul_left p (Field51_as_Nat W_inv * Field51_as_Nat W) 1 (Field51_as_Nat U) h_W_inv
            _ ≡ Field51_as_Nat e.Y + Field51_as_Nat e.Z [MOD p] := by
                  have h_U_eq : Field51_as_Nat U = Field51_as_Nat e.Y + Field51_as_Nat e.Z := by
                    unfold Field51_as_Nat
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [U_post_1 i (Finset.mem_range.mp hi)]
                    ring
                  unfold Nat.ModEq
                  simp only [h_U_eq]
        have h_full := Nat.ModEq.add_left (U8x32_as_Nat a * Field51_as_Nat e.Y) (h_elim)
        grind
    · have :  fromEdwards.toPoint e.toPoint =  MontgomeryPoint.toPoint a := by
        sorry
      intro n
      rw[comm_mul_fromEdwards, this]

end curve25519_dalek.edwards.EdwardsPoint
