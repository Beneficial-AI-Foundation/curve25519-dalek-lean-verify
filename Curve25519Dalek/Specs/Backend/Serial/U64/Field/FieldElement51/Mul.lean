/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Tactics
/-! # Spec Theorem for `FieldElement51::mul`

Specification and proof for `FieldElement51::mul`.

This function computes the product of two field elements.

Source: curve25519-dalek/src/backend/serial/u64/field.rs -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
open _root_.curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
  (mul)
open _root_.curve25519_dalek.backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51
  (mul.m mul.LOW_51_BIT_MASK)

/-
natural language description:

    • Computes the product of two field elements a and b in the field 𝔽_p where p = 2^255 - 19
    • The field elements are represented as five u64 limbs each

natural language specs:

    • The function always succeeds (no panic)
    • Field51_as_Nat(result) ≡ Field51_as_Nat(lhs) * Field51_as_Nat(rhs) (mod p)
-/


/- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.Mul.mul.m`**:
- No panic (always returns successfully)
- The result equals the product of the inputs when viewed as natural numbers
- Input bounds: x, y are valid U64 values
- Output bounds: result < 2^128
-/
@[progress]
theorem m_spec (x y : U64) :
    mul.m x y ⦃ r =>
    r.val = x.val * y.val ⦄ := by
  unfold mul.m
  progress*
  have : x.val < 2 ^64 := by scalar_tac
  have i_lt: i.val < 2^ 64 := by
    rw[i_post, UScalar.cast_val_eq, UScalarTy.numBits]
    have : x.val < 2 ^ 128 := by scalar_tac
    have := Nat.mod_eq_of_lt this
    rw[this]
    scalar_tac
  have : y.val < 2 ^64 := by scalar_tac
  have i1_lt: i1.val < 2^ 64 := by
    rw[i1_post, UScalar.cast_val_eq, UScalarTy.numBits]
    have : y.val < 2 ^ 128 := by scalar_tac
    have := Nat.mod_eq_of_lt this
    rw[this]
    scalar_tac
  have := Nat.mul_lt_mul'' i_lt i1_lt
  scalar_tac



lemma LOW_51_BIT_MASK_spec : mul.LOW_51_BIT_MASK.val = 2^ 51 -1 := by
  unfold mul.LOW_51_BIT_MASK
  decide






lemma decompose (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℕ) :
  (a0 +
  2 ^ 51 * a1 +
  2^ (2 * 51) * a2 +
  2^ (3 * 51) * a3 +
  2^ (4 * 51) * a4) * (b0 +
  2 ^ 51 * b1 +
  2^ (2 * 51) * b2 +
  2^ (3 * 51) * b3 +
  2^ (4 * 51) * b4)
  ≡ a0 * b0 +  a4 * (b1 * 19 )+  a3 * (b2 * 19) + a2 * (b3 * 19) + a1 * (b4 * 19) +
    2 ^ 51 * ( a1 * b0 + a0 * b1 + a4 * (b2 * 19 )+
    a3 * (b3 * 19) + a2 * (b4 * 19) ) +
    2 ^ (2 * 51) * (
      a2 * b0 + a1 * b1 + a0 * b2 +
      a4 * (b3 * 19) + a3 * (b4 * 19)
      ) +
    2 ^ (3 * 51) * (
      a3 * b0 + a2 * b1 + a1 * b2 +  a0 * b3 +
      a4 * (b4 * 19)
    ) +
    2 ^ (4 * 51) * (
      a4 * b0 + a3 * b1 + a2 * b2 +  a1 * b3 + a0 * b4
    )
   [MOD p] := by
  have : (a0 +
  2 ^ 51 * a1 +
  2^ (2 * 51) * a2 +
  2^ (3 * 51) * a3 +
  2^ (4 * 51) * a4) * (b0 +
  2 ^ 51 * b1 +
  2^ (2 * 51) * b2 +
  2^ (3 * 51) * b3 +
  2^ (4 * 51) * b4) =
  (a0 * b0 +
  2 ^ 51 * (a1 * b0 + a0 * b1) +
  2^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2) +
  2^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) +
  2^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4)) +
  2^ (255) * ( (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4) +
  2 ^ 51 * (a4 *  b2 + a3 * b3 + a2 * b4)  +
  2^ (2 * 51) * ( a4 * b3 + a3 * b4) +
  2^ (3 * 51) * (a4 * b4)) := by grind
  rw[this]
  have key  : (2:ℕ)^255 ≡ 19 [MOD p] := by
          unfold p
          rw [Nat.ModEq]
          norm_num
  have := Nat.ModEq.mul_right ( (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4) +
  2 ^ 51 * (a4 *  b2 + a3 * b3 + a2 * b4)  +
  2^ (2 * 51) * ( a4 * b3 + a3 * b4) +
  2^ (3 * 51) * (a4 * b4)) key
  have := Nat.ModEq.add_left  (a0 * b0 +
  2 ^ 51 * (a1 * b0 + a0 * b1) +
  2^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2) +
  2^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) +
  2^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4))  this
  apply Nat.ModEq.trans this
  have : a0 * b0 + 2 ^ 51 * (a1 * b0 + a0 * b1) + 2 ^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2) +
        2 ^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) +
      2 ^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4) +
    19 *
      (a4 * b1 + a3 * b2 + a2 * b3 + a1 * b4 + 2 ^ 51 * (a4 * b2 + a3 * b3 + a2 * b4) +
          2 ^ (2 * 51) * (a4 * b3 + a3 * b4) +
        2 ^ (3 * 51) * (a4 * b4)) =
        a0 * b0 + a4 * (b1 * 19) + a3 * (b2 * 19) + a2 * (b3 * 19) + a1 * (b4 * 19) +
          2 ^ 51 * (a1 * b0 + a0 * b1 + a4 * (b2 * 19) + a3 * (b3 * 19) + a2 * (b4 * 19)) +
        2 ^ (2 * 51) * (a2 * b0 + a1 * b1 + a0 * b2 + a4 * (b3 * 19) + a3 * (b4 * 19)) +
      2 ^ (3 * 51) * (a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3 + a4 * (b4 * 19)) +
    2 ^ (4 * 51) * (a4 * b0 + a3 * b1 + a2 * b2 + a1 * b3 + a0 * b4) := by grind
  rw[this]

/- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.Mul.mul`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to the product of the inputs modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^52
-/

set_option maxHeartbeats 10000000000 in
-- progress heavy
@[progress]
theorem mul_spec (lhs rhs : Array U64 5#usize)
    (hlhs : ∀ i < 5, lhs[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, rhs[i]!.val < 2 ^ 54) :
    mul lhs rhs ⦃ r =>
    Field51_as_Nat r ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by
  unfold mul
  progress*
  · -- BEGIN TASK
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  ·-- BEGIN TASK
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_2 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_2 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_1 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_2 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_0 hrhs_3
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_0 hrhs_3
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
    have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_2 this
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i51.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_3 this
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i56.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_0 hrhs_3
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_4 this
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i61.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
    have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    simp_all
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    suffices h: i71.val < (2^ 64-1)/19 by
    -- END TASK
      · -- BEGIN TASK
        have : i71.val < 2 ^ 64 := by scalar_tac
        have := Nat.mod_eq_of_lt this
        rw[this]
        have := (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
        apply le_trans (le_of_lt this)
        scalar_tac
        -- END TASK
    · -- BEGIN TASK
      simp_all
      rw[Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      expand hrhs with 5; expand hlhs with 5; simp [*];
      have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
      have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
      have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
      have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
      have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
      have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
      have := Nat.add_lt_add eq1 eq2
      have := Nat.add_lt_add this eq3
      have := Nat.add_lt_add this eq4
      have := Nat.add_lt_add this eq5
      have := Nat.add_lt_add this eq6
      apply lt_trans this
      scalar_tac
      -- END TASK
  · -- BEGIN TASK
    simp_all
    rw[ UScalar.cast_val_eq, UScalarTy.numBits, LOW_51_BIT_MASK_spec,
    land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits]
    suffices h: i71.val < (2^ 64 - 1 - 2^ 51)/19 by
      · -- BEGIN TASK
        have : i71.val < 2 ^ 64 := by scalar_tac
        have := Nat.mod_eq_of_lt this
        rw[this]
        have eq1:= (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
        have := Nat.mod_lt (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
        have := Nat.add_lt_add this eq1
        apply le_trans (le_of_lt this)
        scalar_tac
        -- END TASK
    · -- BEGIN TASK
      simp_all
      rw[Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      expand hrhs with 5; expand hlhs with 5; simp [*];
      have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
      have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
      have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
      have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
      have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
      have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
      have := Nat.add_lt_add eq1 eq2
      have := Nat.add_lt_add this eq3
      have := Nat.add_lt_add this eq4
      have := Nat.add_lt_add this eq5
      have := Nat.add_lt_add this eq6
      apply lt_trans this
      scalar_tac
      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    simp_all
    rw[ UScalar.cast_val_eq, UScalarTy.numBits, LOW_51_BIT_MASK_spec,
    land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits,
    land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits,
    Nat.shiftRight_eq_div_pow]
    suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2^ 64 - 1 by --2 ^ 51 * (2^ 64 - 1 - 2^ 51)
      · -- BEGIN TASK
        suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2 ^ 51 * (2^ 64 - 1 - 2^ 51) by
          · -- BEGIN TASK
            have eq1:= Nat.mod_lt (c11.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
            have := Nat.div_lt_of_lt_mul h
            have := Nat.add_lt_add eq1 this
            apply le_trans (le_of_lt this)
            scalar_tac
            -- END TASK
        ·-- BEGIN TASK
          apply lt_trans h
          simp
          -- END TASK
    · -- BEGIN TASK
      suffices h: i71.val < ( 2^ 64 -1 )/19 - 2 ^ 51 by
        · -- BEGIN TASK
          have : i71.val < 2 ^ 64 := by scalar_tac
          have := Nat.mod_eq_of_lt this
          rw[this]
          have eq1:= (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
          have := Nat.mod_lt (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
          have := Nat.add_lt_add  this  eq1
          apply lt_trans this
          scalar_tac
          -- END TASK
      · -- BEGIN TASK
        simp_all
        rw[Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        expand hrhs with 5; expand hlhs with 5; simp [*];
        have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
        have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
        have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
        have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
        have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
        have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
        have := Nat.add_lt_add eq1 eq2
        have := Nat.add_lt_add this eq3
        have := Nat.add_lt_add this eq4
        have := Nat.add_lt_add this eq5
        have := Nat.add_lt_add this eq6
        apply lt_trans this
        scalar_tac
        -- END TASK
      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    constructor
    · -- BEGIN TASK
      simp_all[Field51_as_Nat, Finset.sum_range_succ, U64.size, U64.numBits]
      rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits]
      have :  (c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19) % 2 ^ 51 +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51 + (c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19) >>> 51) +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51) =
          (c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19) +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51)
        := by
        simp [Nat.shiftRight_eq_div_pow]
        have := Nat.mod_add_div (c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19) (2 ^ 51)
        simp at this
        grind
      simp at this
      simp
      rw[this]
      have i71_lt: i71.val < 18446744073709551616  := by
        simp_all
        rw[Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        expand hrhs with 5; expand hlhs with 5; simp [*];
        have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
        have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
        have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
        have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
        have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
        have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
        have := Nat.add_lt_add eq1 eq2
        have := Nat.add_lt_add this eq3
        have := Nat.add_lt_add this eq4
        have := Nat.add_lt_add this eq5
        have := Nat.add_lt_add this eq6
        apply lt_trans this
        scalar_tac
      have i71_mod:= Nat.mod_eq_of_lt i71_lt
      rw[i71_mod]
      have : (c0.val  % 2 ^ 51 + i71.val  * 19) +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51)
          ≡ (c0.val % 2 ^ 51  ) +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51 + 2 ^ 51 * i71.val) [MOD p] := by
        have key  : 19 ≡ (2:ℕ)^255 [MOD p] := by
          unfold p
          rw [Nat.ModEq]
          norm_num
        have := Nat.ModEq.mul_left i71.val key
        have eq1:= Nat.ModEq.add_right ((c0.val % 2 ^ 51  ) +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51)) this
        have : i71.val  * 19 + ((c0.val % 2 ^ 51  ) +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51)) =
          (c0.val % 2 ^ 51 + i71.val  * 19 ) +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51)  := by grind
        rw[← this]
        apply Nat.ModEq.trans eq1
        have : i71.val * 2 ^ 255 +
          (c0.val % 2 ^ 51 + 2 ^ 51 * (↑c11 % 2 ^ 64 % 2 ^ 51) + 2 ^ (2 * 51) * (↑c21 % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51) * (↑c31 % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51) * (↑c41 % 2 ^ 64 % 2 ^ 51)) =
          ↑c0 % 2 ^ 51 + 2 ^ 51 * (↑c11 % 2 ^ 64 % 2 ^ 51) + 2 ^ (2 * 51) * (↑c21 % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51) * (↑c31 % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51) * (↑c41 % 2 ^ 64 % 2 ^ 51 + 2 ^ 51 * ↑i71)  := by grind
        rw[this]
      simp at this
      apply Nat.ModEq.trans this
      have : (c0.val % 2 ^ 51  ) +
          2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
          2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
          2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51 + 2 ^ 51 * i71.val)
          = c0.val    +
          2 ^ 51 * (c1.val)  +
          2 ^ (2 * 51 ) * (c2.val ) +
          2 ^ (3 * 51 )  * (c3.val)
          + 2 ^ (4 * 51 )  * (c4.val  )
           := by
        calc
          (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
            2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
            2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
            2 ^ (4 * 51 )  * (c41.val % 2 ^ 64 % 2 ^ 51 + 2 ^ 51 * i71.val)
            = (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
            2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
            2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51) +
            2 ^ (4 * 51 )  * (c41.val )
            := by
            simp
            rw[i71_post_1, ← c41_post, Nat.shiftRight_eq_div_pow]
            apply Nat.mod_add_div
          _ = (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
            2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
            2 ^ (3 * 51 )  * (c31.val % 2 ^ 64 % 2 ^ 51 + 2 ^ 51 * (i66.val % 2 ^ 64))
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
              simp
              rw[c41_post, ← c4_post, UScalar.cast_val_eq, UScalarTy.numBits,]
              grind
          _ = (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
            2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51) +
            2 ^ (3 * 51 )  * (c31.val)
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
            simp
            have : i66.val < 18446744073709551616 := by
              rw[i66_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_lt_of_lt_mul
              rw[UScalar.cast_val_eq, UScalarTy.numBits,]
              expand hrhs with 5; expand hlhs with 5;
              have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
              have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
              have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
              have eq4:= Nat.mul_lt_mul'' hlhs_0 hrhs_3
              have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
              have eq5:= Nat.mul_lt_mul'' hlhs_4 this
              have eq6:=Nat.mod_lt (i61.val) (by simp : 0 < 2 ^64)
              have := Nat.add_lt_add eq1 eq2
              have := Nat.add_lt_add this eq3
              have := Nat.add_lt_add this eq4
              have := Nat.add_lt_add this eq5
              have := Nat.add_lt_add this eq6
              apply lt_trans this
              scalar_tac
            have := Nat.mod_eq_of_lt this
            rw[this, i66_post_1, ← c31_post, Nat.shiftRight_eq_div_pow]
            apply Nat.mod_add_div
          _ = (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
            2 ^ (2 * 51 ) * (c21.val % 2 ^ 64 % 2 ^ 51 + 2 ^ 51 * (i61.val % 2 ^ 64)) +
            2 ^ (3 * 51 )  * (c3.val)
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
              simp
              rw[c31_post, ← c3_post, UScalar.cast_val_eq, UScalarTy.numBits,]
              grind

          _ = (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51)  +
            2 ^ (2 * 51 ) * (c21.val ) +
            2 ^ (3 * 51 )  * (c3.val)
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
            simp
            have : i61.val < 18446744073709551616 := by
              rw[i61_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_lt_of_lt_mul
              rw[UScalar.cast_val_eq, UScalarTy.numBits,]
              expand hrhs with 5; expand hlhs with 5;
              have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
              have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
              have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
              have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
              have eq4:= Nat.mul_lt_mul'' hlhs_4 this
              have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
              have eq5:= Nat.mul_lt_mul'' hlhs_3 this
              have eq6:=Nat.mod_lt (i56.val) (by simp : 0 < 2 ^64)
              have := Nat.add_lt_add eq1 eq2
              have := Nat.add_lt_add this eq3
              have := Nat.add_lt_add this eq4
              have := Nat.add_lt_add this eq5
              have := Nat.add_lt_add this eq6
              apply lt_trans this
              scalar_tac
            have := Nat.mod_eq_of_lt this
            rw[this, i61_post_1, ← c21_post, Nat.shiftRight_eq_div_pow]
            apply Nat.mod_add_div
          _ = (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val % 2 ^ 64 % 2 ^ 51 + 2 ^ 51 * ( i56.val  % 2 ^ 64))  +
            2 ^ (2 * 51 ) * (c2.val ) +
            2 ^ (3 * 51 )  * (c3.val)
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
              simp
              rw[c21_post, ← c2_post, UScalar.cast_val_eq, UScalarTy.numBits,]
              grind

          _ = (c0.val % 2 ^ 51  ) +
            2 ^ 51 * (c11.val)  +
            2 ^ (2 * 51 ) * (c2.val ) +
            2 ^ (3 * 51 )  * (c3.val)
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
            simp
            have : i56.val < 18446744073709551616 := by
              rw[i56_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_lt_of_lt_mul
              rw[UScalar.cast_val_eq, UScalarTy.numBits,]
              expand hrhs with 5; expand hlhs with 5;
              have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
              have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
              have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
              have eq3:= Nat.mul_lt_mul'' hlhs_4 this
              have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
              have eq4:= Nat.mul_lt_mul'' hlhs_3 this
              have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
              have eq5:= Nat.mul_lt_mul'' hlhs_2 this
              have eq6:=Nat.mod_lt (i51.val) (by simp : 0 < 2 ^64)
              have := Nat.add_lt_add eq1 eq2
              have := Nat.add_lt_add this eq3
              have := Nat.add_lt_add this eq4
              have := Nat.add_lt_add this eq5
              have := Nat.add_lt_add this eq6
              apply lt_trans this
              scalar_tac
            have := Nat.mod_eq_of_lt this
            rw[this, i56_post_1, ← c11_post, Nat.shiftRight_eq_div_pow]
            apply Nat.mod_add_div
          _ = (c0.val % 2 ^ 51  + 2 ^ 51 * (i51.val % 2 ^ 64) ) +
            2 ^ 51 * (c1)  +
            2 ^ (2 * 51 ) * (c2.val ) +
            2 ^ (3 * 51 )  * (c3.val)
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
              simp
              rw[c11_post, ← c1_post, UScalar.cast_val_eq, UScalarTy.numBits,]
              grind
          _ = c0.val  +
            2 ^ 51 * (c1.val)  +
            2 ^ (2 * 51 ) * (c2.val ) +
            2 ^ (3 * 51 )  * (c3.val)
            + 2 ^ (4 * 51 )  * (c4.val  )
            := by
            simp
            have : i51.val < 18446744073709551616 := by
              rw[i51_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_lt_of_lt_mul
              expand hrhs with 5; expand hlhs with 5;
              have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
              have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
              have eq2:= Nat.mul_lt_mul'' hlhs_4 this
              have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
              have eq3:= Nat.mul_lt_mul'' hlhs_3 this
              have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
              have eq4:= Nat.mul_lt_mul'' hlhs_2 this
              have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
              have eq5:= Nat.mul_lt_mul'' hlhs_1 this
              have := Nat.add_lt_add eq1 eq2
              have := Nat.add_lt_add this eq3
              have := Nat.add_lt_add this eq4
              have := Nat.add_lt_add this eq5
              apply lt_trans this
              scalar_tac
            have := Nat.mod_eq_of_lt this
            rw[this, i51_post_1, ← c0_post, Nat.shiftRight_eq_div_pow]
            apply Nat.mod_add_div
      simp at this
      rw[this]
      simp_all
      have := decompose (lhs[0]!).val (lhs[1]!).val (lhs[2]!).val (lhs[3]!).val (lhs[4]!).val (rhs[0]!).val (rhs[1]!).val (rhs[2]!).val (rhs[3]!).val (rhs[4]!).val
      simp at this
      apply Nat.ModEq.symm
      apply Nat.ModEq.trans this
      apply Nat.ModEq.rfl
      -- END TASK
    · -- BEGIN TASK
      intro i _
      interval_cases i
      · -- BEGIN TASK
        simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp
        -- END TASK
      · -- BEGIN TASK
        simp_all
        rw[ UScalar.cast_val_eq, UScalarTy.numBits, LOW_51_BIT_MASK_spec,
        land_pow_two_sub_one_eq_mod,
        UScalar.cast_val_eq, UScalarTy.numBits,
        land_pow_two_sub_one_eq_mod,
        UScalar.cast_val_eq, UScalarTy.numBits,
        Nat.shiftRight_eq_div_pow]
        suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2 ^ 64 -1 by
          ·  -- BEGIN TASK
             suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2 ^ 51 * (2^ 52 - 1 - 2^ 51) by
               · -- BEGIN TASK
                 have eq1:= Nat.mod_lt (c11.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
                 have := Nat.div_lt_of_lt_mul h
                 have := Nat.add_lt_add eq1 this
                 apply lt_trans this
                 scalar_tac
                 -- END TASK
             · -- BEGIN TASK
               apply lt_trans h
               scalar_tac
               -- END TASK
             -- END TASK
        · -- BEGIN TASK
          suffices h: i71.val < ( 2^ 64 -1 )/19 - 2 ^ 51 by
            · -- BEGIN TASK
              have : i71.val < 2 ^ 64 := by scalar_tac
              have := Nat.mod_eq_of_lt this
              rw[this]
              have eq1:= (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
              have := Nat.mod_lt (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
              have := Nat.add_lt_add  this  eq1
              apply lt_trans this
              scalar_tac
              -- END TASK
          · -- BEGIN TASK
            simp_all
            rw[Nat.shiftRight_eq_div_pow]
            apply Nat.div_lt_of_lt_mul
            expand hrhs with 5; expand hlhs with 5; simp [*];
            have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
            have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
            have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
            have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
            have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
            have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
            have := Nat.add_lt_add eq1 eq2
            have := Nat.add_lt_add this eq3
            have := Nat.add_lt_add this eq4
            have := Nat.add_lt_add this eq5
            have := Nat.add_lt_add this eq6
            apply lt_trans this
            scalar_tac
            -- END TASK
          -- END TASK
        -- END TASK
      · -- BEGIN TASK
        simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp
        -- END TASK
      · -- BEGIN TASK
        simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp
        -- END TASK
      · -- BEGIN TASK
        simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp
        -- END TASK

end curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
