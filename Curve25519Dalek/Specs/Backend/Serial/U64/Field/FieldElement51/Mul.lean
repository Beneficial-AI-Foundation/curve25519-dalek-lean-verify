/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Tactics
/-! # Spec Theorem for `FieldElement51::mul`

Specification and proof for `FieldElement51::mul`.

This function computes the product of two field elements.

Source: curve25519-dalek/src/backend/serial/u64/field.rs -/

open Aeneas
open scoped Aeneas
open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51

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
    mul.m x y ⦃ r => r.val = x.val * y.val ⦄ := by
  sorry


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
  sorry

end curve25519_dalek.backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51
