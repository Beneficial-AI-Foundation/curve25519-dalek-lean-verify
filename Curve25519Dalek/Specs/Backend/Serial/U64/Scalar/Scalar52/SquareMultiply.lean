/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomerySquare

/-! # Spec Theorem for `Scalar52::montgomery_invert::square_multiply`

Specification and proof for `Scalar52::montgomery_invert::square_multiply`.

This is a helper function for the addition chain in the inversion algorithm.
It performs repeated Montgomery squaring followed by a Montgomery multiplication.

**Source**: curve25519-dalek/src/scalar.rs

-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.scalar curve25519_dalek.backend.serial.u64.scalar.Scalar52

namespace curve25519_dalek.scalar.Scalar52

/-
natural language description:

    • Takes as input:
      - `y`: An accumulator in Montgomery form.
      - `squarings`: The number of times to square `y`.
      - `x`: A value to multiply into the accumulator after squaring.

    • It computes `y` raised to the power of `2^squarings`, and then multiplies by `x`.
      Since all operations are in Montgomery form, this efficiently computes:
      result = (y^(2^s) * x) * R^(-2^s)  (modulo L)

    • This pattern corresponds to a "window" or "chain" step in the addition chain
      for computing the inverse.

natural language specs:

    • For any inputs `y`, `x` with proper bounds, and `squarings` s:
      - The function returns successfully.
      - The result satisfies the algebraic relation:
        result * R^(2^s) = y^(2^s) * x (mod L)
-/

-- Helper function
def pow2 (n : Nat) : Nat := 2^n

/--
Specification for the inner loop `square_multiply_loop`.
It performs `squarings - i` remaining squarings on `y` (all in Montgomery form).

Mathematically, if the loop runs `k` times, it computes:
  res = y^(2^k) * R^{-(2^k - 1)}
-/
theorem square_multiply_loop_spec (y : Scalar52) (squarings i : Usize) (hi : i.val ≤ squarings.val)
    (h_y_bound : ∀ j < 5, y[j]!.val < 2 ^ 62) :
    ∃ res, montgomery_invert.square_multiply_loop y squarings i = ok res ∧
    (Scalar52_as_Nat res * R ^ (pow2 (squarings.val - i.val) - 1)) % L =
    (Scalar52_as_Nat y) ^ (pow2 (squarings.val - i.val)) % L ∧
    (∀ j < 5, res[j]!.val < 2 ^ 62) := by
  induction h_rem : (squarings.val - i.val) generalizing i y with
  | zero =>
    have : i = squarings := by
      have h_ge : squarings.val ≤ i.val := Nat.le_of_sub_eq_zero h_rem
      have h_val_eq : i.val = squarings.val := Nat.le_antisymm hi h_ge
      cases i; cases squarings; simp_all
      exact BitVec.eq_of_toNat_eq h_val_eq

    unfold montgomery_invert.square_multiply_loop
    simp [this]
    simp [pow2]
    intro i hi; simpa using h_y_bound i hi

  | succ n ih =>
    unfold montgomery_invert.square_multiply_loop
    simp
    split
    · -- Case 1: Loop Continues (i < squarings)
      -- 1. Perform the square
      progress with montgomery_square_spec as ⟨y1, hy1_eq, hy1_bound⟩

      have h_no_overflow : i.val + 1 ≤ Usize.max := by
        have : i.val < squarings.val := by scalar_tac
        scalar_tac

      obtain ⟨i1, h_call_i1, h_val_i1⟩ := @Usize.add_spec i 1#usize h_no_overflow
      rw [h_call_i1]
      simp only [bind_tc_ok]

      have h_i1_bound : i1.val ≤ squarings.val := by
        simp [h_val_i1]; scalar_tac

      have h_rem_next : squarings.val - i1.val = n := by
        simp [h_val_i1]
        scalar_tac

      obtain ⟨res, h_call_loop, h_math_ih, h_res_bound⟩ :=
        ih y1 i1 h_i1_bound hy1_bound h_rem_next

      refine ⟨res, h_call_loop, ?_, h_res_bound⟩
      · -- Proof of Equality
        have h_pow_split : pow2 (n + 1) - 1 = (pow2 n - 1) + pow2 n := by
          simp [pow2, Nat.pow_succ, Nat.mul_succ]
          have : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
          omega

        rw [h_pow_split, Nat.pow_add]
        unfold pow2 at *; try ring_nf at ⊢ h_math_ih
        rw [Nat.mul_mod, h_math_ih, ← Nat.mul_mod, ← Nat.mul_pow, Nat.pow_mod, ← hy1_eq, ← Nat.pow_mod]
        try ring_nf

    · -- Case 2: Loop Terminates (i >= squarings)
      -- This contradicts the induction hypothesis (squarings - i = n + 1 >= 1)
      have : squarings.val - i.val = n + 1 := by assumption
      scalar_tac


/--
**Spec and proof concerning `montgomery_invert.square_multiply`**:
- Preconditions: Inputs `y` and `x` fit in 62-bit limbs.
- Postcondition:
  The result `res` satisfies: res * R^(2^squarings) = y^(2^squarings) * x (mod L)
-/
@[progress]
theorem square_multiply_spec (y : Scalar52) (squarings : Usize) (x : Scalar52)
    (hy : ∀ i < 5, y[i]!.val < 2 ^ 62) (hx : ∀ i < 5, x[i]!.val < 2 ^ 62) :
    ∃ res, montgomery_invert.square_multiply y squarings x = ok res ∧
    (Scalar52_as_Nat res * R ^ (pow2 squarings.val)) % L =
    ((Scalar52_as_Nat y) ^ (pow2 squarings.val) * (Scalar52_as_Nat x)) % L ∧
    (∀ i < 5, res[i]!.val < 2 ^ 62) := by
  sorry
  -- unfold montgomery_invert.square_multiply

  -- -- 1. Run the loop (squaring phase)
  -- -- Loop runs from 0 to squarings, so it runs `squarings` times.
  -- progress with square_multiply_loop_spec as ⟨y_pow, h_loop_eq, h_loop_bnds⟩
  -- · simp
  -- · exact hy

  -- -- 2. Run the multiplication phase
  -- -- y_pow is roughly y^(2^s) * R^(-(2^s - 1))
  -- progress with montgomery_mul_spec as ⟨res, h_mul_eq, h_mul_bnds⟩
  -- · exact h_loop_bnds
  -- · exact hx

  -- exists res
  -- constructor
  -- · exact h_mul_bnds
  -- · -- Algebra:
  --   -- 1. y_pow * R^(2^s - 1) = y^(2^s)
  --   -- 2. res * R = y_pow * x
  --   -- Combine to prove: res * R^(2^s) = y^(2^s) * x
  --   sorry

end curve25519_dalek.scalar.Scalar52
