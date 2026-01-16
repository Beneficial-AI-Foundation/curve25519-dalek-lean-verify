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

open Aeneas
open scoped Aeneas
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
    montgomery_invert.square_multiply_loop y squarings i ⦃ res =>
      (Scalar52_as_Nat res * R ^ (pow2 (squarings.val - i.val) - 1)) % L =
        (Scalar52_as_Nat y) ^ (pow2 (squarings.val - i.val)) % L ∧
      (∀ j < 5, res[j]!.val < 2 ^ 62) ⦄ := by
  sorry

@[progress]
theorem square_multiply_spec (y : Scalar52) (squarings : Usize) (x : Scalar52)
    (hy : ∀ i < 5, y[i]!.val < 2 ^ 62) (hx : ∀ i < 5, x[i]!.val < 2 ^ 62) :
    montgomery_invert.square_multiply y squarings x ⦃ res =>
      (Scalar52_as_Nat res * R ^ (pow2 squarings.val)) % L =
        ((Scalar52_as_Nat y) ^ (pow2 squarings.val) * (Scalar52_as_Nat x)) % L ∧
      (∀ i < 5, res[i]!.val < 2 ^ 62) ⦄ := by
  sorry

end curve25519_dalek.scalar.Scalar52
