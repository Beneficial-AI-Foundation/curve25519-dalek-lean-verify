/-
Copyright 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
import Mathlib.FieldTheory.Finite.Basic

/-! In a finite field of odd characteristic, the product of two non-squares is a square.
This follows from the Euler criterion: non-squares satisfy `a ^ (q / 2) = -1`,
so their product satisfies `(a * b) ^ (q / 2) = (-1)(-1) = 1`.

TODO: These results belong in `Mathlib.FieldTheory.Finite.Basic`, near `FiniteField.isSquare_iff`.
-/

/-- In a finite field of odd characteristic, the product of two non-squares is a square. -/
theorem FiniteField.isSquare_mul_of_not_isSquare {F : Type*} [Field F] [Finite F]
    (hchar : ringChar F ≠ 2) {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  have := Fintype.ofFinite F
  have ha0 : a ≠ 0 := by intro h; exact ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := by intro h; exact hb (h ▸ IsSquare.zero)
  have half_pow_neg {z : F} (hz : z ≠ 0) (hns : ¬ IsSquare z) :
      z ^ (Fintype.card F / 2) = -1 :=
    (FiniteField.pow_dichotomy hchar hz).resolve_left
      (fun h1 => hns ((FiniteField.isSquare_iff hchar hz).mpr h1))
  rw [FiniteField.isSquare_iff hchar (mul_ne_zero ha0 hb0),
      mul_pow, half_pow_neg ha0 ha, half_pow_neg hb0 hb]
  norm_num

/-- In `ZMod n` for an odd prime `n`, the product of two non-squares is a square. -/
theorem ZMod.isSquare_mul_of_not_isSquare {n : ℕ} [Fact (Nat.Prime n)] (hodd : n ≠ 2)
    {a b : ZMod n} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) :=
  FiniteField.isSquare_mul_of_not_isSquare (by rwa [ZMod.ringChar_zmod_n]) ha hb
