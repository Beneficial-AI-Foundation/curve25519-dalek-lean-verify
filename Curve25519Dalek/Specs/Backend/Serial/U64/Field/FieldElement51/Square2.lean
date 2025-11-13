/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K

/-! # Spec Theorem for `FieldElement51::square2`

Specification and proof for `FieldElement51::square2`.

This function computes the square of the element and then doubles it.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result

set_option linter.hashCommand false
#setup_aeneas_simps

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Computes twice the square of a field element a in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs

natural language specs:

    • The function always succeeds (no panic)
    • Field51_as_Nat(result) ≡ 2 * Field51_as_Nat(a)² (mod p)
-/

/-- **Spec and proof concerning the loop in `backend.serial.u64.field.FieldElement51.square2`**:
- No panic when i ≤ 5
- Doubles each limb from index i onwards
- Leaves limbs before index i unchanged
-/
@[progress]
theorem square2_loop_spec (square : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (h_no_overflow : ∀ (j : Nat), j < 5 → i.val ≤ j → square[j]!.val * 2 ≤ U64.max) :
    ∃ r, square2_loop square i = ok r ∧
    (∀ (j : Nat), j < 5 → i.val ≤ j → r[j]!.val = square[j]!.val * 2) ∧
    (∀ (j : Nat), j < 5 → j < i.val → r[j]! = square[j]!) := by
  unfold square2_loop
  split
  · progress*
    · have := h_no_overflow i (by scalar_tac) (by simp)
      scalar_tac
    · intro j hj _
      have := h_no_overflow j hj
      have := h_no_overflow j (by scalar_tac) (by omega)
      have : i.val ≠ j := by scalar_tac
      simp_all
    · refine ⟨?_, ?_⟩
      · intro j hj _
        obtain hc | hc := (show j = i ∨ i + 1 ≤ j by omega)
        · simp_all
        · have := res_post_1 j hj (by omega)
          have := Array.set_of_ne' square i2 j i (by scalar_tac) (by omega)
          have := Array.val_getElem!_eq' square j (by scalar_tac)
          simp_all
      · intro j hj _
        have := res_post_2 j hj (by omega)
        simp_all
  · use square
    simp only [implies_true, and_true, true_and]
    intro j hj _
    have : j = 5 := by scalar_tac
    omega
  termination_by 5 - i.val
  decreasing_by scalar_decr_tac

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.square2`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to twice the square of the input modulo p
-/
@[progress]
theorem square2_spec (a : Array U64 5#usize) (h_bounds : ∀ i, i < 5 → a[i]!.val < 2 ^ 54) :
    ∃ r, square2 a = ok r ∧
    Field51_as_Nat r % p = (2 * (Field51_as_Nat a)^2) % p
    := by
  unfold square2
  have ⟨square, h_square, square_post_2, square_post_1⟩ := pow2k_spec a 1#u32 (by decide) h_bounds
  simp [h_square]
  progress*
  · intro j hj _
    have := square_post_1 j hj
    scalar_tac
  · have h_doubled : Field51_as_Nat res = 2 * Field51_as_Nat square := by
      unfold Field51_as_Nat
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      grind
    simp [Nat.ModEq] at square_post_2 ⊢
    rw [h_doubled, Nat.mul_mod, square_post_2, ← Nat.mul_mod]

end curve25519_dalek.backend.serial.u64.field.FieldElement51
