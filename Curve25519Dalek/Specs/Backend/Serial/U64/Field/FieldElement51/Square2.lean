/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K

/-! # Spec Theorem for `FieldElement51::square2`

Specification and proof for `FieldElement51::square2`.

This function computes the square of the element and then doubles it.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

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
@[step]
theorem square2_loop_spec (square : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (h_no_overflow : ∀ j < 5, i.val ≤ j → square[j]!.val * 2 ≤ U64.max) :
    square2_loop square i ⦃ (result : FieldElement51) =>
      (∀ j < 5, i.val ≤ j → result[j]!.val = square[j]!.val * 2) ∧
      (∀ j < 5, j < i.val → result[j]! = square[j]!) ⦄ := by
  unfold square2_loop
  split
  · let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
    let* ⟨ i2, i2_post ⟩ ← U64.mul_spec
    let* ⟨ a, a_post ⟩ ← Array.update_spec
    let* ⟨ i3, i3_post ⟩ ← Usize.add_spec
    let* ⟨ result, result_post1, result_post2 ⟩ ← square2_loop_spec
    case h_no_overflow =>
      intro j hj hj2
      simp_all only [Array.getElem!_Nat_eq, UScalar.lt_equiv, UScalar.ofNatCore_val_eq,
        Order.add_one_le_iff, Array.set_val_eq, Nat.not_eq, ne_eq, true_or, or_true,
        ↓List.getElem!_set_ne]
      exact h_no_overflow j hj (by omega)
    refine ⟨fun j _ _ ↦ ?_, fun j _ _ ↦ ?_⟩
    · obtain _ | _ := (show j = i ∨ i + 1 ≤ j by omega) <;> simp_all
    · have := result_post2 j (by omega) (by omega)
      simp_all
  · simp only [step_simps]
    grind
  termination_by 5 - i.val
  decreasing_by scalar_tac

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.square2`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to twice the square of the input
  modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^53
-/
@[step]
theorem square2_spec (self : Array U64 5#usize) (h_bounds : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square2 self ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (2 * (Field51_as_Nat self) ^ 2) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 53) ⦄ := by
  unfold square2
  let* ⟨ square, square_post2, square_post1 ⟩ ← pow2k_spec
  let* ⟨ result, result_post1, result_post2 ⟩ ← square2_loop_spec
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have : Field51_as_Nat result = 2 * Field51_as_Nat square := by
      unfold Field51_as_Nat
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have := result_post1 x (Finset.mem_range.mp hx) (by omega)
      rw [this]; ring
    grind [Nat.ModEq, Nat.mul_mod]
  · have := result_post1 i hi (by omega)
    have := square_post1 i hi
    omega

end curve25519_dalek.backend.serial.u64.field.FieldElement51
