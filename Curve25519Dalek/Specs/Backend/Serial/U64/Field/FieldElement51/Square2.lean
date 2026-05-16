/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::square2`

This function computes `2 * a^2` for a `FieldElement51` `a` in 𝔽_p (p = 2^255 - 19). It first
squares the element via `pow2k` and then doubles each limb.

Source: "curve25519-dalek/src/backend/serial/u64/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

set_option linter.hashCommand false
#setup_aeneas_simps

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- **Spec theorem for the inner loop `square2_loop` of `square2`**
• The function always succeeds (no panic) when `i ≤ 5` and every remaining limb satisfies
  `square[j] * 2 ≤ U64.max`
• Each limb from index `i` onwards is doubled: `result[j].val = square[j].val * 2`
• Limbs before index `i` are left unchanged -/
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
    · refine ⟨fun j _ _ ↦ ?_, by grind⟩
      obtain _ | _ := (show j = i ∨ i + 1 ≤ j by omega) <;> grind
  · simp only [step_simps]
    grind
  termination_by 5 - i.val
  decreasing_by scalar_tac

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::square2`**
• The function always succeeds (no panic) provided every input limb is `< 2 ^ 54`
• `Field51_as_Nat result ≡ 2 * (Field51_as_Nat self)^2 (mod p)`
• Every output limb is `< 2 ^ 53`
-/
@[step]
theorem square2_spec (self : Array U64 5#usize) (h_bounds : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square2 self ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (2 * (Field51_as_Nat self) ^ 2) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 53) ⦄ := by
  unfold square2
  let* ⟨ square, square_post2, square_post1 ⟩ ← pow2k_spec
  let* ⟨ result, result_post1, result_post2 ⟩ ← square2_loop_spec
  refine ⟨?_, by grind⟩
  have : Field51_as_Nat result = 2 * Field51_as_Nat square := by
    unfold Field51_as_Nat
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    grind
  grind [Nat.ModEq, Nat.mul_mod]

end curve25519_dalek.backend.serial.u64.field.FieldElement51
