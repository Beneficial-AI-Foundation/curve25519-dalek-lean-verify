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

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas
open scoped Aeneas
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
    (h_no_overflow : ∀ j < 5, i.val ≤ j → square[j]!.val * 2 ≤ U64.max) :
    square2_loop square i ⦃ r =>
      (∀ j < 5, i.val ≤ j → r[j]!.val = square[j]!.val * 2) ∧
      (∀ j < 5, j < i.val → r[j]! = square[j]!) ⦄ := by
  sorry

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.square2`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to twice the square of the input modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^53
-/
@[progress]
theorem square2_spec (a : Array U64 5#usize) (h_bounds : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    square2 a ⦃ r =>
      Field51_as_Nat r % p = (2 * (Field51_as_Nat a)^2) % p ∧
      (∀ i < 5, r[i]!.val < 2 ^ 53) ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
