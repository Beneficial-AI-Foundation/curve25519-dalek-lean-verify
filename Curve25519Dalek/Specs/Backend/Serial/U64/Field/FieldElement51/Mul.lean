/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::mul`

Specification and proof for `FieldElement51::mul`.

This function computes the product of two field elements.

Source: curve25519-dalek/src/backend/serial/u64/field.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Mul

/-
natural language description:

    • Computes the product of two field elements a and b in the field 𝔽_p where p = 2^255 - 19
    • The field elements are represented as five u64 limbs each

natural language specs:

    • The function always succeeds (no panic)
    • Field51_as_Nat(result) ≡ Field51_as_Nat(lhs) * Field51_as_Nat(rhs) (mod p)
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.Mul.mul`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to the product of the inputs modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^52
-/
@[progress]
theorem mul_spec (lhs rhs : Array U64 5#usize)
    (hlhs : ∀ i < 5, lhs[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, rhs[i]!.val < 2 ^ 54) :
    ∃ r, mul lhs rhs = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Mul
