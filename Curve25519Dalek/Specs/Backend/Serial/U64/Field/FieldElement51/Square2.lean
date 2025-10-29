/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::square2`

Specification and proof for `FieldElement51::square2`.

This function computes the square of the element and then doubles it.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Computes twice the square of a field element a in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs

natural language specs:

    • The function always succeeds (no panic)
    • Field51_as_Nat(result) ≡ 2 * Field51_as_Nat(a)² (mod p)
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.square2`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to twice the square of the input modulo p
-/
theorem square2_spec (a : Array U64 5#usize) :
    ∃ r,
    square2 a = ok r ∧
    Field51_as_Nat r % p = (2 * (Field51_as_Nat a)^2) % p
    := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
