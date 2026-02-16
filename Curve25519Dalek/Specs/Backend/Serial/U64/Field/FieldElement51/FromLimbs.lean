/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `FieldElement51::from_limbs`

Specification and proof for `FieldElement51::from_limbs`.

This function constructs a field element from an array of five u64 limbs.
Since `FieldElement51` is just a type alias for `Array U64 5#usize`, this function
is essentially the identity function wrapped in a `Result` type.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
Natural language description:

    • Constructs a field element from five u64 limbs representing a field element in 𝔽_p where p = 2^255 - 19
    • The assumed representation for a field element is in radix 2^51 form
    • Since FieldElement51 is a just type alias for `Array U64 5#usize` in Lean, this is
      merely the identity function wrapped in `Result`

Natural language specs:

    • The function always succeeds (no panic)
    • The result is identical to the input limbs array
    • Field51_as_Nat(result) = Field51_as_Nat(limbs) (trivially, since result = limbs)
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.from_limbs`**:
- No panic (always returns successfully)
- The result is identical to the input limbs array
- The natural number representation of the result equals that of the input
-/
@[progress]
theorem from_limbs_spec (a : Array U64 5#usize) :
    spec (from_limbs a) (fun r =>
    r = a ∧ Field51_as_Nat r = Field51_as_Nat a) := by
  simp [from_limbs]

end curve25519_dalek.backend.serial.u64.field.FieldElement51
