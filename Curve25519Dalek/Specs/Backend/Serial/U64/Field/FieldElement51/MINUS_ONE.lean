/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `FieldElement51::MINUS_ONE`

Specification and proof for `FieldElement51::MINUS_ONE`.

This constant represents the field element -1, i.e., the additive inverse of the
multiplicative identity element in the field. This is congruent to p-1 (mod p) with p = 2^255 - 19.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std.WP Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Represents the additive inverse of the multiplicative identity element in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs:

        [2251799813685228, 2251799813685247, 2251799813685247, 2251799813685247, 2251799813685247]

    • This is the constant field element with value p - 1 (equivalent to -1 mod p)

natural language specs:

    • Field51_as_Nat(MINUS_ONE) = 2^255 - 20 = p - 1
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.MINUS_ONE`**:
- The constant, when converted to a natural number, equals 2^255 - 20 (i.e., p - 1)
-/
@[progress]
theorem MINUS_ONE_spec : MINUS_ONE ⦃ result => Field51_as_Nat result = p - 1 ⦄ := by
    unfold MINUS_ONE from_limbs
    simp only [spec_ok];
    decide

end curve25519_dalek.backend.serial.u64.field.FieldElement51
