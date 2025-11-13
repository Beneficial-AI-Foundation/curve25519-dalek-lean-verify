/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K

/-! # Spec Theorem for `FieldElement51::square`

Specification and proof for `FieldElement51::square`.

This function computes the square of the element.

Source: curve25519-dalek/src/backend/serial/u64/field.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Computes the square of a field element a in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs

natural language specs:

    • The function always succeeds (no panic)
    • U64x5_as_Nat(result) ≡ U64x5_as_Nat(a)² (mod p)
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.square`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to the square of the input modulo p
- Note: this implements the `pow2k` function with k=1
-/
@[progress]
theorem square_spec (a : Array U64 5#usize) (h_bounds : ∀ i, i < 5 → a[i]!.val < 2 ^ 54) :
    ∃ r, square a = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^2 [MOD p] := by
  unfold square
  obtain ⟨r, h_eq, ⟨h_mod, _⟩⟩ := pow2k_spec a 1#u32 (by decide) h_bounds
  exact ⟨r, h_eq, by simp_all⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51
