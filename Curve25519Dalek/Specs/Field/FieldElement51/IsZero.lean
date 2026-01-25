/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 10000000000000

/-!
# Spec Theorem for `FieldElement51::is_zero`

Specification and proof for `FieldElement51::is_zero`.

This function checks whether a field element is zero.

**Source**: curve25519-dalek/src/field.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result

namespace curve25519_dalek.field.FieldElement51

/-!
Natural language description:

- Checks whether a field element is zero in 𝔽_p, p = 2^255 - 19.
- Field element is in radix 2^51 with five u64 limbs.
- Returns a `subtle.Choice` (0 = false, 1 = true).

Spec:

- Function succeeds (no panic).
- For any field element `r`, result `c` satisfies
  `c.val = 1 ↔ Field51_as_Nat(r) % p = 0`.
-/

/-- Spec and proof concerning `FieldElement51.is_zero`. -/
lemma Choice.val_eq_one_iff (c : subtle.Choice) :
  c.val = 1#u8 ↔ c = Choice.one := by
  cases c with
  | mk val valid =>
    simp [Choice.one]

/-- Arrays are equal if their slices are equal. -/
lemma array_eq_of_to_slice_eq {α : Type} {n : Usize} {h1 h2 : Array α n}
    (h : h1.to_slice = h2.to_slice) :
    h1 = h2 := by
  simp [Array.to_slice] at h
  cases h1; cases h2
  simp at h
  cases h
  rfl

@[progress]
theorem is_zero_spec (r : backend.serial.u64.field.FieldElement51) :
    is_zero r ⦃ c =>
      (c.val = 1#u8 ↔ Field51_as_Nat r % p = 0) ⦄ := by
  sorry

end curve25519_dalek.field.FieldElement51
