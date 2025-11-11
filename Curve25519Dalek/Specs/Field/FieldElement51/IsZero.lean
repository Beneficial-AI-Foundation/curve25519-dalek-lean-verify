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

/-! # Spec Theorem for `FieldElement51::is_zero`

Specification and proof for `FieldElement51::is_zero`.

This function checks whether a field element is zero.

**Source**: curve25519-dalek/src/field.rs


-/

open Aeneas.Std Result
namespace curve25519_dalek.field.FieldElement51

/-
Natural language description:

    • Checks whether a field element is zero in 𝔽_p where p = 2^255 - 19
    • The field element is represented in radix 2^51 form with five u64 limbs
    • Returns a subtle.Choice value (0 for false, 1 for true)

Natural language specs:

    • The function succeeds (no panic)
    • For any field element r, the result c satisfies:
      - c.val = 1 if and only if Field51_as_Nat(r) ≡ 0 (mod p)
-/

/-- **Spec and proof concerning `field.FieldElement51.is_zero`**:
- No panic for field element inputs r (always returns c successfully)
- c.val = 1 ↔ Field51_as_Nat(r) ≡ 0 (mod p)
-/



lemma Choice.val_eq_one_iff (c : subtle.Choice) : c.val = 1#u8 ↔ c = Choice.one := by
  cases c with
  | mk val valid =>
    simp [Choice.one]



lemma array_eq_of_to_slice_eq
    {α : Type} {n : Usize}
    {h1 h2 : Array α n}
    (h : h1.to_slice = h2.to_slice) :
    h1 = h2 := by
  -- Unfold definition
  simp [Array.to_slice] at h
  -- Reduce equality between subtypes
  cases h1; cases h2
  simp at h
  cases h
  rfl









@[progress]
theorem is_zero_spec (r : backend.serial.u64.field.FieldElement51) :
    ∃ c, is_zero r = ok c ∧
    (c.val = 1#u8 ↔ Field51_as_Nat r % p = 0)
    := by
  unfold is_zero
  progress as ⟨bytes, h_to_bytes⟩
  progress as ⟨s, h_bytes_slice⟩
  progress as ⟨s1, h_zero_slice⟩
  progress as ⟨result, h_ct_eq⟩

  constructor
  · intro h
    have s_eq_s1 : s = s1 := by
      exact h_ct_eq.mp ((Choice.val_eq_one_iff result).mp h)
    rw [h_bytes_slice, h_zero_slice] at s_eq_s1
    have heq : bytes = Array.repeat 32#usize 0#u8 := by
      apply array_eq_of_to_slice_eq
      exact s_eq_s1
    rw [heq, Nat.ModEq] at h_to_bytes
    rw [← h_to_bytes]
    unfold U8x32_as_Nat
    iterate 31 (rw [Finset.sum_range_succ])
    rw [Finset.sum_range_one]
    simp [Array.repeat]

  · intro h
    rename_i h1
    rw [Nat.ModEq, h] at h_to_bytes
    have h_bytes_zero : U8x32_as_Nat bytes = 0 := by
      have h2 := Nat.mod_eq_of_lt h1
      rw [h2] at h_to_bytes
      exact h_to_bytes

    have bytes_eq : bytes = Array.repeat 32#usize 0#u8 := by
      unfold U8x32_as_Nat at h_bytes_zero
      simp_all
      apply Subtype.ext
      apply List.ext_getElem
      repeat simp
      intro i hi _
      have hi_val := h_bytes_zero i hi
      -----
      interval_cases i
      all_goals simp [Array.repeat, List.replicate]; scalar_tac
      -----

    have s_eq_s1 : s = s1 := by
      rw [h_bytes_slice, h_zero_slice, bytes_eq]
    rw [← h_ct_eq] at s_eq_s1
    simp [s_eq_s1, Choice.one]



end curve25519_dalek.field.FieldElement51
