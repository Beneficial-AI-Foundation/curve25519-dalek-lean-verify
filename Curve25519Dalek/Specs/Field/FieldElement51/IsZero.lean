/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce


set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 10000000000000

/-! # Spec Theorem for `FieldElement51::is_zero`

Specification and proof for `FieldElement51::is_zero`.

This function checks whether a field element is zero.

**Source**: curve25519-dalek/src/field.rs

## TODO
- Complete proof
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

lemma to_bytes_ok_extract (r : backend.serial.u64.field.FieldElement51) (h1 : Aeneas.Std.Array U8 32#usize)
    (h2 : r.to_bytes = ok h1) : ∃ v,  r.to_bytes = ok v ∧ v = h1 := by
  exists h1


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
    cases h : r.to_bytes
    repeat progress
    constructor
    intro h
    --unfold Field51_as_Nat
    rename_i h1 h2 h3 h4 h5 h6 h7 h8
    --rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,Finset.sum_range_one]
    have h3eqh5 : h3 = h5 := h8.mp ((Choice.val_eq_one_iff h7).mp h)
    rw[h4,h6,] at h3eqh5
    have heq: h1 = (Array.repeat 32#usize 0#u8) := by
        apply array_eq_of_to_slice_eq
        exact h3eqh5

    set zero:= (Array.repeat 32#usize 0#u8) with hzero
    rw [heq,hzero] at h2
    revert h2
    unfold backend.serial.u64.field.FieldElement51.to_bytes
    obtain ⟨a, ha_ok,h_bounds_a,hao_mod⟩ := reduce_spec r
    simp only [ha_ok, bind_tc_ok]
    
     -- Index a[0]
    have hlen_a0 : 0#usize < a.length := by scalar_tac
    obtain ⟨a0, ha0_ok⟩ := Array.index_usize_spec a 0#usize hlen_a0
    simp only [ha0_ok, bind_tc_ok, UScalar.ofNat_val_eq]
    generalize ha0 : (a.val)[0]! = a0

    have ha0_bound : a0.val + 19#u64 ≤ U64.max := by
      have := h_bounds_a 0 (by simp)
      scalar_tac
    obtain ⟨a0', ha0'_ok, ha0'_val⟩ := U64.add_spec ha0_bound
    simp only [ha0'_ok, bind_tc_ok]




    have ha0'_bound : a0'.val >>> (51:Nat) ≤ U64.max := by
      have := h_bounds_a 0 (by simp)
      scalar_tac
    
      
    
    











end curve25519_dalek.field.FieldElement51



  