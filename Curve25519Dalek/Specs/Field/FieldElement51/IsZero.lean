/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
/-!
# Spec Theorem for `FieldElement51::is_zero`

Specification and proof for `FieldElement51::is_zero`.

This function checks whether a field element is zero.

Source: "curve25519-dalek/src/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

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

/-- Arrays are equal if their slices are equal. -/
lemma array_eq_of_to_slice_eq {α : Type} {n : Usize} {h1 h2 : Array α n}
    (h : h1.to_slice = h2.to_slice) :
    h1 = h2 := by
  simp only [Array.to_slice] at h
  cases h1; cases h2
  simp only at h
  cases h
  rfl

/-! ## Workaround for `progress` timeout

The `progress` tactic runs `simp` on **all hypotheses** in the context. After `progress`
processes `to_bytes`, the postconditions involving `U8x32_as_Nat` / `Field51_as_Nat` are
expensive for `simp` to reduce (whnf timeout), causing any subsequent `progress` call to
time out.

Workaround:
1. Use `simp only [lift, bind_tc_ok] at ⊢` to reduce the pure `Array.to_slice` binds
   without touching hypotheses (bypasses `progress` for those steps).
2. Wrap the expensive hypotheses in `Hold` (opaque to `simp`) before calling `progress`
   on `ct_eq`.
3. Recover with `change ... at` afterwards (`Hold P` is defeq to `P`).
-/

private def Hold (P : Prop) : Prop := P

@[progress]
theorem is_zero_spec (r : backend.serial.u64.field.FieldElement51) :
    is_zero r ⦃ c =>
    (c.val = 1#u8 ↔ Field51_as_Nat r % p = 0) ⦄ := by
  unfold is_zero
  progress as ⟨bytes, h_to_bytes_mod, h_to_bytes_lt⟩
  simp only [lift, bind_tc_ok] at ⊢
  have h_mod : Hold (U8x32_as_Nat bytes ≡ Field51_as_Nat r [MOD p]) := h_to_bytes_mod
  have h_lt : Hold (U8x32_as_Nat bytes < p) := h_to_bytes_lt
  clear h_to_bytes_mod h_to_bytes_lt
  progress as ⟨result, h_ct_eq⟩
  change U8x32_as_Nat bytes ≡ Field51_as_Nat r [MOD p] at h_mod
  change U8x32_as_Nat bytes < p at h_lt
  -- Step 6: prove the iff
  constructor
  · intro h
    have h_eq : result = Choice.one := (Choice.val_eq_one_iff result).mp h
    have h_slice_eq := h_ct_eq.mp h_eq
    have heq : bytes = Array.repeat 32#usize 0#u8 := array_eq_of_to_slice_eq h_slice_eq
    rw [heq, Nat.ModEq] at h_mod
    rw [← h_mod]
    unfold U8x32_as_Nat
    iterate 31 (rw [Finset.sum_range_succ])
    rw [Finset.sum_range_one]
    simp [Array.repeat]
  · intro h
    rw [Nat.ModEq, h] at h_mod
    have h_bytes_zero : U8x32_as_Nat bytes = 0 := by
      have h2 := Nat.mod_eq_of_lt h_lt
      rw [h2] at h_mod
      exact h_mod
    have bytes_eq : bytes = Array.repeat 32#usize 0#u8 := by
      unfold U8x32_as_Nat at h_bytes_zero
      simp_all only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_eq_zero_iff,
        Finset.mem_range, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem?_pos,
        Option.getD_some, mul_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_or,
        false_and]
      apply Subtype.ext
      apply List.ext_getElem
      repeat simp only [List.Vector.length_val, UScalar.ofNatCore_val_eq, Array.repeat_val,
        List.reduceReplicate, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
      intro i hi _
      have hi_val := h_bytes_zero i hi
      interval_cases i
      all_goals simp only [List.getElem_cons_succ, List.getElem_cons_zero]; agrind
    have h_slice_eq : Array.to_slice bytes =
        Array.to_slice (Array.repeat 32#usize 0#u8) := by rw [bytes_eq]
    exact (Choice.val_eq_one_iff result).mpr (h_ct_eq.mpr h_slice_eq)

end curve25519_dalek.field.FieldElement51
