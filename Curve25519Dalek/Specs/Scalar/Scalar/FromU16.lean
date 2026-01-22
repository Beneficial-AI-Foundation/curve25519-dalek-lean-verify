/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Aeneas.Std.WP

/-! # Spec Theorem for `Scalar::from(u16)`

Specification and proof for `FromScalarU16::from`.

This function embeds a u16 into a Scalar by writing its little-endian bytes.

**Source**: curve25519-dalek/src/scalar.rs
-/

open Aeneas
open scoped Aeneas
open scoped Aeneas.Std.WP
open Aeneas.Std Result
namespace curve25519_dalek.scalar.FromScalarU16

/-
natural language description:

    • Creates a Scalar whose byte representation contains the little-endian
      encoding of x in the first two bytes and zeros elsewhere.

natural language specs:

    • The resulting scalar encodes the same numeric value as x
    • The function always succeeds (no panic)
-/

/-- **Spec and proof concerning `scalar.FromScalarU16.from`**:
- No panic (always returns successfully)
- The resulting Scalar encodes the value x
-/
@[progress]
theorem from_spec (x : U16) :
  «from» x ⦃ s => U8x32_as_Nat s.bytes = x.val ⦄ := by
  unfold «from»
  progress*
  simp [core.array.Array.index_mut, Array.to_slice, Array.from_slice,
    core.slice.Slice.copy_from_slice, Array.repeat, Slice.len]
  classical
  -- The resulting array is the zero array with the 2-byte little-endian encoding of x
  -- written into the first two positions.
  set bytes : Array U8 32#usize :=
      (Array.repeat 32#usize 0#u8).setSlice! 0 (core.num.U16.to_le_bytes x).val
    with hbytes
  -- Reduce the goal to a sum over bytes.
  unfold U8x32_as_Nat
  let f : Nat → Nat := fun i => 2^(8 * i) * (bytes[i]!).val
  have hzero : ∀ i ∈ Finset.range 32, 2 ≤ i → f i = 0 := by
    intro i hi hi2
    have hi32 : i < 32 := by simpa using hi
    have hlen : (core.num.U16.to_le_bytes x).val.length = 2 := by simp
    have hbytes' :
        bytes[i]! = (Array.repeat 32#usize 0#u8)[i]! := by
      -- i ≥ 2 so we are in the suffix of the slice update
      have hle : 0 + (core.num.U16.to_le_bytes x).val.length ≤ i := by
        simpa [hlen] using hi2
      -- use Array.setSlice! suffix lemma
      simpa [bytes] using
        (Array.setSlice!_getElem!_suffix (s := Array.repeat 32#usize 0#u8)
          (s' := (core.num.U16.to_le_bytes x).val) (i := 0) (j := i) hle)
    have hrep : (Array.repeat 32#usize 0#u8)[i]! = 0#u8 := by
      -- reduce to List.replicate
      simpa [Array.repeat, Array.getElem!_Nat_eq] using
        (List.getElem!_replicate (a := 0#u8) (n := 32) (i := i) hi32)
    have hbytes0 : bytes[i]! = 0#u8 := by
      simpa [hbytes'] using hrep
    have hbytes0val : (bytes[i]!).val = 0 := by
      simpa [hbytes0]
    calc
      f i = 2^(8 * i) * (bytes[i]!).val := rfl
      _ = 2^(8 * i) * 0 := by
        rw [hbytes0val]
      _ = 0 := by simp
  have hsum :
      (∑ i ∈ Finset.range 32, f i) = ∑ i ∈ Finset.range 2, f i := by
    classical
    -- Sum over range 32 reduces to the first two indices since the rest are zero.
    have hsubset : (Finset.range 2) ⊆ Finset.range 32 := by
      intro i hi
      have hi' : i < 32 := by
        exact Nat.lt_trans (by simpa using hi) (by decide : (2:Nat) < 32)
      simpa using hi'
    -- Use sum_subset to drop zero terms.
    symm
    refine Finset.sum_subset hsubset ?_
    intro i hi hnot
    have hi2 : 2 ≤ i := by
      exact Nat.le_of_not_lt (by
        intro hi2'
        exact hnot (by simpa using hi2'))
    exact hzero i hi hi2
  -- Now compute the remaining two terms.
  have hlen : (core.num.U16.to_le_bytes x).val.length = 2 := by simp
  have h0 : bytes[0]! = (core.num.U16.to_le_bytes x).val[0]! := by
    have hmid : (0 ≤ 0 ∧ 0 - 0 < (core.num.U16.to_le_bytes x).val.length ∧
        0 < (Array.repeat 32#usize 0#u8).length) := by
      simp [hlen]
    simpa [bytes] using
      (Array.setSlice!_getElem!_middle (s := Array.repeat 32#usize 0#u8)
        (s' := (core.num.U16.to_le_bytes x).val) (i := 0) (j := 0) hmid)
  have h1 : bytes[1]! = (core.num.U16.to_le_bytes x).val[1]! := by
    have hmid : (0 ≤ 1 ∧ 1 - 0 < (core.num.U16.to_le_bytes x).val.length ∧
        1 < (Array.repeat 32#usize 0#u8).length) := by
      simp [hlen]
    simpa [bytes] using
      (Array.setSlice!_getElem!_middle (s := Array.repeat 32#usize 0#u8)
        (s' := (core.num.U16.to_le_bytes x).val) (i := 0) (j := 1) hmid)
  -- Remaining arithmetic over the two bytes.
  have hsum2 :
      (∑ i ∈ Finset.range 2, f i) =
        (bytes[0]!).val + 2^8 * (bytes[1]!).val := by
    -- range 2 = {0,1}
    have hsum2' : (∑ i ∈ Finset.range 2, f i) = f 0 + f 1 := by
      -- sum over range 2
      simp [Finset.sum_range_succ, f]
    -- simplify f 0 and f 1 without expanding getElem!
    rw [hsum2']
    simp only [f, Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.one_mul]
  -- TODO: relate the little-endian bytes to x.val
  -- The goal is now a byte-level characterization of U16.to_le_bytes.
  -- We keep this as a placeholder for a future bitvector lemma.
  -- (bitvec lemma likely: x.val = (bytes[0]!).val + 2^8 * (bytes[1]!).val)
  -- Use the computed reductions to rewrite the sum.
  have hsum' : (∑ i ∈ Finset.range 32, f i) =
      (bytes[0]!).val + 2^8 * (bytes[1]!).val := by
    simpa [hsum, hsum2]
  -- Finish once we prove the byte-level lemma for to_le_bytes.
  -- For now, leave as sorry.
  -- NOTE: This is the only remaining arithmetic/bitvector step.
  sorry

end curve25519_dalek.scalar.FromScalarU16
