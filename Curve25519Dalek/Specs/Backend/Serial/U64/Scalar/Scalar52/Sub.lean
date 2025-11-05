/-
Copyright (c) 2024 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Defs

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 260

/-! # Sub

Specification and proof for `Scalar52::sub`.

This function computes the difference of two Scalar52 values modulo L (the group order).
The function performs subtraction with borrow handling and conditional addition of L
to ensure the result is non-negative.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs:L175-L198
-/

open Aeneas.Std Result
open curve25519_dalek
open backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
-- This activates/deactives some simps to reason about lists
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `sub` -/

/- Auxiliary definition to interpret a vector of `j` u64 limbs as a number (51-bit limbs) -/
def U64x5_slice_as_Nat (limbs : Array U64 5#usize) (j : Nat) : Nat :=
  ∑ i ∈ Finset.range j, 2^(51 * i) * (limbs[i]!).val

/-- Slicing zero limbs yields zero. -/
@[simp]
theorem U64x5_slice_as_Nat_zero (limbs : Array U64 5#usize) :
    U64x5_slice_as_Nat limbs 0 = 0 := by
  simp [U64x5_slice_as_Nat]

/-- Slicing up to `j.succ` adds the `j`-th limb contribution. -/
@[simp]
theorem U64x5_slice_as_Nat_succ (limbs : Array U64 5#usize) (j : Nat) :
    U64x5_slice_as_Nat limbs (j.succ) =
      U64x5_slice_as_Nat limbs j + 2^(51 * j) * (limbs[j]!).val := by
  have h :=
    Finset.sum_range_succ (fun i => 2^(51 * i) * (limbs[i]!).val) j
  simpa [U64x5_slice_as_Nat, add_comm, add_left_comm, add_assoc]
    using h

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub_loop`**: -/
@[progress]
theorem sub_loop_spec (mask : U64) (a b difference : Array U64 5#usize) (borrow : U64) (i : Usize)
    (ha : ∀ j, j < 5 → (a[j]!).val < 2 ^ 52) (hb : ∀ j, j < 5 → (b[j]!).val < 2 ^ 52)
    (hd : ∀ j, j < i.val → difference[j]!.val < 2 ^ 52)
    (hd_rest : ∀ j, i.val ≤ j → j < 5 → difference[j]!.val = 0)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5)
    (hborrow : borrow.val.testBit 63 = false ∨ borrow.val.testBit 63 = true) :
    ∃ difference' borrow', sub_loop mask a b difference borrow i = ok (difference', borrow') ∧
    U64x5_slice_as_Nat a i + 2 ^ (52 * i.val) * (if borrow.val.testBit 63 then 1 else 0) =
      U64x5_slice_as_Nat b i + U64x5_slice_as_Nat difference' i +
      2 ^ (52 * 5) * (if borrow'.val.testBit 63 then 1 else 0) ∧
    (∀ j, j < 5 → difference'[j]!.val < 2 ^ 52)
  := by
  unfold sub_loop
  unfold backend.serial.u64.scalar.Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  unfold backend.serial.u64.scalar.IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
  by_cases hlt : i < 5#usize
  · have hi_lt : i.val < 5 := by simpa using hlt
    -- Recursive case: establish updated bounds and invariant, then recurse.
    progress*
    · -- hmax: show i2 + i3 ≤ U64.max
      -- i3 = borrow >>> 63 is either 0 or 1, and i2 < 2^52 < U64.max
      rw [i2_post]
      have hb_val : (b[i.val]!).val < 2 ^ 52 := hb i.val hi_lt
      -- Use scalar_tac for U64 arithmetic bounds - it handles shiftRight automatically
      scalar_tac
    · -- hd: show bounds for all limbs up to i6
      intro j hj
      have hj_eq : j < ↑i6 := by simpa using hj
      have hj_lt : j < ↑i + 1 := by simpa [i6_post] using hj_eq
      by_cases h : j < ↑i
      · -- j < i: use existing bound
        have := hd j h
        simp_all [Array.getElem!_Nat_eq, Array.set_val_eq]
        -- j ≠ i.val is already handled by simp_all
      · -- j = i: show i5 < 2^52
        have hj_eq : j = i.val := by omega
        simp_all [Array.getElem!_Nat_eq, Array.set_val_eq]
        -- Goal is already of the form x % 2^52 < 2^52, apply mod_lt directly
        apply Nat.mod_lt
        omega
    · -- hd_rest: show limbs from i6 onwards are still 0
      intro j hj_le hj_lt
      simp_all [Array.getElem!_Nat_eq, Array.set_val_eq]
      have : ↑i < j := by omega
      have : i.val ≠ j := by omega
      -- Use hd_rest since we only modified index i, and j > i
      -- Need to show that setting i doesn't affect j when j ≠ i
      have hj_bounds : j < difference.length := by simpa using hj_lt
      have hi_bounds : i.val < difference.length := by simpa using hi_lt
      have h_ne : i.val ≠ j := by omega
      -- Use set_of_ne: setting index i.val doesn't affect index j
      have : ((difference.set i i5)[j]!).val = difference[j]!.val := by
        simp [Array.set_of_ne difference i5 j i.val hj_bounds hi_bounds h_ne]
      simp_all [this]
      exact hd_rest j (by omega) hj_lt
    · -- Main goal: combine recursive result with current step
      refine ⟨res_1, res_2, ?_, ?_⟩
      · rfl
      · refine ⟨?_, ?_⟩
        · rfl
        · refine ⟨?_, ?_⟩
          · -- Arithmetic invariant: need to show the equation holds for i given it holds for i6
            sorry
          · -- Bounds from res_post_2
            intro j hj
            -- res_post_2: ↑res_1[j]! < 4503599627370496 where 4503599627370496 = 2^52
            have : ↑res_1[j]! < 2 ^ 52 := by
              have := res_post_2 j hj
              simpa using this
            exact this
  · have hnot : ¬ i.val < 5 := by
      simpa using hlt
    have hge : 5 ≤ i.val := Nat.le_of_not_lt hnot
    have hi_eq : i.val = 5 := Nat.le_antisymm hi hge
    refine ⟨difference, borrow, ?_, ?_, ?_⟩
    · simp [hlt]
    · -- TODO: arithmetic invariant when the loop terminates.
      sorry
    · intro j hj
      have : j < i.val := by simpa [hi_eq]
      exact hd j this

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub`**:
- Does not error and hence returns a result
- The result represents (a - b) mod L where L is the group order
- Requires that input limbs are within bounds (52-bit values) -/
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 52)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 52) :
    ∃ result, sub a b = ok result ∧
    Scalar52_as_Nat result ≡ (Scalar52_as_Nat a - Scalar52_as_Nat b) [MOD L] := by
  unfold sub
  progress*
  -- TODO: combine loop result, conditional addition, and congruence properties.
  sorry
