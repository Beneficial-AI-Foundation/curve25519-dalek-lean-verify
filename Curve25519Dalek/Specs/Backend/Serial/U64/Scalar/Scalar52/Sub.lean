/-
Copyright (c) 2024 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.ConditionalAddL
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Zero

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

## Algorithm Summary

The subtraction uses base-2^52 arithmetic with borrow propagation:

1. **Loop iteration**: For each limb i:
   - `borrow = a[i].wrapping_sub(b[i] + (borrow >> 63))`
   - `difference[i] = borrow & mask` (keep lower 52 bits)

2. **Borrow detection**: `borrow >> 63` extracts a 0/1 flag:
   - 0 if no underflow occurred
   - 1 if underflow occurred (wrapped value has top bits set)

3. **Telescoping property**: The borrows cancel perfectly:
   - `difference[i] = (a[i] - b[i] - c_i) mod 2^52 = a[i] - b[i] - c_i + c_{i+1} * 2^52`
   - Summing: `Σ difference[i] * 2^(52*i) = A - B + c_5 * 2^260`

4. **Final correction**: If `c_5 = 1` (final borrow set), then `A < B`, so add L
   to get a positive result in `[0, L)`.

**Key insight**: The final borrow `c_5` is just a sign indicator, not a quantity to subtract.
When `A < B`, the difference array stores `2^260 + (A - B)` (the representation in Z/(2^260)Z).
Adding L causes wrap-around: `(2^260 + (A - B) + L) mod 2^260 = A - B + L ∈ (0, L)`.
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
-- This activates/deactives some simps to reason about lists
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `sub` -/

/-- Partial sum of limbs up to index n: Σ (j < n) limbs[j] * 2^(52*j) -/
def Scalar52_partial_as_Nat (limbs : Array U64 5#usize) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, 2 ^ (52 * j) * (limbs[j]!).val

set_option maxHeartbeats 4000000 in
/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub_loop`**:

The loop computes the subtraction a - b with borrow propagation.
After processing indices 0..i, the loop invariant holds:
  partial_a(i) + (borrow / 2^63) * 2^(52*i) = partial_b(i) + partial_diff(i)

When the loop completes (i = 5), this gives:
  A + (borrow / 2^63) * 2^260 = B + D

Where (borrow / 2^63) = 1 means A < B (underflow occurred), and the difference D
represents (A - B) mod 2^260.
-/
@[progress]
theorem sub_loop_spec (a b difference : Scalar52) (mask borrow : U64) (i : Usize)
    (ha : ∀ j < 5, a[j]!.val < 2 ^ 52)
    (hb : ∀ j < 5, b[j]!.val < 2 ^ 52)
    (hdiff : ∀ j < i.val, difference[j]!.val < 2 ^ 52)
    (hdiff_rest : ∀ j, i.val ≤ j → j < 5 → difference[j]!.val = 0)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5)
    (hborrow : borrow.val / 2 ^ 63 ≤ 1)
    (hinv : Scalar52_partial_as_Nat a i.val + borrow.val / 2 ^ 63 * 2 ^ (52 * i.val) =
            Scalar52_partial_as_Nat b i.val + Scalar52_partial_as_Nat difference i.val) :
    ∃ result, sub_loop a b difference mask borrow i = ok result ∧
    (∀ j < 5, result.1[j]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat a + result.2.val / 2 ^ 63 * 2 ^ 260 =
     Scalar52_as_Nat b + Scalar52_as_Nat result.1) := by
  unfold sub_loop
  unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  unfold IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
  split
  case isTrue hlt =>
    have hi' : i.val < 5 := by scalar_tac
    have ha_i : a[i.val]!.val < 2 ^ 52 := ha i.val hi'
    have hb_i : b[i.val]!.val < 2 ^ 52 := hb i.val hi'
    have hborrow_bit : borrow.val >>> 63 ≤ 1 := by
      have hbv : borrow.val < 2 ^ 64 := by scalar_tac
      omega
    -- Step through the operations manually
    progress as ⟨i1, hi1⟩  -- a[i]
    progress as ⟨i2, hi2⟩  -- b[i]
    progress as ⟨i3, hi3_1, hi3_2⟩  -- borrow >>> 63
    have hi3_bound : i3.val ≤ 1 := by simp [hi3_1]; exact hborrow_bit
    have hi2_bound : i2.val < 2 ^ 52 := by simp only [hi2]; simp_all
    have hi4_ok : i2.val + i3.val < 2 ^ 64 := by omega
    progress as ⟨i4, hi4⟩  -- i2 + i3
    progress as ⟨borrow1, hborrow1⟩  -- wrapping_sub
    progress as ⟨x, index_mut_back⟩  -- index_mut
    progress as ⟨i5, hi5_1, hi5_2⟩  -- borrow1 &&& mask
    progress as ⟨i6, hi6⟩  -- i + 1
    -- Set up the recursive call hypotheses
    have hborrow1_bound : borrow1.val / 2 ^ 63 ≤ 1 := by
      have hb1 : borrow1.val < 2 ^ 64 := by scalar_tac
      omega
    -- i5 = borrow1 &&& mask = borrow1 % 2^52
    have hi5_mod : i5.val = borrow1.val % 2 ^ 52 := by
      have hi5_eq : i5.val = (borrow1 &&& mask).val := by simp [hi5_1]
      rw [hi5_eq]
      have hband : (borrow1 &&& mask).val = borrow1.val &&& mask.val := by
        simp only [HAnd.hAnd, AndOp.and, UScalar.and, UScalar.val]
        exact BitVec.toNat_and borrow1.bv mask.bv
      rw [hband, hmask]
      exact Nat.and_two_pow_sub_one_eq_mod borrow1.val 52
    have hi5_bound : i5.val < 2 ^ 52 := by
      rw [hi5_mod]
      exact Nat.mod_lt borrow1.val (by decide : 2 ^ 52 > 0)
    have hdiff1 : ∀ j < i6.val, (Aeneas.Std.Array.set difference i i5)[j]!.val < 2 ^ 52 := by
      intro j hj
      simp only [hi6] at hj
      by_cases hjc : j = i.val
      · rw [hjc]
        have := Array.set_of_eq difference i5 i (by scalar_tac)
        simp only [UScalar.ofNat_val, Array.getElem!_Nat_eq, Array.set_val_eq] at this ⊢
        simp only [this]
        exact hi5_bound
      · have hj' : j < i.val := by omega
        have hne := Array.set_of_ne difference i5 j i (by scalar_tac) (by scalar_tac) (by omega)
        simp only [Array.getElem!_Nat_eq, Array.set_val_eq] at hne ⊢
        have hdiff_j := hdiff j hj'
        simp only [Array.getElem!_Nat_eq] at hdiff_j
        simp_all
    have hdiff1_rest : ∀ j, i6.val ≤ j → j < 5 → (Aeneas.Std.Array.set difference i i5)[j]!.val = 0 := by
      intro j hji hj5
      simp only [hi6] at hji
      have hne : j ≠ i.val := by omega
      have := Array.set_of_ne' difference i5 j i (by scalar_tac) (by omega)
      simp only [Array.getElem!_Nat_eq, Array.set_val_eq] at this ⊢
      have hr := hdiff_rest j (by omega) hj5
      simp only [Array.getElem!_Nat_eq] at hr
      simp_all
    -- Main proof: combine expansions with hkey and hinv
    -- This is the complex arithmetic proof that needs careful handling
    have hinv1 : Scalar52_partial_as_Nat a i6.val + borrow1.val / 2 ^ 63 * 2 ^ (52 * i6.val) =
                 Scalar52_partial_as_Nat b i6.val + Scalar52_partial_as_Nat (Aeneas.Std.Array.set difference i i5) i6.val := by
      sorry
    progress as ⟨result, hres1, hres2⟩
    exact ⟨hres1, hres2⟩
  case isFalse hge =>
    have hi5 : i.val = 5 := by scalar_tac
    use (difference, borrow)
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      by_cases hjc : j < i.val
      · exact hdiff j hjc
      · have : i.val ≤ j := by omega
        have hj5 : j < 5 := hj
        have := hdiff_rest j this hj5
        omega
    · -- At i = 5, partial sums equal full sums
      unfold Scalar52_partial_as_Nat Scalar52_as_Nat at *
      simp only [hi5] at hinv
      exact hinv
termination_by 5 - i.val
decreasing_by scalar_decr_tac

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub`**:
- Requires bounded limbs for both inputs
- Requires both inputs to be bounded from above
- The result represents (a - b) mod L
- The result has bounded limbs and is canonical -/
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < Scalar52_as_Nat b + L)
    (hb' : Scalar52_as_Nat b ≤ L) :
    ∃ result, sub a b = ok result ∧
    Scalar52_as_Nat result + Scalar52_as_Nat b ≡ Scalar52_as_Nat a [MOD L] ∧
    Scalar52_as_Nat result < L ∧
    (∀ i < 5, result[i]!.val < 2 ^ 52) := by
  unfold sub
  unfold subtle.FromsubtleChoiceU8.from
  progress*
  · intro j _ _
    interval_cases j
    all_goals simp [ZERO, ZERO_body]; decide
  · sorry
  · split
    · sorry
    · sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
