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
    -- Main proof: the loop invariant is preserved
    -- Key equation: a[i] + new_borrow_bit * 2^52 = b[i] + old_borrow_bit + i5
    -- This follows from wrapping_sub arithmetic with proper borrow handling
    have hinv1 : Scalar52_partial_as_Nat a i6.val + borrow1.val / 2 ^ 63 * 2 ^ (52 * i6.val) =
                 Scalar52_partial_as_Nat b i6.val + Scalar52_partial_as_Nat (Aeneas.Std.Array.set difference i i5) i6.val := by
      -- Use wrapping_sub_val_eq to reason about borrow1
      have hws : borrow1.val = (i1.val + (2^64 - i4.val)) % 2^64 := by
        simp only [hborrow1]
        have := U64.wrapping_sub_val_eq i1 i4
        simp only [UScalar.size] at this
        exact this
      -- Establish key value equalities
      have hi1_val : i1.val = a[i.val]!.val := by
        simp only [hi1, UScalar.val, Array.getElem!_Nat_eq]
      have hi2_val : i2.val = b[i.val]!.val := by
        simp only [hi2, UScalar.val, Array.getElem!_Nat_eq]
      have hi4_val : i4.val = b[i.val]!.val + i3.val := by
        simp only [hi4, hi2_val]
      have hi3_eq : i3.val = borrow.val / 2^63 := by
        simp only [hi3_1, Nat.shiftRight_eq_div_pow]
      -- Expand partial sums at i+1
      have hi6_eq : i6.val = i.val + 1 := by simp [hi6]
      simp only [hi6_eq, Scalar52_partial_as_Nat]
      simp only [Finset.range_add_one, Finset.sum_insert (Finset.notMem_range_self)]
      -- The new difference array: diff'[j] = diff[j] for j < i, diff'[i] = i5
      have hdiff'_lt : ∀ j < i.val,
          (Aeneas.Std.Array.set difference i i5)[j]!.val = difference[j]!.val := by
        intro j hj
        have h := Array.set_of_ne difference i5 j i (by scalar_tac) (by scalar_tac) (by omega)
        grind [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.val, UScalar.ofNat_val]
      have hdiff'_eq : (Aeneas.Std.Array.set difference i i5)[i.val]!.val = i5.val := by
        have h := Array.set_of_eq difference i5 i (by scalar_tac)
        grind [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.val, UScalar.ofNat_val]
      -- Partial sum of diff' at i equals partial sum of diff at i
      have hdiff'_partial : ∑ j ∈ Finset.range i.val, 2^(52*j) * (Aeneas.Std.Array.set difference i i5)[j]!.val
                          = ∑ j ∈ Finset.range i.val, 2^(52*j) * difference[j]!.val := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [hdiff'_lt j hj]
      rw [hdiff'_partial, hdiff'_eq]
      -- From old invariant: partial_a(i) + old_borrow_bit * 2^(52*i) = partial_b(i) + partial_diff(i)
      have hinv' := hinv
      simp only [Scalar52_partial_as_Nat] at hinv'
      -- Case split on whether a[i] >= b[i] + old_borrow
      have hold_borrow : borrow.val / 2^63 = i3.val := by omega
      -- Key bounds for later
      have ha_bound : i1.val < 2^52 := by rw [hi1_val]; exact ha_i
      have hb_i_bound : b[i.val]!.val < 2^52 := hb_i
      have hi3_le : i3.val ≤ 1 := hi3_bound
      have hi4_bound : i4.val < 2^52 + 1 := by rw [hi4_val]; omega
      -- Define P = 2^(52*i) for convenience
      set P := 2^(52*i.val) with hP_def
      by_cases hcase : i1.val ≥ i4.val
      · -- Case 1: No underflow (a[i] >= b[i] + old_borrow_bit)
        have hborrow1_val : borrow1.val = i1.val - i4.val := by
          rw [hws]
          have h1 : i1.val + (2^64 - i4.val) = 2^64 + (i1.val - i4.val) := by omega
          rw [h1]
          have h2 : i1.val - i4.val < 2^64 := by omega
          omega
        have hborrow1_lt : borrow1.val < 2^63 := by rw [hborrow1_val]; omega
        have hnew_borrow : borrow1.val / 2^63 = 0 := by omega
        have hi5_val : i5.val = borrow1.val := by
          rw [hi5_mod, hborrow1_val]
          have h : i1.val - i4.val < 2^52 := by omega
          exact Nat.mod_eq_of_lt h
        -- Prove the equation
        simp only [hnew_borrow, zero_mul, add_zero]
        rw [hi5_val, hborrow1_val]
        -- Limb-level: i1 = i4 + (i1 - i4) = b[i] + i3 + (i1 - i4)
        -- Goal reduces to: sum_a + P * a[i] = sum_b + P * b[i] + sum_diff + P * (i1 - i4)
        -- Using hinv': sum_a + i3 * P = sum_b + sum_diff
        -- So: sum_a = sum_b + sum_diff - i3 * P
        -- LHS = sum_b + sum_diff - i3 * P + P * i1
        -- RHS = sum_b + P * b[i] + sum_diff + P * (i1 - i4)
        --     = sum_b + P * b[i] + sum_diff + P * i1 - P * i4
        --     = sum_b + P * b[i] + sum_diff + P * i1 - P * (b[i] + i3)
        --     = sum_b + sum_diff + P * i1 - P * i3
        -- So LHS = RHS ✓
        have hlimb : a[i.val]!.val = b[i.val]!.val + i3.val + (i1.val - i4.val) := by
          rw [← hi1_val, hi4_val]; omega
        grind
      · -- Case 2: Underflow occurred (a[i] < b[i] + old_borrow_bit)
        have hi1_lt_i4 : i1.val < i4.val := by omega
        have hborrow1_val : borrow1.val = 2^64 + i1.val - i4.val := by rw [hws]; omega
        have hborrow1_ge : borrow1.val ≥ 2^63 := by rw [hborrow1_val]; omega
        have hborrow1_lt_264 : borrow1.val < 2^64 := by rw [hborrow1_val]; omega
        have hnew_borrow : borrow1.val / 2^63 = 1 := by omega
        -- i5 = borrow1 % 2^52 = (2^64 + a[i] - b[i] - old) % 2^52 = 2^52 + a[i] - b[i] - old
        have hi5_val : i5.val = 2^52 + i1.val - i4.val := by
          rw [hi5_mod, hborrow1_val]
          have hdiff : i4.val - i1.val ≤ 2^52 := by omega
          have hdpos : 0 < i4.val - i1.val := by omega
          have heq1 : 2^64 + i1.val - i4.val = 2^64 - (i4.val - i1.val) := by omega
          rw [heq1]
          have heq2 : 2^64 - (i4.val - i1.val) = (2^12 - 1) * 2^52 + (2^52 - (i4.val - i1.val)) := by
            have h : (2:ℕ)^64 = (2:ℕ)^12 * (2:ℕ)^52 := by decide
            omega
          rw [heq2]
          -- Rewrite (k * m + r) as (r + k * m) for Nat.add_mul_mod_self_left
          have heq3 : (2^12 - 1) * 2^52 + (2^52 - (i4.val - i1.val)) =
                      (2^52 - (i4.val - i1.val)) + (2^12 - 1) * 2^52 := by ring
          rw [heq3, Nat.add_mul_mod_self_right]
          have hlt : 2^52 - (i4.val - i1.val) < 2^52 := by omega
          rw [Nat.mod_eq_of_lt hlt]
          omega
        -- Prove the equation
        simp only [hnew_borrow, one_mul]
        rw [hi5_val]
        have hpow_succ : 2^(52*(i.val + 1)) = 2^52 * P := by
          simp only [hP_def]
          have : 52 * (i.val + 1) = 52 + 52 * i.val := by ring
          rw [this, Nat.pow_add]
        rw [hpow_succ]
        -- Limb-level: a[i] + 2^52 = b[i] + i3 + (2^52 + i1 - i4)
        have hlimb : a[i.val]!.val + 2^52 = b[i.val]!.val + i3.val + (2^52 + i1.val - i4.val) := by
          rw [← hi1_val, hi4_val]; omega
        grind
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

set_option maxHeartbeats 5000000 in
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
  -- First, progress through mask computation (two steps: shift then subtract)
  progress  -- 1 <<< 52
  progress  -- mask = i - 1
  -- Progress through the loop with all required hypotheses
  progress as ⟨loop_res, hdiff_limbs, hdiff_inv⟩
  · -- hdiff_rest: ZERO[j] = 0 for all j in 0..5
    intro j _ hj5
    interval_cases j <;> simp [ZERO, ZERO_body] <;> decide
  · -- hinv: Initial invariant at i=0 - partial sums are all 0
    have h0 : (0#usize).bv.toNat = 0 := by decide
    have h1 : (0#u64).bv.toNat = 0 := by decide
    simp only [Scalar52_partial_as_Nat, UScalar.val, h0, h1,
               Finset.range_zero, Finset.sum_empty, zero_add, Nat.zero_div, zero_mul]
  -- Extract diff and borrow from the loop result
  obtain ⟨diff, borrow⟩ := loop_res
  -- diff_inv: A + (borrow/2^63) * 2^260 = B + D
  -- Progress through borrow >>> 63 and cast
  progress as ⟨i1, hi1_eq, _⟩  -- borrow >>> 63
  have hborrow_bit : i1.val ≤ 1 := by
    have hbv : borrow.val < 2 ^ 64 := by scalar_tac
    simp only [hi1_eq, Nat.shiftRight_eq_div_pow]
    omega
  progress as ⟨i2, hi2⟩  -- cast to U8
  have hi2_eq_i1 : i2.val = i1.val := by
    simp only [hi2, UScalar.cast, UScalar.val]
    have hi1_lt : i1.val < 2 ^ 8 := by omega
    exact Nat.mod_eq_of_lt hi1_lt
  have hi2_bound : i2.val ≤ 1 := by omega
  -- Helper: Choice.one.val = 1
  have hChoice_one_val : Choice.one.val.val = 1 := by rfl
  -- Helper: Choice.zero.val = 0
  have hChoice_zero_val : Choice.zero.val.val = 0 := by rfl
  -- Now split on whether i2 = 0 or i2 = 1 (for FromsubtleChoiceU8.from)
  split
  case isTrue hi2_zero =>
    -- i2 = 0, so no borrow, A >= B
    have hi2_val_zero : i2.val = 0 := by simp only [hi2_zero]; rfl
    have hi1_zero : i1.val = 0 := by omega
    have hborrow_div : borrow.val / 2 ^ 63 = 0 := by
      simp only [hi1_eq, Nat.shiftRight_eq_div_pow] at hi1_zero
      exact hi1_zero
    have hdiff_val : Scalar52_as_Nat diff = Scalar52_as_Nat a - Scalar52_as_Nat b := by
      simp only [hborrow_div, zero_mul, add_zero] at hdiff_inv
      omega
    have hA_ge_B : Scalar52_as_Nat a ≥ Scalar52_as_Nat b := by
      simp only [hborrow_div, zero_mul, add_zero] at hdiff_inv
      omega
    have hdiff_lt_L : Scalar52_as_Nat diff < L := by omega
    -- Progress through conditional_add_l with Choice.zero
    progress as ⟨cond_res, hres_limbs, hres_lt_L, _, hres_eq_zero⟩
    · -- hself' (Choice.one case): vacuously true since i2 = 0 ≠ 1
      intro hcond
      simp only [Choice.one, subtle.Choice.mk.injEq, hi2_zero] at hcond
      exact absurd hcond (by decide)
    · -- hself'' (Choice.one case): vacuously true
      intro hcond
      simp only [Choice.one, subtle.Choice.mk.injEq, hi2_zero] at hcond
      exact absurd hcond (by decide)
    · -- hself''' (Choice.zero case): D < L
      intro _
      exact hdiff_lt_L
    have hcz : (subtle.Choice.mk i2 (Or.inl hi2_zero)) = Choice.zero := by
      simp only [Choice.zero, hi2_zero]
    have hres_val := hres_eq_zero hcz
    refine ⟨?_, ?_, ?_⟩
    · -- Modular equivalence: res + B ≡ A [MOD L]
      rw [hres_val, hdiff_val]
      have : Scalar52_as_Nat a - Scalar52_as_Nat b + Scalar52_as_Nat b = Scalar52_as_Nat a := by omega
      rw [this]
    · exact hres_lt_L
    · exact hres_limbs
  case isFalse hi2_nonzero =>
    split
    case isTrue hi2_one =>
      -- i2 = 1, so borrow occurred, A < B
      have hi2_val_one : i2.val = 1 := by simp only [hi2_one]; rfl
      have hi1_one : i1.val = 1 := by omega
      have hborrow_div : borrow.val / 2 ^ 63 = 1 := by
        simp only [hi1_eq, Nat.shiftRight_eq_div_pow] at hi1_one
        have hbv : borrow.val < 2 ^ 64 := by scalar_tac
        omega
      -- From inv: A + 2^260 = B + D, so D = A + 2^260 - B
      have hD_val : Scalar52_as_Nat diff = Scalar52_as_Nat a + 2 ^ 260 - Scalar52_as_Nat b := by
        simp only [hborrow_div, one_mul] at hdiff_inv
        omega
      have hD_bound : Scalar52_as_Nat diff < 2 ^ 260 := Scalar52_as_Nat_bounded diff hdiff_limbs
      have hA_lt_B : Scalar52_as_Nat a < Scalar52_as_Nat b := by
        simp only [hborrow_div, one_mul] at hdiff_inv
        omega
      have hL_bound : L < 2 ^ 260 := by unfold L; decide
      -- Progress through conditional_add_l with Choice.one
      progress as ⟨cond_res, hres_limbs, hres_lt_L, hres_eq_one, _⟩
      · -- hself' (Choice.one case): 2^260 ≤ D + L
        intro _
        rw [hD_val]
        omega
      · -- hself'' (Choice.one case): D < 2^260
        intro _
        exact hD_bound
      · -- hself''' (Choice.zero case): vacuously true since i2 = 1 ≠ 0
        intro hcond
        simp only [Choice.zero, subtle.Choice.mk.injEq, hi2_one] at hcond
        exact absurd hcond (by decide)
      have hco : (subtle.Choice.mk i2 (Or.inr hi2_one)) = Choice.one := by
        simp only [Choice.one, hi2_one]
      have hres_rel := hres_eq_one hco
      -- res + 2^260 = D + L = A + 2^260 - B + L, so res = A + L - B
      have hres_val : Scalar52_as_Nat cond_res.2 = Scalar52_as_Nat a + L - Scalar52_as_Nat b := by
        rw [hD_val] at hres_rel
        omega
      refine ⟨?_, ?_, ?_⟩
      · -- Modular equivalence: res + B = A + L ≡ A [MOD L]
        rw [hres_val]
        have hB_le_AL : Scalar52_as_Nat b ≤ Scalar52_as_Nat a + L := by omega
        have heq : Scalar52_as_Nat a + L - Scalar52_as_Nat b + Scalar52_as_Nat b = Scalar52_as_Nat a + L := by omega
        rw [heq]
        have hL_mod : L ≡ 0 [MOD L] := by rw [Nat.ModEq, Nat.zero_mod, Nat.mod_self]
        have : Scalar52_as_Nat a + L ≡ Scalar52_as_Nat a + 0 [MOD L] := Nat.ModEq.add_left _ hL_mod
        simp only [add_zero] at this
        exact this
      · exact hres_lt_L
      · exact hres_limbs
    case isFalse hi2_neither =>
      -- i2 ≠ 0 and i2 ≠ 1: contradiction since borrow >>> 63 ≤ 1
      exfalso
      have hi2_cases : i2.val = 0 ∨ i2.val = 1 := by omega
      cases hi2_cases with
      | inl h0 =>
        apply hi2_nonzero
        exact UScalar.eq_of_val_eq h0
      | inr h1 =>
        apply hi2_neither
        exact UScalar.eq_of_val_eq h1

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
