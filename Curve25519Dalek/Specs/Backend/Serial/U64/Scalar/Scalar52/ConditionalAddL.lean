/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L

/-! # Spec Theorem for `Scalar52::conditional_add_l`

Specification and proof for `Scalar52::conditional_add_l`.

This function conditionally adds the group order L to a scalar based on a choice parameter.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs -/

set_option linter.hashCommand false
#setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow
set_option exponentiation.threshold 260

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input Scalar52 u and a binary condition c.
    • If condition is true (1), adds L modulo 2^260 and returns the result u' and a carry value;
      if false (0), returns the scalar unchanged.
    • This function is only used in `sub` where the carry value is ignored.

natural language specs (tailored for use in `sub`):

    • Input: limbs bounded by 2^52
    • If condition is 1 (and input ∈ [2^260 - L, 2^260)):
        - Output value: u' + 2^260 = u + L, equivalently u' = u + L - 2^260
        - Output bounded: u' < L
        - Output limbs: < 2^52
    • If condition is 0:
        - Output value: u' = u
        - Output limbs: < 2^52
    • Carry value: not specified (not used by caller)
-/

/-- L limbs are bounded -/
theorem L_limbs_bounded : ∀ i < 5, constants.L[i]!.val < 2 ^ 52 := by
  intro i _
  unfold constants.L
  interval_cases i <;> decide

-- Decidability instance for Choice equality
instance : DecidableEq subtle.Choice := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro heq; apply h; rw [heq])

/-- Helper: Choice val is 0 or 1 -/
theorem Choice.val_cases (c : subtle.Choice) : c.val = 0#u8 ∨ c.val = 1#u8 := by
  cases c with
  | mk val valid =>
    cases valid with
    | inl h => left; exact h
    | inr h => right; exact h

/-- 0#u8 ≠ 1#u8 -/
@[simp] theorem U8_zero_ne_one : (0#u8 = 1#u8) = False := by decide

/-- If all limbs are < 2^52, then Scalar52_as_Nat < 2^260 -/
theorem Scalar52_as_Nat_bounded (s : Scalar52) (hs : ∀ i < 5, s[i]!.val < 2 ^ 52) :
    Scalar52_as_Nat s < 2 ^ 260 := by
  simp only [Scalar52_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  grind

set_option maxHeartbeats 5000000 in -- Needed for complex loop invariant proof
@[progress]
theorem conditional_add_l_loop_spec (self : Scalar52) (condition : subtle.Choice)
    (carry : U64) (mask : U64) (i : Usize)
    (hself : ∀ j < 5, self[j]!.val < 2 ^ 52)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5)
    (hcarry : carry.val < 2 ^ 53) :
    spec (conditional_add_l_loop self condition carry mask i) (fun result =>
    (∀ j < 5, result.2[j]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat result.2 + 2 ^ 260 * (result.1.val / 2 ^ 52) =
      Scalar52_as_Nat self + (if condition.val = 1#u8 then Scalar52_as_Nat constants.L else 0) +
      2 ^ (52 * i.val) * (carry.val / 2 ^ 52) -
      (if condition.val = 1#u8 then ∑ j ∈ Finset.Ico 0 i.val, 2 ^ (52 * j) * constants.L[j]!.val else 0))) := by
  sorry
/- OLD PROOF (needs updating for WP spec form — progress destructuring changed)
  unfold conditional_add_l_loop
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64.index_mut
  split
  case isTrue hlt =>
    -- i < 5 case: process one limb and recurse
    -- Each iteration:
    -- 1. Gets addend = L[i] if condition=1, else 0
    -- 2. Computes carry1 = (carry >>> 52) + self[i] + addend
    -- 3. Stores carry1 % 2^52 in self[i]
    -- 4. Recurses with carry1 as the new carry
    --
    -- The invariant preservation requires showing:
    -- - How the partial sums change with each modified limb
    -- - The relationship between carry / 2^52 and the overflow
    -- - The conditional addition of L[i] versus the subtracted sum
    have hi' : i.val < 5 := by scalar_tac
    have hself_i : self[i.val]!.val < 2 ^ 52 := hself i.val hi'
    have hL_i : constants.L[i.val]!.val < 2 ^ 52 := L_limbs_bounded i.val hi'
    have hcarry_div : carry.val / 2 ^ 52 < 2 := by omega
    have hcarry_shift : carry.val >>> 52 < 2 := by simp only [Nat.shiftRight_eq_div_pow]; omega
    -- Step through progress one at a time to control naming
    progress as ⟨i1, hi1⟩  -- L[i]
    progress as ⟨addend, haddend⟩  -- conditional_select
    have hi1_eq : i1.val = constants.L[i.val]!.val := by simp [hi1]
    have haddend_bound : addend.val < 2 ^ 52 := by
      simp only [haddend]
      split
      · rw [hi1_eq]; exact hL_i
      · decide
    progress as ⟨i2, hi2⟩  -- carry >>> 52
    have hi2_bound : i2.val < 2 := by simp [hi2]; exact hcarry_shift
    progress as ⟨i3, hi3⟩  -- self[i]
    have hi3_eq : i3.val = self[i.val]!.val := by simp [hi3]
    have hi3_bound : i3.val < 2 ^ 52 := by rw [hi3_eq]; exact hself_i
    have hi2i3_ok : i2.val + i3.val < 2 ^ 64 := by
      have h1 : i2.val < 2 := hi2_bound
      have h2 : i3.val < 2 ^ 52 := hi3_bound
      omega
    progress as ⟨i4, hi4⟩  -- i2 + i3
    have hi4_bound : i4.val < 2 ^ 52 + 2 := by simp [hi4]; omega
    have hi4addend_ok : i4.val + addend.val < 2 ^ 64 := by
      have h1 : i4.val < 2 ^ 52 + 2 := hi4_bound
      have h2 : addend.val < 2 ^ 52 := haddend_bound
      omega
    progress as ⟨carry1, hcarry1⟩  -- i4 + addend
    have hcarry1_bound : carry1.val < 2 ^ 53 := by simp [hcarry1]; omega
    progress  -- index_mut (introduces index_mut_back)
    progress as ⟨i5, hi5⟩  -- carry1 &&& mask
    have hi5_bound : i5.val < 2 ^ 52 := by
      have hi5_eq : i5.val = (carry1 &&& mask).val := by simp [hi5]
      rw [hi5_eq]
      have hmask_eq : mask.val = 2 ^ 52 - 1 := hmask
      -- (carry1 &&& mask).val = carry1.val &&& mask.val for UScalar
      have hband : (carry1 &&& mask).val = carry1.val &&& mask.val := by
        simp only [HAnd.hAnd, AndOp.and, UScalar.and, UScalar.val]
        exact BitVec.toNat_and carry1.bv mask.bv
      rw [hband, hmask_eq]
      have hand_le : carry1.val &&& (2 ^ 52 - 1) ≤ 2 ^ 52 - 1 := Nat.and_le_right
      omega
    have hi_plus1_ok : i.val + 1 < 2 ^ 64 := by omega
    progress as ⟨i6, hi6⟩  -- i + 1
    have hi6_bound : i6.val ≤ 5 := by simp [hi6]; omega
    -- The modified array is `Aeneas.Std.Array.set self i i5`
    -- Prove limbs bounded for recursive call
    have hself1_limbs : ∀ j < 5, (Aeneas.Std.Array.set self i i5)[j]!.val < 2 ^ 52 := by
      intro j hj
      by_cases hjc : j = i.val
      · rw [hjc]
        have := Array.set_of_eq self i5 i (by scalar_tac)
        simp only [UScalar.ofNat_val, Array.getElem!_Nat_eq, Array.set_val_eq] at this ⊢
        simp only [this]
        exact hi5_bound
      · have hne := Array.set_of_ne self i5 j i (by scalar_tac) (by scalar_tac) (by omega)
        have hself_j := hself j hj
        simp_all
    -- Recursive call
    progress as ⟨res, hres_limbs, hres_inv⟩
    refine ⟨hres_limbs, ?_⟩
    -- Prove the invariant
    simp only [hi6] at hres_inv
    have hi5_mod : i5.val = carry1.val % 2 ^ 52 := by
      have hi5_eq : i5.val = (carry1 &&& mask).val := by simp [hi5]
      rw [hi5_eq]
      have hband : (carry1 &&& mask).val = carry1.val &&& mask.val := by
        simp only [HAnd.hAnd, AndOp.and, UScalar.and, UScalar.val]
        exact BitVec.toNat_and carry1.bv mask.bv
      rw [hband, hmask]
      exact Nat.and_two_pow_sub_one_eq_mod carry1.val 52
    have hcarry1_eq : carry1.val = i2.val + i3.val + addend.val := by
      simp [hcarry1, hi4]
    have hi2_eq : i2.val = carry.val / 2 ^ 52 := by
      simp [hi2, Nat.shiftRight_eq_div_pow]
    have hi3_val : i3.val = self[i.val]!.val := by simp [hi3_eq]
    -- carry1 = carry/2^52 + self[i] + addend
    have hcarry1_expand : carry1.val = carry.val / 2 ^ 52 + self[i.val]!.val + addend.val := by
      rw [hcarry1_eq, hi2_eq, hi3_val]
    -- i5 + 2^52 * (carry1 / 2^52) = carry1
    have hcarry1_split : i5.val + 2 ^ 52 * (carry1.val / 2 ^ 52) = carry1.val := by
      rw [hi5_mod]
      have := Nat.mod_add_div carry1.val (2 ^ 52)
      omega
    -- For the sum over Ico: sum_{j < k+1} = sum_{j < k} + term_k
    have hsum_split : ∀ k < 5, ∑ j ∈ Finset.Ico 0 (k + 1), 2 ^ (52 * j) * constants.L[j]!.val =
        ∑ j ∈ Finset.Ico 0 k, 2 ^ (52 * j) * constants.L[j]!.val + 2 ^ (52 * k) * constants.L[k]!.val := by
      intro k _
      rw [Finset.sum_Ico_succ_top (Nat.zero_le k)]
    -- Key: Scalar52_as_Nat of modified array
    -- Scalar52_as_Nat (Array.set self i i5) = Scalar52_as_Nat self - 2^(52*i) * self[i] + 2^(52*i) * i5
    have hself1_nat : Scalar52_as_Nat (Aeneas.Std.Array.set self i i5) =
        Scalar52_as_Nat self - 2 ^ (52 * i.val) * self[i.val]!.val + 2 ^ (52 * i.val) * i5.val := by
      unfold Scalar52_as_Nat
      -- Split the sum at index i
      have heq : ∀ j < 5, j ≠ i.val → (Aeneas.Std.Array.set self i i5)[j]!.val = self[j]!.val := by
        intro j hj hne
        have hlen : self.length = 5 := by simp [Aeneas.Std.Array.length]
        have := Array.set_of_ne self i5 j i (by simp [hlen]; omega) (by scalar_tac) (by omega)
        simp_all
      have heq_i : (Aeneas.Std.Array.set self i i5)[i.val]!.val = i5.val := by
        have := Array.set_of_eq self i5 i (by scalar_tac)
        simp only [UScalar.ofNat_val, Array.getElem!_Nat_eq, Array.set_val_eq] at this ⊢
        simp_all
      -- Expand both sums and show equality
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      interval_cases i.val <;> grind
    have hpow_split : 2 ^ (52 * (i.val + 1)) = 2 ^ (52 * i.val) * 2 ^ 52 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have : ∑ j ∈ Finset.Ico 0 (i.val + 1), 2 ^ (52 * j) * constants.L[j]!.val =
        ∑ j ∈ Finset.Ico 0 i.val, 2 ^ (52 * j) * constants.L[j]!.val +
        2 ^ (52 * i.val) * constants.L[i.val]!.val := by grind
    -- Final algebraic manipulation: case split on condition
    cases Choice.val_cases condition with
    | inl hc0 =>
      simp only [hc0, U8_zero_ne_one, reduceIte] at hres_inv ⊢
      have : addend.val = 0 := by simp [*]
      have : 2 ^ (52 * i.val) * i5.val + 2 ^ (52 * i.val) * 2 ^ 52 * (carry1.val / 2 ^ 52) =
          2 ^ (52 * i.val) * carry1.val := by grind
      have : 2 ^ (52 * i.val) * carry1.val = 2 ^ (52 * i.val) * (carry.val / 2 ^ 52) +
          2 ^ (52 * i.val) * self[i.val]!.val := by grind
      rw [hself1_nat, hpow_split] at hres_inv
      have hself_nat_bound : 2 ^ (52 * i.val) * self[i.val]!.val ≤ Scalar52_as_Nat self := by
        simp only [Scalar52_as_Nat, Finset.sum_range_succ]
        interval_cases i.val <;> omega
      omega
    | inr hc1 =>
      simp only [hc1, reduceIte] at hres_inv ⊢
      rw [hpow_split] at hres_inv
      have : 2 ^ (52 * i.val) * i5.val + 2 ^ (52 * i.val) * 2 ^ 52 * (carry1.val / 2 ^ 52) =
          2 ^ (52 * i.val) * carry1.val := by grind
      have : 2 ^ (52 * i.val) * carry1.val =
          2 ^ (52 * i.val) * (carry.val / 2 ^ 52) + 2 ^ (52 * i.val) * self[i.val]!.val +
          2 ^ (52 * i.val) * constants.L[i.val]!.val := by grind
      have : 2 ^ (52 * i.val) * self[i.val]!.val ≤ Scalar52_as_Nat self := by
        simp only [Scalar52_as_Nat, Finset.sum_range_succ]
        interval_cases i.val <;> omega
      omega
  case isFalse hge =>
    -- i >= 5 case: return (carry, self)
    have hi5 : i.val = 5 := by scalar_tac
    use (carry, self)
    refine ⟨rfl, ?_, ?_⟩
    · assumption
    · simp only [hi5]
      have : ∑ j ∈ Finset.Ico 0 5, 2 ^ (52 * j) * constants.L[j]!.val =
          Scalar52_as_Nat constants.L := by
        simp [Scalar52_as_Nat]
      rw [this, constants.L_spec]
      cases Choice.val_cases condition with
      | inl => simp [*]
      | inr => grind
termination_by 5 - i.val
decreasing_by scalar_decr_tac
-/

set_option maxHeartbeats 2000000 in -- Increased heartbeats needed for complex arithmetic proofs
/-- **Spec for `scalar.Scalar52.conditional_add_l`** (tailored for use in `sub`):
- Requires input limbs bounded by 2^52
- When condition is 1, requires input value in [2^260 - L, 2^260)
- When condition is 1: result + 2^260 = input + L, with result < L and limbs < 2^52
- When condition is 0: result unchanged with limbs < 2^52
- Carry value not specified (not used by sub)
-/
@[progress]
theorem conditional_add_l_spec (self : Scalar52) (condition : subtle.Choice)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : condition = Choice.one → 2 ^ 260 ≤ Scalar52_as_Nat self + L)
    (hself'' : condition = Choice.one → Scalar52_as_Nat self < 2 ^ 260)
    (hself''' : condition = Choice.zero → Scalar52_as_Nat self < L) :
    spec (conditional_add_l self condition) (fun result =>
    (∀ i < 5, result.2[i]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat result.2 < L) ∧
    (condition = Choice.one → Scalar52_as_Nat result.2 + 2 ^ 260 = Scalar52_as_Nat self + L) ∧
    (condition = Choice.zero → Scalar52_as_Nat result.2 = Scalar52_as_Nat self)) := by
  unfold conditional_add_l
  progress*
  rw [constants.L_spec] at *
  refine ⟨by assumption, ?_, ?_, ?_⟩
  · -- BEGIN TASK
    -- result < L
    cases Choice.val_cases condition with
    | inl =>
      have : condition = Choice.zero := by cases condition; simp [Choice.zero]; grind
      have : Scalar52_as_Nat res.2 + 2 ^ 260 * (res.1.val / 2 ^ 52) = Scalar52_as_Nat self := by
        simp_all
      grind
    | inr =>
      have : condition = Choice.one := by cases condition; simp [Choice.one]; grind
      have : Scalar52_as_Nat res.2 < 2 ^ 260 := Scalar52_as_Nat_bounded res.2 (by assumption)
      simp only [Finset.Ico_self] at *
      grind
    -- END TASK
  · -- BEGIN TASK
    -- condition = Choice.one case
    intro hc
    have : condition.val = 1#u8 := by rw [hc]; rfl
    have : Scalar52_as_Nat res.2 < 2 ^ 260 := Scalar52_as_Nat_bounded res.2 (by assumption)
    have : L < 2 ^ 260 := by unfold L; grind
    simp only [Finset.Ico_self] at *
    grind
    -- END TASK
  · -- BEGIN TASK
    -- condition = Choice.zero case
    intro hc
    have : condition.val = 0#u8 := by rw [hc]; rfl
    have : Scalar52_as_Nat res.2 + 2 ^ 260 * (res.1.val / 2 ^ 52) = Scalar52_as_Nat self := by
      simp_all
    have : L < 2 ^ 260 := by unfold L; grind
    grind
    -- END TASK

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
