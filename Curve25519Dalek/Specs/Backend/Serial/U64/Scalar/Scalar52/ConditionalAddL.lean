/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L

/-! # Spec Theorem for `Scalar52::conditional_add_l`

Specification and proof for `Scalar52::conditional_add_l`.

This function conditionally adds the group order L to a scalar based on a boolean-style choice parameter.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

set_option exponentiation.threshold 280
set_option linter.hashCommand false
#setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input unpacked scalar u and a binary condition c.
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

/-- Helper: L limbs are bounded -/
theorem L_limbs_bounded : ∀ i < 5, constants.L[i]!.val < 2 ^ 52 := by
  intro i hi
  unfold constants.L
  interval_cases i <;> decide

-- Decidability instance for Choice equality
instance : DecidableEq subtle.Choice := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro heq; apply h; rw [heq])

/-- Helper: Choice.one has val = 1 -/
theorem Choice.one_val : (Choice.one : subtle.Choice).val = 1#u8 := rfl

/-- Helper: Choice.zero has val = 0 -/
theorem Choice.zero_val : (Choice.zero : subtle.Choice).val = 0#u8 := rfl

/-- Helper: Choice val is 0 or 1 -/
theorem Choice.val_cases (c : subtle.Choice) : c.val = 0#u8 ∨ c.val = 1#u8 := by
  cases c with
  | mk val valid =>
    cases valid with
    | inl h => left; exact h
    | inr h => right; exact h

/-- Progress spec for ConditionallySelectableU64.conditional_select -/
@[progress]
theorem conditional_select_U64_spec (a b : U64) (choice : subtle.Choice) :
    ∃ res, subtle.ConditionallySelectableU64.conditional_select a b choice = ok res ∧
    res = if choice.val = 1#u8 then b else a := by
  unfold subtle.ConditionallySelectableU64.conditional_select
  split <;> simp_all

/-- Helper: 0#u8 ≠ 1#u8 for simp -/
@[simp] theorem U8_zero_ne_one : (0#u8 = 1#u8) = False := by decide

/-- Helper: 1#u8 = 1#u8 for simp -/
@[simp] theorem U8_one_eq_one : (1#u8 = 1#u8) = True := by decide

/-- Helper: 0#u8 = 0#u8 for simp -/
@[simp] theorem U8_zero_eq_zero : (0#u8 = 0#u8) = True := by decide

/-- Helper: If all limbs are < 2^52, then Scalar52_as_Nat < 2^260 -/
theorem Scalar52_as_Nat_bounded (s : Scalar52) (hs : ∀ i < 5, s[i]!.val < 2 ^ 52) :
    Scalar52_as_Nat s < 2 ^ 260 := by
  unfold Scalar52_as_Nat
  have h0 := hs 0 (by decide)
  have h1 := hs 1 (by decide)
  have h2 := hs 2 (by decide)
  have h3 := hs 3 (by decide)
  have h4 := hs 4 (by decide)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  omega

-- Loop spec with complex invariant tracking partial sums
-- The proof requires careful induction on carry propagation
set_option maxHeartbeats 5000000 in -- Needed for complex loop invariant proof
@[progress]
theorem conditional_add_l_loop_spec (self : Scalar52) (condition : subtle.Choice)
    (carry : U64) (mask : U64) (i : Usize)
    (hself : ∀ j < 5, self[j]!.val < 2 ^ 52)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5)
    (hcarry : carry.val < 2 ^ 53) :
    ∃ result, conditional_add_l_loop self condition carry mask i = ok result ∧
    (∀ j < 5, result.2[j]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat result.2 + 2 ^ 260 * (result.1.val / 2 ^ 52) =
      Scalar52_as_Nat self + (if condition.val = 1#u8 then Scalar52_as_Nat constants.L else 0) +
      2 ^ (52 * i.val) * (carry.val / 2 ^ 52) -
      (if condition.val = 1#u8 then ∑ j ∈ Finset.Ico 0 i.val, 2 ^ (52 * j) * constants.L[j]!.val else 0)) := by
  unfold conditional_add_l_loop
  unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  unfold IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
  split
  case isTrue hlt =>
    -- i < 5 case: process one limb and recurse
    -- The full proof requires careful tracking of carry propagation through
    -- the loop. Each iteration:
    -- 1. Gets addend = L[i] if condition=1, else 0
    -- 2. Computes carry1 = (carry >>> 52) + self[i] + addend
    -- 3. Stores carry1 % 2^52 in self[i]
    -- 4. Recurses with carry1 as the new carry
    --
    -- The invariant preservation requires showing:
    -- - How the partial sums change with each modified limb
    -- - The relationship between carry / 2^52 and the overflow
    -- - The conditional addition of L[i] versus the subtracted sum
    --
    -- This sorry allows the main theorem to be used while the detailed
    -- carry propagation proof is being developed.
    progress*
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  case isFalse hge =>
    -- i >= 5 case: return (carry, self)
    have hi5 : i.val = 5 := by scalar_tac
    use (carry, self)
    refine ⟨rfl, ?_, ?_⟩
    · -- limbs bounded
      exact hself
    · -- invariant at i = 5
      simp only [hi5]
      -- At i = 5: carry / 2^52 * 2^260 = carry / 2^52 * 2^260
      -- and the sum over Ico 0 5 equals Scalar52_as_Nat constants.L
      have hsum_L : ∑ j ∈ Finset.Ico 0 5, 2 ^ (52 * j) * constants.L[j]!.val =
                    Scalar52_as_Nat constants.L := by
        unfold Scalar52_as_Nat
        simp only [Finset.range_eq_Ico]
      rw [hsum_L, constants.L_spec]
      -- Now we have: Scalar52_as_Nat self + 2^260 * (carry / 2^52) =
      --              Scalar52_as_Nat self + (if cond then L else 0) + 2^260 * (carry / 2^52) -
      --              (if cond then L else 0)
      cases Choice.val_cases condition with
      | inl hc0 =>
        simp only [hc0, U8_zero_ne_one, ↓reduceIte, add_zero, Nat.sub_zero]
      | inr hc1 =>
        simp only [hc1, ↓reduceIte]
        omega

-- Main theorem using loop spec
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
    ∃ result, conditional_add_l self condition = ok result ∧
    (∀ i < 5, result.2[i]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat result.2 < L) ∧
    (condition = Choice.one → Scalar52_as_Nat result.2 + 2 ^ 260 = Scalar52_as_Nat self + L) ∧
    (condition = Choice.zero → Scalar52_as_Nat result.2 = Scalar52_as_Nat self) := by
  unfold conditional_add_l
  progress*
  -- res_post_2: Scalar52_as_Nat res.2 + 2^260 * (res.1 / 2^52) =
  --             (Scalar52_as_Nat self + if cond then L else 0) + 2^(52*0) * (0/2^52) -
  --             (if cond then sum[0,0) else 0)
  -- Simplifies to: Scalar52_as_Nat res.2 + 2^260 * (res.1 / 2^52) =
  --                Scalar52_as_Nat self + (if cond then Scalar52_as_Nat constants.L else 0)
  simp only [Finset.Ico_self, Finset.sum_empty, Nat.zero_div, mul_zero, add_zero] at res_post_2
  rw [constants.L_spec] at res_post_2
  have hL_bound : L < 2 ^ 260 := by unfold L; grind
  refine ⟨res_post_1, ?_, ?_, ?_⟩
  · -- result < L
    cases Choice.val_cases condition with
    | inl hc0 =>
      have hcz : condition = Choice.zero := by
        cases condition; simp only [Choice.zero, subtle.Choice.mk.injEq]; exact hc0
      simp only [hc0, U8_zero_ne_one, ↓reduceIte, add_zero, Nat.sub_zero] at res_post_2
      have hself_bound := hself''' hcz
      have hcarry_zero : res.1.val / 2 ^ 52 = 0 := by omega
      omega
    | inr hc1 =>
      have hco : condition = Choice.one := by
        cases condition; simp only [Choice.one, subtle.Choice.mk.injEq]; exact hc1
      simp only [hc1, ↓reduceIte, Nat.sub_zero] at res_post_2
      have h1 := hself' hco
      have h2 := hself'' hco
      have hres_bounded : Scalar52_as_Nat res.2 < 2 ^ 260 := Scalar52_as_Nat_bounded res.2 res_post_1
      have hsum_bound : Scalar52_as_Nat self + L < 2 ^ 261 := by omega
      have hcarry_bound : res.1.val / 2 ^ 52 ≤ 1 := by omega
      have hcarry_lower : 1 ≤ res.1.val / 2 ^ 52 := by omega
      have hcarry_eq : res.1.val / 2 ^ 52 = 1 := by omega
      omega
  · -- condition = Choice.one case
    intro hc
    have hc1 : condition.val = 1#u8 := by rw [hc]; rfl
    simp only [hc1, ↓reduceIte, Nat.sub_zero] at res_post_2
    have h1 := hself' hc
    have h2 := hself'' hc
    have hres_bounded : Scalar52_as_Nat res.2 < 2 ^ 260 := Scalar52_as_Nat_bounded res.2 res_post_1
    have hsum_bound : Scalar52_as_Nat self + L < 2 ^ 261 := by omega
    have hcarry_bound : res.1.val / 2 ^ 52 ≤ 1 := by omega
    have hcarry_lower : 1 ≤ res.1.val / 2 ^ 52 := by omega
    have hcarry_eq : res.1.val / 2 ^ 52 = 1 := by omega
    omega
  · -- condition = Choice.zero case
    intro hc
    have hc0 : condition.val = 0#u8 := by rw [hc]; rfl
    simp only [hc0, U8_zero_ne_one, ↓reduceIte, add_zero, Nat.sub_zero] at res_post_2
    have hself_bound := hself''' hc
    have hcarry_zero : res.1.val / 2 ^ 52 = 0 := by omega
    omega

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
