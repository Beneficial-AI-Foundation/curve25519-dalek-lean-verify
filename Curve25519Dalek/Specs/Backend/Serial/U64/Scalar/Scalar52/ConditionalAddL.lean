/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
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

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
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
    conditional_add_l_loop self condition carry mask i ⦃ result =>
      (∀ j < 5, result.2[j]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2 + 2 ^ 260 * (result.1.val / 2 ^ 52) =
        Scalar52_as_Nat self + (if condition.val = 1#u8 then Scalar52_as_Nat constants.L else 0) +
        2 ^ (52 * i.val) * (carry.val / 2 ^ 52) -
        (if condition.val = 1#u8 then ∑ j ∈ Finset.Ico 0 i.val, 2 ^ (52 * j) * constants.L[j]!.val else 0)) ⦄ := by
  sorry

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
    conditional_add_l self condition ⦃ result =>
      (∀ i < 5, result.2[i]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2 < L) ∧
      (condition = Choice.one → Scalar52_as_Nat result.2 + 2 ^ 260 = Scalar52_as_Nat self + L) ∧
      (condition = Choice.zero → Scalar52_as_Nat result.2 = Scalar52_as_Nat self) ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
