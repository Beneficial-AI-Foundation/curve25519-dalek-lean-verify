/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Mathlib

set_option linter.style.setOption false
set_option grind.warning false

/-! # clamp_integer -/

open Aeneas.Std Result
open curve25519_dalek
open scalar

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxiliary theorems -/

/- This allows `bvify` to automatically do the conversion `a ∣ b ↔ b % a = 0`,
   which can then be lifted to something which uses bit-vectors -/
attribute [bvify_simps] Nat.dvd_iff_mod_eq_zero

theorem clamp_integer_spec_aux_a (byte : U8) : 8 ∣ (byte &&& 248#u8).val := by
  bvify 8; bv_decide

theorem clamp_integer_spec_aux_b (byte : U8) : byte.val &&& 127 ||| 64 ≤ 127 := by
  have h : (byte.bv &&& 127 ||| 64) ≤ 127 := by bv_decide
  bound

/-! ## Spec for `clamp_integer` -/

/-- **Spec and proof concerning `scalar.clamp_integer`**:
- No panic
- (as_nat_32_u8 result) is divisible by h (cofactor of curve25519)
- as_nat_32_u8 result < 2^255
- 2^254 ≤ as_nat_32_u8 result
-/
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    ∃ result, clamp_integer bytes = ok (result) ∧
    h ∣ U8x32_as_Nat result ∧
    U8x32_as_Nat result < 2^255 ∧
    2^254 ≤ U8x32_as_Nat result := by
  unfold clamp_integer h
  progress*
  unfold U8x32_as_Nat
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.dvd_sum
    intro i hi
    by_cases hc : i = 0
    · subst_vars
      simpa [*] using clamp_integer_spec_aux_a _
    · have := List.mem_range.mp hi
      interval_cases i <;> omega
  · subst_vars
    simp [*]
    rw [Finset.sum_range_succ]
    simp [*]
    have := clamp_integer_spec_aux_b (bytes : List U8)[31]
    calc
      _ ≤ ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * (2^8 - 1) +
          2 ^ 248 * ((bytes : List U8)[31] &&& 127 ||| 64) := by
        gcongr
        bv_tac
      _ ≤ ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * (2^8 - 1) + 2 ^ 248 * 127 := by
        gcongr
      _ < 2 ^ 255 := by
        bound
  · subst_vars
    simp [Finset.sum_range_succ, *]
    have : 64 ≤ ((bytes : List U8)[31] &&& 127 ||| 64) := Nat.right_le_or
    scalar_tac
