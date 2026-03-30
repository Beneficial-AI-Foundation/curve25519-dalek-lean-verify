/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.style.setOption false
set_option grind.warning false

/-! # clamp_integer -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
open scalar

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `clamp_integer` -/

namespace curve25519_dalek.scalar

/-- **Spec and proof concerning `scalar.clamp_integer`**:
- No panic
- (as_nat_32_u8 result) is divisible by h (cofactor of curve25519)
- as_nat_32_u8 result < 2^255
- 2^254 ≤ as_nat_32_u8 result -/
@[step]
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (result : Std.Array U8 32#usize) =>
      h ∣ U8x32_as_Nat result ∧
      U8x32_as_Nat result < 2^255 ∧
      2^254 ≤ U8x32_as_Nat result ⦄ := by
  unfold clamp_integer h
  step*
  unfold U8x32_as_Nat
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.dvd_sum
    intro i hi
    by_cases hc : i = 0
    · subst_vars
      have (byte : U8) : 8 ∣ (byte &&& 248#u8).val := by bvify 8; bv_decide
      simpa [*] using this _
    · have := List.mem_range.mp hi
      interval_cases i <;> omega
  · subst_vars
    simp only [Array.getElem!_Nat_eq, Array.set_val_eq, UScalar.ofNatCore_val_eq, List.set_set,
      List.getElem!_eq_getElem?_getD]
    rw [Finset.sum_range_succ]
    simp only [Nat.reduceMul, List.length_set, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      Nat.lt_add_one, getElem?_pos, List.getElem_set_self, Option.getD_some, Array.set_val_eq,
      getElem!_pos, UScalar.val_or, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true,
      List.getElem_set_ne, UScalar.val_and, i5_post1, i3_post1]
    have : (bytes : List U8)[31].val &&& 127 ||| 64 ≤ 127 := by
      have h : ((bytes : List U8)[31].bv &&& 127 ||| 64) ≤ 127 := by bv_decide
      bound
    calc
      _ ≤ ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * (2^8 - 1) +
          2 ^ 248 * ((bytes : List U8)[31] &&& 127 ||| 64) := by gcongr; bv_tac
      _ ≤ ∑ x ∈ Finset.range 31, 2 ^ (8 * x) * (2^8 - 1) + 2 ^ 248 * 127 := by gcongr
      _ < 2 ^ 255 := by decide
  · have : 64 ≤ ((bytes : List U8)[31] &&& 127 ||| 64) := Nat.right_le_or
    simp [Finset.sum_range_succ]
    grind

end curve25519_dalek.scalar
