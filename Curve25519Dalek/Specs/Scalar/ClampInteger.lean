/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Spec theorem for `curve25519_dalek::scalar::clamp_integer`

Applies bitwise clamping to a 32-byte little-endian scalar representation:
• clears the three lowest bits of byte[0] (ensuring divisibility by the cofactor h = 8),
• clears the highest bit of byte[31] (ensuring the value < 2^255),
• sets bit 6 of byte[31] (ensuring the value ≥ 2^254).

The result is a properly clamped scalar in the range [2^254, 2^255) divisible by h = 8,
suitable for use in X25519 scalar multiplication.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek scalar

attribute [-simp] Int.reducePow Nat.reducePow

namespace curve25519_dalek.scalar

/-- **Spec theorem for `curve25519_dalek::scalar::clamp_integer`**
• The function always succeeds (no panic) for any 32-byte input
• h divides U8x32_as_Nat result (the result is divisible by the cofactor h = 8)
• U8x32_as_Nat result < 2^255
• 2^254 ≤ U8x32_as_Nat result
-/
@[step]
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (result : Array U8 32#usize) =>
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

/-- **Spec theorem for `curve25519_dalek::scalar::clamp_integer`** (via `U8x32_as_Nat_foldr`)
• The function always succeeds (no panic) for any 32-byte input
• h divides U8x32_as_Nat_foldr result
• U8x32_as_Nat_foldr result < 2^255
• 2^254 ≤ U8x32_as_Nat_foldr result
-/
theorem clamp_integer_spec' (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (result : Array U8 32#usize) =>
      h ∣ U8x32_as_Nat_foldr result ∧
      U8x32_as_Nat_foldr result < 2^255 ∧
      2^254 ≤ U8x32_as_Nat_foldr result ⦄ := by
  simp only [← U8x32_as_Nat_eq_foldr']
  apply clamp_integer_spec

end curve25519_dalek.scalar
