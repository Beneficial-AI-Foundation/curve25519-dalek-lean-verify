/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Mathlib.Data.Nat.ModEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs
-/

set_option exponentiation.threshold 280
set_option linter.hashCommand false
#setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

/-- If `Scalar52_as_Nat a < 2^259`, then the top limb `a[4]` is bounded by `2^51`.
This follows because `2^208 * a[4] ≤ Scalar52_as_Nat a < 2^259` implies `a[4] < 2^51`. -/
theorem Scalar52_top_limb_lt_of_as_Nat_lt (a : Scalar52)
    (h : Scalar52_as_Nat a < 2 ^ 259) : a[4]!.val < 2 ^ 51 := by
  unfold Scalar52_as_Nat at h
  have h4 : 2 ^ 208 * a[4]!.val ≤ ∑ j ∈ Finset.range 5, 2 ^ (52 * j) * a[j]!.val := by
    have hmem : 4 ∈ Finset.range 5 := by simp
    have := Finset.single_le_sum (f := fun j => 2 ^ (52 * j) * a[j]!.val)
      (fun j _ => Nat.zero_le _) hmem
    convert this using 2
  omega

set_option maxHeartbeats 1000000 in
-- probably the simp_all
/-- **Spec for `backend.serial.u64.scalar.Scalar52.add_loop`**:
- Starting from index `i` with accumulator `sum` and carry `carry`
- Computes limb-wise addition with carry propagation
- Result limbs are bounded by 2^52
- Parts of sum before index i are preserved
- The result satisfies the modular arithmetic property -/
@[progress]
theorem add_loop_spec (a b sum : Scalar52) (mask carry : U64) (i : Usize)
    (ha : ∀ j < 5, a[j]!.val < 2 ^ 52) (hb : ∀ j < 5, b[j]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < 2 ^ 259) (hb' : Scalar52_as_Nat b < 2 ^ 259)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5)
    (hcarry : i.val = 5 → carry.val < 2 ^ 52)
    (hcarry : ∀ i < 5, carry.val < 2 ^ 53)
    (hsum : ∀ j < 5, sum[j]!.val < 2 ^ 52)
    (hsum' : ∀ j < 5, i.val ≤ j → sum[j]!.val = 0) :
    ∃ sum', add_loop a b sum mask carry i = ok sum' ∧
    (∀ j < 5, sum'[j]!.val < 2 ^ 52) ∧
    (∀ j < i.val, sum'[j]!.val = sum[j]!.val) ∧
    ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * sum'[j]!.val =
      ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) +
      2 ^ (52 * i.val) * (carry.val / 2 ^ 52) := by
  unfold add_loop
  unfold Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  unfold IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
  progress*
  · have := ha i (by scalar_tac)
    have := hb i (by scalar_tac)
    scalar_tac
  · have := ha i (by scalar_tac)
    have := hb i (by scalar_tac)
    scalar_tac
  · intro hi
    have : i.val = 4 := by grind
    have : a[4]!.val < 2 ^ 51 := by grind [Scalar52_top_limb_lt_of_as_Nat_lt]
    have : b[4]!.val < 2 ^ 51 := by grind [Scalar52_top_limb_lt_of_as_Nat_lt]
    simp [*]
    have : carry.val >>> 52 ≤ 1 := by have := hcarry i (by scalar_tac); omega
    simp at *; grind
  · intro j hj
    have : carry.val >>> 52 ≤ 1 := by have := hcarry i (by scalar_tac); omega
    have := ha i (by scalar_tac)
    have := hb i (by scalar_tac)
    simp at *; grind
  · intro j hj
    by_cases hc : j = i
    · rw [hc]
      have := Array.set_of_eq sum i5 i (by scalar_tac)
      simp only [UScalar.ofNat_val, Array.getElem!_Nat_eq, Array.set_val_eq, gt_iff_lt] at this ⊢
      simp [this, i5_post_1, hmask]
      grind
    · have := Array.set_of_ne sum i5 j i (by scalar_tac) (by scalar_tac) (by grind)
      have := hsum j (by scalar_tac)
      simp_all
  · intro j hj _
    have hne : j ≠ i := by grind
    have := Array.set_of_ne' sum i5 j i (by scalar_tac) (by omega)
    have := hsum' j hj (by omega)
    simp_all
  · refine ⟨?_, ?_, ?_⟩
    · grind
    · intro j hj
      have := res_post_2 j (by omega)
      have := Array.set_of_ne sum i5 j i (by scalar_tac) (by scalar_tac) (by omega)
      simp_all
    · have : carry1.val = a[i]!.val + b[i]!.val + carry.val / 2 ^ 52 := by
        simp [*]; omega
      have : res[i]! = carry1.val % 2 ^ 52 := by
        have := res_post_2 i.val (by omega)
        have := Array.set_of_eq sum i5 i (by scalar_tac)
        simp_all
      have : ∑ j ∈ Finset.Ico (i.val + 1) 5, 2 ^ (52 * j) * res[j]!.val =
          ∑ j ∈ Finset.Ico (i.val + 1) 5, 2 ^ (52 * j) * ((a)[j]!.val + (b)[j]!.val) +
          2 ^ (52 * (i.val + 1)) * (↑carry1 / 2 ^ 52) := by
        have : 4503599627370496 = 2 ^ 52 := by grind
        simp_all
      have : 2 ^ (52 * i.val) * (carry1.val % 2 ^ 52) +
          2 ^ (52 * (i.val + 1)) * (carry1.val / 2 ^ 52) = 2 ^ (52 * i.val) * carry1.val := by
        have : carry1.val % 2 ^ 52 + 2 ^ 52 * (carry1.val / 2 ^ 52) = carry1.val := by grind
        grind
      calc ∑ j ∈ Finset.Ico (↑i) 5, 2 ^ (52 * j) * res[j]!
        _ = 2 ^ (52 * ↑i) * res[i]! +
            ∑ j ∈ Finset.Ico (↑i + 1) 5, 2 ^ (52 * j) * res[j]! := by
          have hi : i.val < 5 := by scalar_tac
          simp [Finset.sum_eq_sum_Ico_succ_bot hi]
        _ = ∑ j ∈ Finset.Ico (↑i) 5, 2 ^ (52 * j) * (↑a[j]! + ↑b[j]!) +
            2 ^ (52 * ↑i) * (↑carry / 2 ^ 52) := by
          have hi : i.val < 5 := by scalar_tac
          rw [Finset.sum_eq_sum_Ico_succ_bot hi]
          grind
  · refine ⟨?_, fun j hj ↦ ?_, ?_⟩
    · grind
    · simp
    · have : i.val = 5 := by scalar_tac
      simp [this]; grind
termination_by 5 - i.val
decreasing_by scalar_decr_tac

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- No panic (always returns successfully)
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (a b : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < 2 ^ 259) (hb' : Scalar52_as_Nat b < 2 ^ 259) :
    ∃ v, add a b = ok v ∧
    Scalar52_as_Nat v % L = (Scalar52_as_Nat a + Scalar52_as_Nat b) % L := by
  unfold add
  progress*
  · intro j _
    unfold ZERO
    interval_cases j <;> decide
  · unfold ZERO; decide
  · intro i hi
    unfold constants.L
    interval_cases i <;> decide
  · rw [L_spec] at res_post
    have h1 : Scalar52_as_Nat res ≡ Scalar52_as_Nat sum [MOD L] := by
      have hL_mod : L ≡ 0 [MOD L] := by
        rw [Nat.ModEq, Nat.zero_mod, Nat.mod_self]
      have : Scalar52_as_Nat res + L ≡ Scalar52_as_Nat res + 0 [MOD L] :=
        Nat.ModEq.add_left _ hL_mod
      simp only [add_zero] at this
      exact this.symm.trans res_post
    have h2 : Scalar52_as_Nat sum = Scalar52_as_Nat a + Scalar52_as_Nat b := by
      unfold Scalar52_as_Nat
      simp only [Finset.range_eq_Ico] at sum_post_3 ⊢
      simp only [add_zero] at sum_post_3
      conv_lhs => rw [sum_post_3]
      simp [Finset.sum_add_distrib, Nat.mul_add]
    rw [h1, h2]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
