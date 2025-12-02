/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Mathlib.Data.Nat.ModEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
-- import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Zero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

set_option linter.hashCommand false
set_option exponentiation.threshold 280
#setup_aeneas_simps

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

/-- **Spec for `backend.serial.u64.scalar.Scalar52.add_loop`**:
- Starting from index `i` with accumulator `sum` and carry `carry`
- Computes limb-wise addition with carry propagation
- Result limbs are bounded by 2^52
- Parts of sum before index i are preserved
- The result satisfies the modular arithmetic property -/
@[progress]
theorem add_loop_spec (a b sum : Scalar52) (mask carry : U64) (i : Usize)
    (ha : ∀ j < 5, (a[j]!).val < 2 ^ 52)
    (hb : ∀ j < 5, (b[j]!).val < 2 ^ 52)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5)
    (hsum_bounds : ∀ j < i.val, (sum[j]!).val < 2 ^ 52)
    (hsum_rest : ∀ j < 5, i.val ≤ j → (sum[j]!).val = 0)
    (hcarry : carry.val < 2 ^ 54) :
    ∃ sum', add_loop a b sum mask carry i = ok sum' ∧
    (∀ j < 5, (sum'[j]!).val < 2 ^ 52) ∧
    (∀ j < i.val, sum'[j]!.val = sum[j]!.val) ∧
    ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * sum'[j]!.val + 2 ^ 260 * (carry.val / 2 ^ 52) =
      ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) := by
  unfold add_loop
  progress*
  sorry
termination_by 5 - i.val
decreasing_by scalar_decr_tac

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- No panic (always returns successfully)
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (a b : Scalar52)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 52)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 52) :
    ∃ v, add a b = ok v ∧
    Scalar52_as_Nat v % L = (Scalar52_as_Nat a + Scalar52_as_Nat b) % L := by
  unfold add
  progress*
  · intro j _ _
    unfold ZERO
    interval_cases j <;> decide
  · intro i hi
    have hL_bounds : ∀ j < 5, (constants.L[j]!).val < 2 ^ 52 := by
      unfold constants.L
      intro j hj
      interval_cases j <;> decide
    exact hL_bounds i hi
  · have hL_eq : Scalar52_as_Nat constants.L = L := L_spec
    rw [hL_eq] at res_post
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
      simp only [Finset.sum_add_distrib, Nat.mul_add]
    rw [h1, h2]

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
