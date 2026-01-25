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

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes two input unpacked scalars u and u' and returns an unpacked scalar v representing
      the sum (u + u') mod L where L is the group order.

natural language specs:

    • scalar_to_nat(v) = (scalar_to_nat(u) + scalar_to_nat(u')) mod L
-/

set_option maxHeartbeats 1000000 in
-- simp_all is heavy
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
    add_loop a b sum mask carry i ⦃ sum' =>
      (∀ j < 5, sum'[j]!.val < 2 ^ 52) ∧
      (∀ j < i.val, sum'[j]!.val = sum[j]!.val) ∧
      ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * sum'[j]!.val =
        ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) +
        2 ^ (52 * i.val) * (carry.val / 2 ^ 52) ⦄ := by
  sorry

termination_by 5 - i.val
decreasing_by scalar_decr_tac

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- Requires the input values to be bounded by  2 ^ 259
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < L) (hb' : Scalar52_as_Nat b ≤ L) :
    add a b ⦃ result =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat a + Scalar52_as_Nat b [MOD L] ∧
      Scalar52_as_Nat result < L ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
