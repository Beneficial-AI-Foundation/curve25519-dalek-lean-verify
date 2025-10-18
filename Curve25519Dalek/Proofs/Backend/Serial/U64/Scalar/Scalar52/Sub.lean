/-
Copyright (c) 2024 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Aux
import Curve25519Dalek.Proofs.Defs

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000

/-! # Sub

Specification and proof for `Scalar52::sub`.

This function computes the difference of two Scalar52 values modulo L (the group order).
The function performs subtraction with borrow handling and conditional addition of L
to ensure the result is non-negative.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs:L175-L198
-/

open Aeneas.Std Result
open curve25519_dalek
open backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
-- This activates/deactives some simps to reason about lists
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `sub` -/

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub_loop`**:
- Helper function that performs the core subtraction with borrow propagation
- Iterates through limbs performing subtraction with borrow
- Conditionally adds L if the result would be negative
- Requires that input limbs and intermediate values are within bounds -/
theorem sub_loop_spec (a b difference : Array U64 5#usize) (mask borrow : U64) (i : Usize)
    (ha : ∀ j, j < 5 → (a[j]!).val < 2 ^ 52)
    (hb : ∀ j, j < 5 → (b[j]!).val < 2 ^ 52)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5) :
    ∃ result, sub_loop a b difference mask borrow i = ok result ∧
    (i.val = 5 →
      U64x5_as_Nat result ≡ (U64x5_as_Nat a - U64x5_as_Nat b) [MOD L]) := by
  sorry

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub`**:
- Does not error and hence returns a result
- The result represents (a - b) mod L where L is the group order
- Requires that input limbs are within bounds (52-bit values) -/
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 52)
    (hb : ∀ i, i < 5 → (b[i]!).val < 2 ^ 52) :
    ∃ result, sub a b = ok result ∧
    U64x5_as_Nat result ≡ (U64x5_as_Nat a - U64x5_as_Nat b) [MOD L] := by
  sorry
