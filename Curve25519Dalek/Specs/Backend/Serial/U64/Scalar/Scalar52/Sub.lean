/-
Copyright (c) 2024 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.ConditionalAddL

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 260

/-! # Sub

Specification and proof for `Scalar52::sub`.

This function computes the difference of two Scalar52 values modulo L (the group order).
The function performs subtraction with borrow handling and conditional addition of L
to ensure the result is non-negative.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs:L175-L198

## Algorithm Summary

The subtraction uses base-2^52 arithmetic with borrow propagation:

1. **Loop iteration**: For each limb i:
   - `borrow = a[i].wrapping_sub(b[i] + (borrow >> 63))`
   - `difference[i] = borrow & mask` (keep lower 52 bits)

2. **Borrow detection**: `borrow >> 63` extracts a 0/1 flag:
   - 0 if no underflow occurred
   - 1 if underflow occurred (wrapped value has top bits set)

3. **Telescoping property**: The borrows cancel perfectly:
   - `difference[i] = (a[i] - b[i] - c_i) mod 2^52 = a[i] - b[i] - c_i + c_{i+1} * 2^52`
   - Summing: `Σ difference[i] * 2^(52*i) = A - B + c_5 * 2^260`

4. **Final correction**: If `c_5 = 1` (final borrow set), then `A < B`, so add L
   to get a positive result in `[0, L)`.

**Key insight**: The final borrow `c_5` is just a sign indicator, not a quantity to subtract.
When `A < B`, the difference array stores `2^260 + (A - B)` (the representation in Z/(2^260)Z).
Adding L causes wrap-around: `(2^260 + (A - B) + L) mod 2^260 = A - B + L ∈ (0, L)`.
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
-- This activates/deactives some simps to reason about lists
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `sub` -/

/-- Partial sum of limbs up to index n: Σ (j < n) limbs[j] * 2^(52*j) -/
def Scalar52_partial_as_Nat (limbs : Array U64 5#usize) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, 2 ^ (52 * j) * (limbs[j]!).val

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub_loop`**:

The loop computes the subtraction a - b with borrow propagation.
After processing indices 0..i, the loop invariant holds:
  partial_a(i) + (borrow / 2^63) * 2^(52*i) = partial_b(i) + partial_diff(i)

When the loop completes (i = 5), this gives:
  A + (borrow / 2^63) * 2^260 = B + D

Where (borrow / 2^63) = 1 means A < B (underflow occurred), and the difference D
represents (A - B) mod 2^260.
-/
@[progress]
theorem sub_loop_spec (a b difference : Scalar52) (mask borrow : U64) (i : Usize)
    (ha : ∀ j < 5, a[j]!.val < 2 ^ 52)
    (hb : ∀ j < 5, b[j]!.val < 2 ^ 52)
    (hdiff : ∀ j < i.val, difference[j]!.val < 2 ^ 52)
    (hdiff_rest : ∀ j, i.val ≤ j → j < 5 → difference[j]!.val = 0)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5)
    (hinv : Scalar52_partial_as_Nat a i.val + borrow.val / 2 ^ 63 * 2 ^ (52 * i.val) =
            Scalar52_partial_as_Nat b i.val + Scalar52_partial_as_Nat difference i.val) :
    ∃ result, sub_loop a b difference mask borrow i = ok result ∧
    (∀ j < 5, result.1[j]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat a + result.2.val / 2 ^ 63 * 2 ^ 260 =
     Scalar52_as_Nat b + Scalar52_as_Nat result.1) := by
  sorry

/-- **Spec for `backend.serial.u64.scalar.Scalar52.sub`**:
- Requires bounded limbs for both inputs
- Requires both inputs to be bounded from above
- The result represents (a - b) mod L
- The result has bounded limbs and is canonical -/
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < Scalar52_as_Nat b + L)
    (hb' : Scalar52_as_Nat b ≤ L) :
    ∃ result, sub a b = ok result ∧
    Scalar52_as_Nat result + Scalar52_as_Nat b ≡ Scalar52_as_Nat a [MOD L] ∧
    Scalar52_as_Nat result < L ∧
    (∀ i < 5, result[i]!.val < 2 ^ 52) := by
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
