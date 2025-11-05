/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::sub`

Specification and proof for `FieldElement51::sub`.

This function performs field element subtraction. To avoid underflow, a multiple
of p is added.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    • Takes two input FieldElement51s a and b and returns another FieldElement51
      that is a representant of the difference a - b in the field (modulo p = 2^255 - 19).

    • The implementation adds a multiple of p (namely 16p) as a bias value to a before
      subtraction is performed to avoid underflow: computes (a + 16*p) - b, then reduces

natural language specs:

    • For appropriately bounded FieldElement51s a and b:
      Field51_as_Nat(sub(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
      Field51_as_Nat(sub(a, b)) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.sub`**:
- No panic (always returns successfully when bounds are satisfied)
- The result c satisfies the field subtraction property:

  Field51_as_Nat(c) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p), or equivalently
  Field51_as_Nat(c) + Field51_as_Nat(b) ≡ Field51_as_Nat(a) (mod p)

- Requires that input limbs are bounded:
  - For a: limbs must allow addition with 16*p without U64 overflow
    - a[0] must be ≤ 18410715276690587951 (= 2^64 - 1 - 36028797018963664)
    - a[1..4] must be ≤ 18410715276690587663 (= 2^64 - 1 - 36028797018963952)
  - For b: limbs must be ≤ the constants (representing 16*p) to avoid underflow
    - b[0] must be ≤ 36028797018963664
    - b[1..4] must be ≤ 36028797018963952
  To make the theorem more easily readable and provable, we
  replace these precise bounds with the slightly looser bounds
  a[i] ≤ 2^63  and b[i] ≤ 2^54
-/
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (h_bounds_a : ∀ i, i < 5 → (a[i]!).val ≤ 2 ^ 63)
    (h_bounds_b : ∀ i, i < 5 → (b[i]!).val ≤ 2 ^ 54) :
    ∃ c,
    sub a b = ok c ∧
    (Field51_as_Nat c + Field51_as_Nat b) % p = Field51_as_Nat a % p
    := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
