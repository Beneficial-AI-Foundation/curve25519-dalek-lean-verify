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
      Field51_as_Nat(sub(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p)
      where p = 2^255 - 19
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.sub`**:
- No panic (always returns successfully when bounds are satisfied)
- The result c satisfies the field subtraction property:
  Field51_as_Nat(c) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p)
  where p = 2^255 - 19
- Requires that input limbs are bounded:
  - For a: limbs must allow addition with 16*p without U64 overflow
    - a[0] must be ≤ 18410715276690587951 (= 2^64 - 1 - 36028797018963664)
    - a[1..4] must be ≤ 18410715276690587663 (= 2^64 - 1 - 36028797018963952)
  - For b: limbs must be ≤ the constants (representing 16*p) to avoid underflow
    - b[0] must be ≤ 36028797018963664
    - b[1..4] must be ≤ 36028797018963952
-/
@[progress]
theorem sub_spec (a b : Array U64 5#usize)
    (h_bound_a0 : (a[0]!).val ≤ 18410715276690587951)
    (h_bound_a1 : (a[1]!).val ≤ 18410715276690587663)
    (h_bound_a2 : (a[2]!).val ≤ 18410715276690587663)
    (h_bound_a3 : (a[3]!).val ≤ 18410715276690587663)
    (h_bound_a4 : (a[4]!).val ≤ 18410715276690587663)
    (h_bound_b0 : (b[0]!).val ≤ 36028797018963664)
    (h_bound_b1 : (b[1]!).val ≤ 36028797018963952)
    (h_bound_b2 : (b[2]!).val ≤ 36028797018963952)
    (h_bound_b3 : (b[3]!).val ≤ 36028797018963952)
    (h_bound_b4 : (b[4]!).val ≤ 36028797018963952) :
    ∃ c,
    sub a b = ok c ∧
    Field51_as_Nat c % p = (Field51_as_Nat a + (16*p - Field51_as_Nat b)) % p
    := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
