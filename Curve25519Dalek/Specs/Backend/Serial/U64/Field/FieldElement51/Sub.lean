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
      subtraction is performed to avoid underflow.

natural language specs:

    • For all FieldElement51s a and b:
      Field51_as_Nat(sub(a, b)) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p)
      where p = 2^255 - 19
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.sub`**:
- No panic (always succeeds due to bias addition preventing underflow)
- The result c satisfies the field subtraction property:
  Field51_as_Nat(c) ≡ Field51_as_Nat(a) - Field51_as_Nat(b) (mod p)
  where p = 2^255 - 19
-/
@[progress]
theorem sub_spec (a b : Array U64 5#usize) :
    ∃ c,
    sub a b = ok c ∧
    Field51_as_Nat c % p = (Field51_as_Nat a - Field51_as_Nat b) % p
    := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
