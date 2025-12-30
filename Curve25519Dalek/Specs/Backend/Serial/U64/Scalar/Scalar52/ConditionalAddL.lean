/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar52::conditional_add_l`

Specification and proof for `Scalar52::conditional_add_l`.

This function conditionally adds the group order L to a scalar based on a boolean-style choice parameter.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input unpacked scalar u and a binary condition c.
    • If condition is true (1), adds L modulo 2^260 and returns the result u' and a carry value;
      if false (0), returns the scalar unchanged.
    • This function is only used in `sub` where the carry value is ignored.

natural language specs (tailored for use in `sub`):

    • Input: limbs bounded by 2^52
    • If condition is 1 (and input ∈ [2^260 - L, 2^260)):
        - Output value: u' + 2^260 = u + L, equivalently u' = u + L - 2^260
        - Output bounded: u' < L
        - Output limbs: < 2^52
    • If condition is 0:
        - Output value: u' = u
        - Output limbs: < 2^52
    • Carry value: not specified (not used by caller)
-/

/-- **Spec for `scalar.Scalar52.conditional_add_l`** (tailored for use in `sub`):
- Requires input limbs bounded by 2^52
- When condition is 1, requires input value in [2^260 - L, 2^260)
- When condition is 1: result + 2^260 = input + L, with result < L and limbs < 2^52
- When condition is 0: result unchanged with limbs < 2^52
- Carry value not specified (not used by sub)
-/
@[progress]
theorem conditional_add_l_spec (self : Scalar52) (condition : subtle.Choice)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : condition = Choice.one → 2 ^ 260 ≤ Scalar52_as_Nat self + L)
    (hself'' : condition = Choice.one → Scalar52_as_Nat self < 2 ^ 260)
    (hself''' : condition = Choice.zero → Scalar52_as_Nat self < L) :
    ∃ result, conditional_add_l self condition = ok result ∧
    (∀ i < 5, result.2[i]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat result.2 < L) ∧
    (condition = Choice.one → Scalar52_as_Nat result.2 + 2 ^ 260 = Scalar52_as_Nat self + L) ∧
    (condition = Choice.zero → Scalar52_as_Nat result.2 = Scalar52_as_Nat self) := by
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
