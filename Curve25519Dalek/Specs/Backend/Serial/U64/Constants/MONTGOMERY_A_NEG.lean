/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec Theorem for `constants::MONTGOMERY_A_NEG`

Specification and proof for the constant `MONTGOMERY_A_NEG`.

This constant represents the negation of the Montgomery curve parameter A
in the curve equation By^2 = x^3 + Ax^2 + x. This is used internally within
the Elligator map.

Source: curve25519-dalek/src/backend/serial/u64/constants.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.constants

/-
natural language description:

    • constants.MONTGOMERY_A_NEG is a constant representing the negation of the
      Montgomery curve parameter A (i.e., -486662) in the defining curve equation
      By^2 = x^3 + Ax^2 + x.
    • The field element constants.MONTGOMERY_A_NEG is represented as five u64 limbs (51-bit limbs)
    • The value is -486662, which in the field equals p - 486662 where
      p = 2^255 - 19

natural language specs:

    • Field51_as_Nat(constants.MONTGOMERY_A_NEG) = 57896044618658097711785492504343953926634992332820282019728792003956564333287
      where this value represents -486662 modulo p (with p = 2^255 - 19), the mathematical
      representation of the negation of the Montgomery curve parameter A as a natural number.
-/

/-- **Spec and proof concerning `backend.serial.u64.constants.MONTGOMERY_A_NEG`**:
- The value of constants.MONTGOMERY_A_NEG when converted to a natural number equals
  p - 486662 = 57896044618658097711785492504343953926634992332820282019728792003956564333287
-/
theorem MONTGOMERY_A_NEG_spec :
    Field51_as_Nat MONTGOMERY_A_NEG + Field51_as_Nat MONTGOMERY_A= p  := by
  unfold MONTGOMERY_A_NEG p MONTGOMERY_A
  decide

end curve25519_dalek.backend.serial.u64.constants
