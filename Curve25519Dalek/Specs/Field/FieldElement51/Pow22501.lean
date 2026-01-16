/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
/-! # Spec Theorem for `FieldElement51::pow22501`

Specification and proof for `FieldElement51::pow22501`.

This function computes (r^(2^250-1), r^11) for a field element r in 𝔽_p where p = 2^255 - 19.

**Source**: curve25519-dalek/src/field.rs

-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.field.FieldElement51

set_option exponentiation.threshold 100000
/-
Natural language description:

    • Computes a pair of powers: (r^(2^250-1), r^11) for a field element r in 𝔽_p where p = 2^255 - 19
    • The field element is represented in radix 2^51 form with five u64 limbs
    • This is a helper function used in computing field inversions and other exponentiations

Natural language specs:

    • The function succeeds (no panic)
    • For any field element r, the result (r1, r2) satisfies:
      - Field51_as_Nat(r1) ≡ Field51_as_Nat(r)^(2^250-1) (mod p)
      - Field51_as_Nat(r2) ≡ Field51_as_Nat(r)^11 (mod p)
-/

/-- **Spec and proof concerning `field.FieldElement51.pow22501`**:
- No panic (always returns (r1, r2) successfully)
- Field51_as_Nat(r1) ≡ Field51_as_Nat(r)^(2^250-1) (mod p)
  Field51_as_Nat(r2) ≡ Field51_as_Nat(r)^11 (mod p)
-/
@[progress]
theorem pow22501_spec (r : backend.serial.u64.field.FieldElement51) (h_bounds : ∀ i, i < 5 → (r[i]!).val < 2 ^ 54) :
    pow22501 r ⦃ r1 r2 =>
      Field51_as_Nat r1 % p = (Field51_as_Nat r ^ (2 ^ 250 - 1)) % p ∧
      Field51_as_Nat r2 % p = (Field51_as_Nat r ^ 11) % p ∧
      (∀ i, i < 5 → (r1[i]!).val < 2 ^ 52) ∧
      (∀ i, i < 5 → (r2[i]!).val < 2 ^ 52) ⦄ := by
  sorry

end curve25519_dalek.field.FieldElement51
