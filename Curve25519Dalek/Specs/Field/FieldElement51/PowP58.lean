/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Field.FieldElement51.Pow22501
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
/-! # Spec Theorem for `FieldElement51::pow_p58`

Specification and proof for `FieldElement51::pow_p58`.

This function computes r^((p-5)/8) for a field element r in 𝔽_p where p = 2^255 - 19
and thus (p-5)/8 = 2^252 -3

**Source**: curve25519-dalek/src/field.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.field.FieldElement51

/-
Natural language description:

    • Computes r^((p-5)/8) = r^(2^252-3) for a field element r in 𝔽_p where p = 2^255 - 19
    • The field element is represented in radix 2^51 form with five u64 limbs

Natural language specs:

    • The function succeeds (no panic)
    • For any field element r, the result r' satisfies:
      - Field51_as_Nat(r') ≡ Field51_as_Nat(r)^(2^252-3) (mod p)
-/

/-- **Spec and proof concerning `field.FieldElement51.pow_p58`**:
- No panic for field element inputs r (always returns r' successfully)
- Field51_as_Nat(r') ≡ Field51_as_Nat(r)^(2^252-3) (mod p)
-/
@[progress]
theorem pow_p58_spec (r : backend.serial.u64.field.FieldElement51) (h_bounds : ∀ i, i < 5 → (r[i]!).val ≤ 2 ^ 52 - 1) :
    pow_p58 r ⦃ r' =>
      Field51_as_Nat r' % p = (Field51_as_Nat r ^ (2 ^ 252 - 3)) % p ∧
      (∀ i, i < 5 → (r'[i]!).val ≤ 2 ^ 52 - 1) ⦄ := by
  sorry

end curve25519_dalek.field.FieldElement51
