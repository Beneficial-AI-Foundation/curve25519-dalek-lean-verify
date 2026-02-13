/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Field.FieldElement51.Pow22501
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
/-! # Spec Theorem for `FieldElement51::pow_p58`

Specification and proof for `FieldElement51::pow_p58`.

This function computes r^((p-5)/8) for a field element r in 𝔽_p where p = 2^255 - 19
and thus (p-5)/8 = 2^252 -3

**Source**: curve25519-dalek/src/field.rs
-/

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
    ∃ r', pow_p58 r = ok r' ∧
    Field51_as_Nat r' % p = (Field51_as_Nat r ^ (2 ^ 252 - 3)) % p ∧
    (∀ i, i < 5 → (r'[i]!).val ≤ 2 ^ 52 - 1)
    := by
    unfold pow_p58
    progress*
    · intro i hi
      apply lt_of_le_of_lt (h_bounds i hi)
      simp
    · intro i hi
      apply lt_trans  (__discr_post_3 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_bounds i hi)
      simp
    · intro i hi
      apply lt_trans  (t20_post_1 i hi)
      simp
    constructor
    · rw[← Nat.ModEq]
      apply Nat.ModEq.trans  res_post_1
      have := Nat.ModEq.mul_left (Field51_as_Nat r) t20_post_2
      apply Nat.ModEq.trans  this
      rw[← Nat.ModEq] at __discr_post_1
      have := Nat.ModEq.pow 4 __discr_post_1
      have := Nat.ModEq.mul_left (Field51_as_Nat r) this
      apply Nat.ModEq.trans  this
      rw[← pow_mul]
      have one:= pow_one (Field51_as_Nat r)
      have := pow_add (Field51_as_Nat r) 1 (1809251394333065553493296640760748560207343510400633813116524750123642650623 * 4)
      rw[one] at this
      simp[← this]
      apply Nat.ModEq.rfl
    · intro i hi
      apply Nat.le_pred_of_lt (res_post_2 i hi)

end curve25519_dalek.field.FieldElement51
