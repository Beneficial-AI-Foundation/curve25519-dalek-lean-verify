/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
/-!
# Spec Theorem for `FieldElement51::is_negative`

Specification and proof for `FieldElement51::is_negative`.

This function checks whether a field element is "negative" in the sense used by
curve25519-dalek, namely whether the least significant bit of its canonical
little-endian encoding is set. Concretely, it returns the LSB of the first byte
of `to_bytes(self)` as a `subtle.Choice`.

Mathematically, this corresponds to the parity of the canonical representative
of the residue modulo `p = 2^255 - 19`.

**Source**: curve25519-dalek/src/field.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.field.FieldElement51

/-!
Natural language description:

- For a field element `r` in 𝔽_p, represented in radix 2^51 (five u64 limbs),
  compute the least significant bit of its canonical encoding
  (equivalently, the parity of `Field51_as_Nat(r) % p`).
- Returns a `subtle.Choice` (0 = even, 1 = odd).

Spec:

- Function succeeds (no panic).
- For any field element `r`, the result `c` satisfies
  `c.val = 1 ↔ (Field51_as_Nat(r) % p) % 2 = 1`.
-/

/-- Helper: characterize when a `subtle.Choice` encodes the value 1. -/
lemma Choice.val_eq_one_iff (c : subtle.Choice) :
  c.val = 1#u8 ↔ c = Choice.one := by
  cases c with
  | mk val valid =>
    simp [Choice.one]

/-- **Spec and proof concerning `FieldElement51.is_negative`.** -/

theorem first_bit (bytes : Aeneas.Std.Array U8 32#usize) :
   U8x32_as_Nat bytes  % 2 = (bytes.val[0]).val %2 := by
   rw[← Nat.ModEq]
   apply Nat.ModEq.symm
   rw[Nat.modEq_iff_dvd]
   unfold U8x32_as_Nat
   simp[Finset.sum_range_succ]
   scalar_tac

@[progress]
theorem is_negative_spec (r : backend.serial.u64.field.FieldElement51) :
    ∃ c, is_negative r = ok c ∧
    (c.val = 1#u8 ↔ (Field51_as_Nat r % p) % 2 = 1) := by
  /-
  Outline (mirrors the extracted code):
  - `to_bytes r` returns the canonical encoding of `r mod p`;
  - `is_negative` reads the first byte and ANDs with 1, then converts to Choice.
  Therefore, `c = 1` iff the least significant bit of the canonical encoding is 1,
  which is equivalent to `(Field51_as_Nat r % p) mod 2 = 1`.
  The full proof would relate `to_bytes` to `Field51_as_Nat r % p` and show that the
  LSB of the first byte equals parity.
  -/
  unfold is_negative
  progress*
  unfold subtle.FromChoiceU8.from
  simp_all
  have : i1.val<2:= by
   rw[i1_post_1]
   apply Nat.mod_lt
   simp
  have h01 : i1.val = 0 ∨ i1.val = 1 := by
   have :=(Nat.lt_succ_iff.mp (by simpa using this))
   interval_cases i1.val
   all_goals simp
  rcases h01 with zero | one
  · progress*
    simp_all
    rename_i h
    rw[Nat.ModEq] at bytes_post_1
    rw[← bytes_post_1 ]
    have := Nat.mod_eq_of_lt bytes_post_2
    simp[this, first_bit]
    apply i1_post_1
  · progress*
    simp_all
    rename_i h
    rw[Nat.ModEq] at bytes_post_1
    rw[← bytes_post_1 ]
    have := Nat.mod_eq_of_lt bytes_post_2
    simp[this, first_bit]
    apply i1_post_1

end curve25519_dalek.field.FieldElement51
