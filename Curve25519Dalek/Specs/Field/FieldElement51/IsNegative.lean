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

open Aeneas Aeneas.Std Result Aeneas.Std.WP
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

/-- **Spec and proof concerning `FieldElement51.is_negative`.** -/
theorem first_bit (bytes : Aeneas.Std.Array U8 32#usize) :
    U8x32_as_Nat bytes  % 2 = (bytes.val[0]).val %2 := by
  rw[← Nat.ModEq]
  apply Nat.ModEq.symm
  rw[Nat.modEq_iff_dvd]
  unfold U8x32_as_Nat
  simp only [Nat.cast_ofNat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
    List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos, Option.getD_some,
    one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT, Nat.lt_add_one,
    Nat.cast_add, Nat.cast_mul]
  scalar_tac

@[progress]
theorem is_negative_spec (r : backend.serial.u64.field.FieldElement51) :
    is_negative r ⦃ c =>
    (c.val = 1#u8 ↔ (Field51_as_Nat r % p) % 2 = 1) ⦄ := by
  unfold is_negative
  progress as ⟨bytes, h_mod, h_lt⟩
  progress as ⟨b0⟩
  progress as ⟨i1, h_i1⟩
  unfold subtle.Choice.Insts.CoreConvertFromU8.from
  simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem!_pos,
    UScalar.val_and, Nat.and_one_is_mod, UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv, U8.ofNat_bv]
  have : i1.val < 2 := by
    rw [h_i1]
    apply Nat.mod_lt
    simp
  have h01 : i1.val = 0 ∨ i1.val = 1 := by
    have := Nat.lt_succ_iff.mp (by simpa using this)
    interval_cases i1.val
    all_goals simp
  rcases h01 with zero | one
  · progress*
    simp_all only [UScalar.ofNatCore_val_eq, ReduceNat.reduceNatEq, U8.ofNat_bv,
      UScalarTy.U8_numBits_eq, Nat.ofNat_pos, Nat.not_eq, ne_eq, zero_ne_one, not_false_eq_true,
      one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq,
      false_iff, Nat.mod_two_not_eq_one]
    rw [Nat.ModEq] at h_mod
    rw [← h_mod]
    have := Nat.mod_eq_of_lt h_lt
    simp only [this, first_bit]
    exact h_i1
  · progress*
    simp_all only [UScalar.ofNatCore_val_eq, ReduceNat.reduceNatEq, U8.ofNat_bv,
      UScalarTy.U8_numBits_eq, Nat.one_lt_ofNat, Nat.not_eq, ne_eq, one_ne_zero, not_false_eq_true,
      zero_ne_one, not_lt_zero, zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq,
      true_iff]
    rw [Nat.ModEq] at h_mod
    rw [← h_mod]
    have := Nat.mod_eq_of_lt h_lt
    simp only [this, first_bit]
    exact h_i1

end curve25519_dalek.field.FieldElement51
