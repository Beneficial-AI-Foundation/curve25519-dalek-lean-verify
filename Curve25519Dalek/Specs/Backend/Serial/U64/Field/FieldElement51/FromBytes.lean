/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
/-! # FromBytes
Specification and proof for `FieldElement51::from_bytes`.
This function constructs a field element from a 32-byte array.
Source: curve25519-dalek/src/backend/serial/u64/field.rs

-/
set_option linter.style.induction false

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
open Aeneas
open scoped Aeneas
open Aeneas.Std Result
open scoped BigOperators

/-! ## Spec for `load8_at` -/
/-- Spec for `backend.serial.u64.field.FieldElement51.from_bytes.load8_at`.
Loads 8 bytes from a slice starting at index `i` and interprets them as a little-endian U64.
Specification:
- Requires at least 8 bytes available from index i
- Returns the 64-bit value formed by bytes[i..i+8] in little-endian order
-/

theorem byte_testBit_of_ge (j : Nat) (hj : 8 ≤ j) (byte : U8) : (byte.val.testBit j) = false := by
  apply Nat.testBit_lt_two_pow
  calc byte.val < 2 ^ 8 := by scalar_tac
    _ ≤ 2^j := by apply Nat.pow_le_pow_right (by omega); omega

theorem U8_shiftLeft_lt {n : Nat} (hn : n ≤ 56) (byte : U8) : byte.val <<< n < U64.size := by
  interval_cases n
  all_goals scalar_tac

-- TODO: this proof is long and repetitive; refactor.
/- **Bit-level spec for `backend.serial.u64.field.FieldElement51.from_bytes.load8_at`**:
Each bit j of the result corresponds to bit (j mod 8) of byte (j / 8) in the input slice.
Specification phrased in terms of individual bits:
- Bit j of the result equals bit (j mod 8) of input[i + j/8]
- This captures the little-endian byte ordering where lower-indexed bytes contribute to lower bits
-/

set_option maxHeartbeats 100000000000 in
-- simp_alll heavy


@[progress]
theorem load8_at_spec_bitwise (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      ∀ (j : Nat), j < 64 →
        result.val.testBit j = (input.val[i.val + j / 8]!).val.testBit (j % 8) ⦄ := by
  sorry

lemma bytes_mod255 (bytes : Array U8 32#usize) :(U8x32_as_Nat bytes % 2^255) =
 ( ∑ i ∈ Finset.range 31, 2^(8 * i) * (bytes[i]!).val
 + 2^(8 * 31) * ( (bytes.val[31].val)%2
 + 2 ^ 1 * ((bytes.val[31].val >>> 1)%2)
 + 2 ^ 2 * ((bytes.val[31].val >>>2)%2 )
 + 2 ^3 * ((bytes.val[31].val >>>3)%2 )
 + 2 ^4 * ((bytes.val[31].val >>>4)%2 )
 + 2 ^5 * ((bytes.val[31].val >>>5)%2 )
 + 2 ^6 * ((bytes.val[31].val >>>6)%2))) %2^255 := by
  sorry

lemma bytes_lt (n : Nat) (bytes : Array U8 32#usize) :
  ∑ i ∈ Finset.range n, 2^(8 * i) * (bytes[i]!).val < 2^(8 * n) := by
  induction' n with n hn
  · simp
  · rw [Finset.sum_range_succ]
    have hbyte : (bytes[n]!).val < 2^8 := by
      scalar_tac
    have hbyte' := Nat.le_pred_of_lt hbyte
    have hpos : 0 < 2^(8 * n) := by simp
    have hmul := Nat.mul_le_mul_left (2^(8 * n)) hbyte'
    have hle := Nat.add_le_add_left hmul (2^(8 * n))
    have hlt := Nat.add_lt_add_right hn (2^(8 * n) * (bytes[n]!).val)
    have eq1 :
        2^(8 * n) + 2^(8 * n) * (2^8).pred = 2^(8 * (n + 1)) := by
      rw [Nat.mul_add, Nat.pred_eq_sub_one]
      ring
    have h := Nat.lt_of_lt_of_le hlt hle
    rw [eq1] at h
    exact h

lemma bytes_mod_lt (bytes : Array U8 32#usize) :
  ( ∑ i ∈ Finset.range 31, 2^(8 * i) * (bytes[i]!).val
  + 2^(8 * 31) *
      (  (bytes.val[31].val % 2)
      + 2^1 * ((bytes.val[31].val >>> 1) % 2)
      + 2^2 * ((bytes.val[31].val >>> 2) % 2)
      + 2^3 * ((bytes.val[31].val >>> 3) % 2)
      + 2^4 * ((bytes.val[31].val >>> 4) % 2)
      + 2^5 * ((bytes.val[31].val >>> 5) % 2)
      + 2^6 * ((bytes.val[31].val >>> 6) % 2))) < 2^255 := by
  sorry

lemma bytes_mod255_eq
    (bytes : Array U8 32#usize) :
    U8x32_as_Nat bytes % 2^255 =
      (∑ i ∈ Finset.range 31, 2^(8 * i) * (bytes[i]!).val)
      + 2^(8 * 31) *
        (  (bytes.val[31].val % 2)
        + 2^1 * ((bytes.val[31].val >>> 1) % 2)
        + 2^2 * ((bytes.val[31].val >>> 2) % 2)
        + 2^3 * ((bytes.val[31].val >>> 3) % 2)
        + 2^4 * ((bytes.val[31].val >>> 4) % 2)
        + 2^5 * ((bytes.val[31].val >>> 5) % 2)
        + 2^6 * ((bytes.val[31].val >>> 6) % 2)) := by
  sorry

set_option maxHeartbeats 100000000000 in
-- simp_alll heavy


@[progress]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ result =>
      Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
