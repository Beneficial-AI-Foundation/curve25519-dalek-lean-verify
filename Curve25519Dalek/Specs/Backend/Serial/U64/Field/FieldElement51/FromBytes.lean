/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
/-! # FromBytes
Specification and proof for `FieldElement51::from_bytes`.
This function constructs a field element from a 32-byte array.
Source: curve25519-dalek/src/backend/serial/u64/field.rs

-/
set_option linter.style.induction false

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
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
    ∃ result, from_bytes.load8_at input i = ok result ∧
    ∀ (j : Nat), j < 64 →
      result.val.testBit j = (input.val[i.val + j / 8]!).val.testBit (j % 8) := by
  unfold from_bytes.load8_at
  progress*
  intro j hj
  simp [*]
  obtain hc | hc | hc | hc | hc | hc | hc | hc : j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 ∨ j / 8 = 3 ∨
      j / 8 = 4 ∨ j / 8 = 5 ∨ j / 8 = 6 ∨ j / 8 = 7 := by omega
  · rw [hc]
    have : j < 8 := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j by omega]
    all_goals grind
  · rw [hc]
    have : j < 16 := by omega
    have : 8 ≤ j := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j - 8 by omega]
    repeat rw [byte_testBit_of_ge _ (by grind)]
    simp only [ge_iff_le]
    rw [show decide (16 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (24 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (32 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (40 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (48 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (56 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    all_goals grind
  · rw [hc]
    have : j < 24 := by omega
    have : 16 ≤ j := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j - 16 by omega]
    repeat rw [byte_testBit_of_ge _ (by grind)]
    simp only [ge_iff_le]
    rw [show decide (8 ≤ j) by grind]
    rw [show decide (16 ≤ j) by grind]
    rw [show decide (24 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (32 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (40 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (48 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (56 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    all_goals grind
  · rw [hc]
    have : j < 32 := by omega
    have : 24 ≤ j := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j - 24 by omega]
    repeat rw [byte_testBit_of_ge _ (by grind)]
    simp only [ge_iff_le]
    rw [show decide (8 ≤ j) by grind]
    rw [show decide (16 ≤ j) by grind]
    rw [show decide (24 ≤ j) by grind]
    rw [show decide (32 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (40 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (48 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (56 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    all_goals grind
  · rw [hc]
    have : j < 40 := by omega
    have : 32 ≤ j := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j - 32 by omega]
    repeat rw [byte_testBit_of_ge _ (by grind)]
    simp only [ge_iff_le]
    rw [show decide (8 ≤ j) by grind]
    rw [show decide (16 ≤ j) by grind]
    rw [show decide (24 ≤ j) by grind]
    rw [show decide (32 ≤ j) by grind]
    rw [show decide (40 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (48 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (56 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    all_goals grind
  · rw [hc]
    have : j < 48 := by omega
    have : 40 ≤ j := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j - 40 by omega]
    repeat rw [byte_testBit_of_ge _ (by grind)]
    simp only [ge_iff_le]
    rw [show decide (8 ≤ j) by grind]
    rw [show decide (16 ≤ j) by grind]
    rw [show decide (24 ≤ j) by grind]
    rw [show decide (32 ≤ j) by grind]
    rw [show decide (40 ≤ j) by grind]
    rw [show decide (48 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    rw [show decide (56 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    all_goals grind
  · rw [hc]
    have : j < 56 := by omega
    have : 48 ≤ j := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j - 48 by omega]
    repeat rw [byte_testBit_of_ge _ (by grind)]
    simp only [ge_iff_le]
    rw [show decide (8 ≤ j) by grind]
    rw [show decide (16 ≤ j) by grind]
    rw [show decide (24 ≤ j) by grind]
    rw [show decide (32 ≤ j) by grind]
    rw [show decide (40 ≤ j) by grind]
    rw [show decide (48 ≤ j) by grind]
    rw [show decide (56 ≤ j) = false by rw [decide_eq_false_iff_not]; omega]
    all_goals grind
  · rw [hc]
    have : j < 64 := by omega
    have : 56 ≤ j := by omega
    repeat rw [Nat.mod_eq_of_lt (U8_shiftLeft_lt (by grind) _)]
    repeat rw [Nat.testBit_shiftLeft]
    rw [show j % 8 = j - 56 by omega]
    repeat rw [byte_testBit_of_ge _ (by grind)]
    simp only [ge_iff_le]
    rw [show decide (8 ≤ j) by grind]
    rw [show decide (16 ≤ j) by grind]
    rw [show decide (24 ≤ j) by grind]
    rw [show decide (32 ≤ j) by grind]
    rw [show decide (40 ≤ j) by grind]
    rw [show decide (48 ≤ j) by grind]
    rw [show decide (56 ≤ j) by grind]
    all_goals grind

theorem land_pow_two_sub_one_eq_mod (a n : Nat) :
    a &&& (2^n - 1) = a % 2^n := by
  induction n generalizing a
  · simp
    scalar_tac
  · simp

/-! ## Spec for `from_bytes` -/
/-- **Spec for `backend.serial.u64.field.FieldElement51.from_bytes`**:
Constructs a FieldElement51 from the low 255 bits of a 32-byte (256-bit) array.
The function:
1. Loads 8-byte chunks from the input
2. Extracts 51-bit limbs with appropriate shifts and masks
3. The high bit (bit 255) is masked off - only the low 255 bits are used
**Warning**: This function does not check that the input uses the canonical representative.
It masks the high bit, but will decode 2^255 - 18 to 1.
Specification:
- Always succeeds for 32-byte input
- The resulting field element value (mod p) equals the little-endian interpretation
  of the bytes with the high bit (bit 255) cleared
-/

lemma eq_of_testBit_eq (n m : ℕ)
  (h : ∀ i < 8, n.testBit i = m.testBit i)
  (hbound_n : n < 2 ^ 8)
  (hbound_m : m < 2 ^ 8) : n = m :=
by
  apply Nat.eq_of_testBit_eq
  intro i
  have := lt_or_ge i 8
  rcases this with h₁ | h₁
  · apply h
    exact h₁
  · have lt8 := (@Nat.pow_le_pow_iff_right 2 8 i (by simp)).mpr h₁
    have := Nat.lt_of_lt_of_le hbound_n lt8
    have := Nat.testBit_eq_false_of_lt this
    have := Nat.lt_of_lt_of_le hbound_m lt8
    have := Nat.testBit_eq_false_of_lt this
    simp_all

lemma ofNat64_or (a b : Nat) :
  BitVec.ofNat 64 (a ||| b)
    = BitVec.ofNat 64 a ||| BitVec.ofNat 64 b := by
  ext i
  simp [BitVec.ofNat]
  have := @Nat.or_mod_two_pow a b 64
  simp at this
  rw[this]
  apply Nat.testBit_or

theorem powTwo_split_block_remain {z n m k r : ℕ} (hmn : (k + 1) * n + r < m) :
  z % 2 ^ (k * n + r)
  + 2 ^ (k * n+r) * ((z % 2 ^ m) >>> (k * n+r) % 2 ^ n)
  = z % 2^ ( (k+1) * n+r) := by
  have :   (z % 2 ^ m) % ( 2^ ((k+1) * n +r)) = z % (2^ ((k+1) * n+r)) := by
    apply Nat.mod_mod_of_dvd;
    have := Nat.sub_add_cancel (Nat.le_of_lt hmn)
    rw[← this]
    simp[pow_add]
  rw[← this]
  rw[Nat.shiftRight_eq_div_pow]
  set r1:=z % 2^m with hr
  have h := Nat.div_add_mod (r1 / 2^(k * n +r)) (2 ^  n)
  have h₁ := Nat.div_add_mod r1 (2 ^ (k * n + r))
  have :   r1 % (2 ^(k * n +r)) = z  % (2^(k * n+r)) := by
    rw[hr]
    apply Nat.mod_mod_of_dvd
    have : k* n + r < m := by
      have hk : k * n +r ≤ (k + 1) * n +r := by
        calc
          k * n +r ≤ k * n + n + r:= by simp
          _   = k * n + 1 * n + r:= by simp
          _   = (k + 1) * n +r:= by rw[Nat.add_mul]
      exact lt_of_le_of_lt hk hmn
    have := Nat.sub_add_cancel (Nat.le_of_lt this)
    rw[← this]
    simp[pow_add]
  rw[this,← h, mul_add] at h₁
  have h2 := Nat.div_add_mod r1 (2^(k*n+r) * 2^n)
  have :
    2^(k*n+r) * (2^n * (r1 / 2^(k*n +r) / 2^n))
      = 2^(k*n+r) * 2^n * (r1 / (2^(k*n+r) * 2^n)) := by
    rw[mul_assoc]
    simp [Nat.div_div_eq_div_mul]
  rw[this] at h₁
  rw[add_comm]
  apply @Nat.add_left_cancel (2^(k*n+r) * 2^n * (r1 / (2^(k*n+r) * 2^n)))
  rw[← add_assoc, h₁]
  have : 2 ^ ((k+1) * n+r)= 2 ^ (k*n+r) * 2^n := by
    have : (k+1) * n +r = k*n +r + n := by ring
    simp [this, pow_add]
  rw[this, h2]

theorem powTwo_split_block {z n m k : ℕ} (hmn : (k + 1) * n < m) :
  z % 2 ^ (k * n) + 2 ^ (k * n) * ((z % 2 ^ m) >>> (k * n) % 2 ^ n) = z % 2^ ( (k+1) * n) := by
  exact @powTwo_split_block_remain _ _ _ _ 0 (by simp[hmn])

theorem powTwo_8_block_split {n m : ℕ} (z : Nat) (hmn : 8 * n < m) :
  z % 2 ^ n
  + 2 ^ n * ((z % 2 ^ m) >>> n % 2 ^ n)
  + 2 ^ (2*n) * ((z % 2 ^ m) >>> (2*n) % 2 ^ n)
  + 2 ^ (3*n) * ((z % 2 ^ m) >>>(3 * n) % 2 ^ n)
  + 2 ^ (4*n) * ((z % 2 ^ m) >>>( 4 * n) % 2 ^ n)
  + 2 ^ (5*n) * ((z % 2 ^ m) >>> (5 *n) % 2 ^ n)
  + 2 ^ (6*n) * ((z % 2 ^ m) >>> (6 *n) % 2 ^ n)
  + 2 ^ (7*n) * ((z % 2 ^ m) >>> (7 *n) % 2 ^ n)
  = z % 2 ^ (8 * n) := by
  have : 2 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 1 (by simp[this])
  simp at this
  rw[this]
  have : 3 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 2 (by simp[this])
  simp at this
  rw[this]
  have : 4 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 3 (by simp[this])
  simp at this
  rw[this]
  have : 5 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 4 (by simp[this])
  simp at this
  rw[this]
  have : 6 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 5 (by simp[this])
  simp at this
  rw[this]
  have : 7 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 6 (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block z n m 7 (by simp[hmn])
  simp at this
  apply this

theorem powTwo_six_block_split {n m : ℕ} (z : Nat) (hmn : 6 * n < m) :
  z % 2 ^ n --0
  + 2 ^ n * ((z % 2 ^ m) >>> n % 2 ^ n) --8
  + 2 ^ (2*n) * ((z % 2 ^ m) >>> (2*n) % 2 ^ n) --16
  + 2 ^ (3*n) * ((z % 2 ^ m) >>>(3 * n) % 2 ^ n) --24
  + 2 ^ (4*n) * ((z % 2 ^ m) >>>( 4 * n) % 2 ^ n) --32
  + 2 ^ (5*n) * ((z % 2 ^ m) >>> (5 *n) % 2 ^ n) --40
  = z % 2 ^ (6 * n) := by
  have : 2 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 1 (by simp[this])
  simp at this
  rw[this]
  have : 3 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 2 (by simp[this])
  simp at this
  rw[this]
  have : 4 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 3 (by simp[this])
  simp at this
  rw[this]
  have : 5 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 4 (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block z n m 5 (by simp[hmn])
  simp at this
  apply this

theorem powTwo_seven_block_split {n m : ℕ} (z : Nat) (hmn : 7 * n < m) :
  z % 2 ^ n
  + 2 ^ n * ((z % 2 ^ m) >>> n % 2 ^ n)
  + 2 ^ (2*n) * ((z % 2 ^ m) >>> (2*n) % 2 ^ n)
  + 2 ^ (3*n) * ((z % 2 ^ m) >>>(3 * n) % 2 ^ n)
  + 2 ^ (4*n) * ((z % 2 ^ m) >>>( 4 * n) % 2 ^ n)
  + 2 ^ (5*n) * ((z % 2 ^ m) >>> (5 *n) % 2 ^ n)
  + 2 ^ (6*n) * ((z % 2 ^ m) >>> (6 *n) % 2 ^ n)
  = z % 2 ^ (7 * n) := by
  have : 2 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 1 (by simp[this])
  simp at this
  rw[this]
  have : 3 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 2 (by simp[this])
  simp at this
  rw[this]
  have : 4 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 3 (by simp[this])
  simp at this
  rw[this]
  have : 5 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 4 (by simp[this])
  simp at this
  rw[this]
  have : 6 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 5 (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block z n m 6 (by simp[hmn])
  simp at this
  apply this

theorem powTwo_five_block_split {n m : ℕ} (z : Nat) (hmn : 5 * n < m) :
  z % 2 ^ n
  + 2 ^ n * ((z % 2 ^ m) >>> n % 2 ^ n)
  + 2 ^ (2*n) * ((z % 2 ^ m) >>> (2*n) % 2 ^ n)
  + 2 ^ (3*n) * ((z % 2 ^ m) >>>(3 * n) % 2 ^ n)
  + 2 ^ (4*n) * ((z % 2 ^ m) >>>( 4 * n) % 2 ^ n)
  = z % 2 ^ (5 * n) := by
  have : 2 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 1 (by simp[this])
  simp at this
  rw[this]
  have : 3 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 2 (by simp[this])
  simp at this
  rw[this]
  have : 4 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 3 (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block z n m 4 (by simp[hmn])
  simp at this
  apply this

theorem powTwo_three_block_split {n m : ℕ} (z : Nat) (hmn : 3 * n < m) :
  z % 2 ^ n
  + 2 ^ n * ((z % 2 ^ m) >>> n % 2 ^ n)
  + 2 ^ (2*n) * ((z % 2 ^ m) >>> (2*n) % 2 ^ n)
  = z % 2 ^ (3 * n) := by
  have : 2 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 1 (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block z n m 2 (by simp[hmn])
  simp at this
  apply this

theorem powTwo_two_block_split {n m : ℕ} (z : Nat) (hmn : 2 * n < m) :
  z % 2 ^ n
  + 2 ^ n * ((z % 2 ^ m) >>> n % 2 ^ n)
  = z % 2 ^ (2 * n) := by
  have := @powTwo_split_block z n m 1 (by simp[hmn])
  simp at this
  apply this

theorem powTwo_four_block_split {n m : ℕ} (z : Nat) (hmn : 4 * n < m) :
  z % 2 ^ n
  + 2 ^ n * ((z % 2 ^ m) >>> n % 2 ^ n)
  + 2 ^ (2*n) * ((z % 2 ^ m) >>> (2*n) % 2 ^ n)
  + 2 ^ (3*n) * ((z % 2 ^ m) >>> (3*n) % 2 ^ n)
  = z % 2 ^ (4 * n) := by
  have : 2 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 1 (by simp[this])
  simp at this
  rw[this]
  have : 3 * n < m := by
    scalar_tac
  have := @powTwo_split_block z n m 2 (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block z n m 3 (by simp[hmn])
  simp at this
  apply this

theorem powTwo_block_split_51 (z : ℕ) :
  z % 2 ^ 8 --0
  + 2 ^ 8 * ((z % 2 ^ 51)  >>> 8 % 2 ^ 8) --8
  + 2 ^ 16 * ((z % 2 ^ 51)  >>> 16 % 2 ^ 8) --16
  + 2 ^ 24 * ((z % 2 ^ 51)   >>> 24 % 2 ^ 8) --24
  + 2 ^ 32 * ((z % 2 ^ 51)   >>> 32 % 2 ^ 8) --32
  + 2 ^ 40 * ((z % 2 ^ 51)   >>> 40 % 2 ^ 8) --40
  + 2 ^ 48 * (
        ((z % 2 ^ 51)   >>> 48) % 2
        + 2* (((z % 2 ^ 51)   >>> 48) >>> 1 % 2)
        + 2 ^2 * (((z % 2 ^ 51)   >>> 48) >>> 2 % 2)
        )
  = z % 2^ 51 := by
  have := powTwo_six_block_split z (by simp : 6 * 8 < 51)
  rw [this]
  have mod51: ((z % 2 ^ 51)   >>> 48) % 2^51 = (z % 2 ^ 51)   >>> 48 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply lt_trans (Nat.mod_lt z (by simp))
    simp
  have := powTwo_three_block_split ((z % 2 ^ 51)   >>> 48) (by simp : 3 * 1 < 51)
  rw [mod51] at this
  simp at this
  simp [this]
  have mod8: ((z % 2251799813685248)   >>> 48) % 8 = (z % 2251799813685248)   >>> 48 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply Nat.mod_lt z (by simp)
  rw [mod8, Nat.shiftRight_eq_div_pow]
  have := Nat.div_add_mod  (z % 2 ^ 51) (2 ^ 48)
  simp [add_comm] at this
  simp [this]

theorem powTwo_split_block_5 {n m r : ℕ} (z : ℕ) (hmn : 5 * n + r < m) :
  z % 2 ^ (r)
  + 2 ^ (r) * ((z % 2 ^ m) >>> (r) % 2 ^ n)
  + 2 ^ (1 * n+r) * ((z % 2 ^ m) >>> (1 * n+r) % 2 ^ n)
  + 2 ^ (2 * n+r) * ((z % 2 ^ m) >>> (2 * n+r) % 2 ^ n)
  + 2 ^ (3 * n+r) * ((z % 2 ^ m) >>> (3 * n+r) % 2 ^ n)
  + 2 ^ (4 * n+r) * ((z % 2 ^ m) >>> (4 * n+r) % 2 ^ n)
  = z % 2^ (5 * n+r) := by
  have : n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 0 r (by simp[this])
  simp at this
  simp[this]
  have : 2*n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 1 r (by simp[this])
  simp at this
  rw[this]
  have : 3*n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 2 r (by simp[this])
  simp at this
  rw[this]
  have : 4*n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 3 r (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block_remain z n m 4 r (by simp[hmn])
  simp at this
  rw[this]

theorem powTwo_block_split_51_remain5 (z : ℕ) :
  z % 2 ^ 5
  + 2 ^ 5 * ((z % 2 ^ 51)  >>> 5 % 2 ^ 8)
  + 2 ^ 13 * ((z % 2 ^ 51)  >>> 13 % 2 ^ 8)
  + 2 ^ 21 * ((z % 2 ^ 51)   >>> 21 % 2 ^ 8)
  + 2 ^ 29 * ((z % 2 ^ 51)   >>> 29 % 2 ^ 8)
  + 2 ^ 37 * ((z % 2 ^ 51)   >>> 37 % 2 ^ 8)
  + 2 ^ 45 * (
        ((z % 2 ^ 51)   >>> 45) % 2
        + 2* (((z % 2 ^ 51)   >>> 45) >>> 1 % 2)
        + 2 ^2 * (((z % 2 ^ 51)   >>> 45) >>> 2 % 2)
        + 2 ^3 * (((z % 2 ^ 51)   >>> 45) >>> 3 % 2)
        + 2 ^4 * (((z % 2 ^ 51)   >>> 45) >>> 4 % 2)
        + 2 ^5 * (((z % 2 ^ 51)   >>> 45) >>> 5 % 2)
        )
  = z % 2^ 51 := by
  have := powTwo_split_block_5 z (by simp : 5 * 8 + 5 < 51)
  rw[this]
  have mod51: ((z % 2 ^ 51)   >>> 45) % 2^51 = (z % 2 ^ 51)   >>> 45 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply lt_trans (Nat.mod_lt z (by simp))
    simp
  have := powTwo_six_block_split ((z % 2 ^ 51)   >>> 45) (by simp : 6 * 1 < 51)
  rw[mod51] at this
  simp at this
  simp[this]
  have mod8: ((z % 2251799813685248)   >>> 45) % 64 = (z % 2251799813685248)   >>> 45 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply Nat.mod_lt z (by simp)
  rw[mod8,  Nat.shiftRight_eq_div_pow]
  have := Nat.div_add_mod  (z % 2 ^ 51) (2 ^ 45)
  simp[add_comm] at this
  simp[this]

theorem powTwo_split_block_6 {n m r : ℕ} (z : ℕ) (hmn : 6 * n + r < m) :
  z % 2 ^ (r)
  + 2 ^ (r) * ((z % 2 ^ m) >>> (r) % 2 ^ n)
  + 2 ^ (1 * n+r) * ((z % 2 ^ m) >>> (1 * n+r) % 2 ^ n)
  + 2 ^ (2 * n+r) * ((z % 2 ^ m) >>> (2 * n+r) % 2 ^ n)
  + 2 ^ (3 * n+r) * ((z % 2 ^ m) >>> (3 * n+r) % 2 ^ n)
  + 2 ^ (4 * n+r) * ((z % 2 ^ m) >>> (4 * n+r) % 2 ^ n)
  + 2 ^ (5 * n+r) * ((z % 2 ^ m) >>> (5 * n+r) % 2 ^ n)
  = z % 2^ (6 * n+r) := by
  have : n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 0 r (by simp[this])
  simp at this
  simp[this]
  have : 2*n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 1 r (by simp[this])
  simp at this
  rw[this]
  have : 3*n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 2 r (by simp[this])
  simp at this
  rw[this]
  have : 4*n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 3 r (by simp[this])
  simp at this
  rw[this]
  have : 5*n +r < m := by
    scalar_tac
  have := @powTwo_split_block_remain z n m 4 r (by simp[this])
  simp at this
  rw[this]
  have := @powTwo_split_block_remain z n m 5 r (by simp[hmn])
  simp at this
  rw[this]

theorem powTwo_block_split_51_remain2 (z : ℕ) :
  z % 2 ^ 2
  + 2 ^ 2 * ((z % 2 ^ 51)  >>> 2 % 2 ^ 8)
  + 2 ^ 10 * ((z % 2 ^ 51)  >>> 10 % 2 ^ 8)
  + 2 ^ 18 * ((z % 2 ^ 51)   >>> 18 % 2 ^ 8)
  + 2 ^ 26 * ((z % 2 ^ 51)   >>> 26 % 2 ^ 8)
  + 2 ^ 34 * ((z % 2 ^ 51)   >>> 34 % 2 ^ 8)
  + 2 ^ 42 * ((z % 2 ^ 51)   >>> 42 % 2 ^ 8)
  + 2 ^ 50 * ( ((z % 2 ^ 51)   >>> 50) % 2)
  = z % 2^ 51 := by
  have := powTwo_split_block_6 z (by simp : 6 * 8 + 2 < 51)
  rw[this]
  have mod51: ((z % 2 ^ 51)   >>> 50) % 2^51 = (z % 2 ^ 51)   >>> 50 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply lt_trans (Nat.mod_lt z (by simp))
    simp
  have mod8: ((z %  2 ^ 51)   >>> 50) % 2 = (z % 2 ^ 51)   >>> 50 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply Nat.mod_lt z (by simp)
  rw[mod8, Nat.shiftRight_eq_div_pow]
  have := Nat.div_add_mod  (z % 2 ^ 51) (2 ^ 50)
  simp[add_comm] at this
  simp[this]

theorem powTwo_block_split_51_remain7 (z : ℕ) :
  z % 2^7
    + 2^7  * ((z % 2^51) >>> 7  % 2^8)
    + 2^15 * ((z % 2^51) >>> 15 % 2^8)
    + 2^23 * ((z % 2^51) >>> 23 % 2^8)
    + 2^31 * ((z % 2^51) >>> 31 % 2^8)
    + 2^39 * ((z % 2^51) >>> 39 % 2^8)
    + 2^47 *
        (  ((z % 2^51) >>> 47) % 2
        + 2    * (((z % 2^51) >>> 47) >>> 1 % 2)
        + 2^2  * (((z % 2^51) >>> 47) >>> 2 % 2)
        + 2^3  * (((z % 2^51) >>> 47) >>> 3 % 2)
        )
    = z % 2^51 := by
  have := powTwo_split_block_5 z (by simp : 5 * 8 + 7 < 51)
  rw [this]
  have mod51 :
      ((z % 2^51) >>> 47) % 2^51 = (z % 2^51) >>> 47 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply lt_trans (Nat.mod_lt z (by simp))
    simp
  have := powTwo_four_block_split ((z % 2^51) >>> 47) (by simp : 4 * 1 < 51)
  rw [mod51] at this
  simp at this
  simp [this]
  have mod8 :
      ((z % 2251799813685248) >>> 47) % 16
        = (z % 2251799813685248) >>> 47 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply Nat.mod_lt z (by simp)
  rw [mod8, Nat.shiftRight_eq_div_pow]
  have := Nat.div_add_mod (z % 2^51) (2^47)
  simp [add_comm] at this
  simp [this]

theorem powTwo_block_split_51_remain4 (z : ℕ) :
  z % 2^4
    + 2^4  * ((z % 2^51) >>> 4  % 2^8)
    + 2^12 * ((z % 2^51) >>> 12 % 2^8)
    + 2^20 * ((z % 2^51) >>> 20 % 2^8)
    + 2^28 * ((z % 2^51) >>> 28 % 2^8)
    + 2^36 * ((z % 2^51) >>> 36 % 2^8)
    + 2^44 *
        (  ((z % 2^51) >>> 44) % 2
        + 2    * (((z % 2^51) >>> 44) >>> 1 % 2)
        + 2^2  * (((z % 2^51) >>> 44) >>> 2 % 2)
        + 2^3  * (((z % 2^51) >>> 44) >>> 3 % 2)
        + 2^4  * (((z % 2^51) >>> 44) >>> 4 % 2)
        + 2^5  * (((z % 2^51) >>> 44) >>> 5 % 2)
        + 2^6  * (((z % 2^51) >>> 44) >>> 6 % 2)
        )
    = z % 2^51 := by
  have := powTwo_split_block_5 z (by simp : 5 * 8 + 4 < 51)
  rw [this]
  have mod51 :
      ((z % 2^51) >>> 44) % 2^51 = (z % 2^51) >>> 44 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply lt_trans (Nat.mod_lt z (by simp))
    simp
  have := powTwo_seven_block_split ((z % 2^51) >>> 44) (by simp : 7 * 1 < 51)
  rw [mod51] at this
  simp at this
  simp [this]
  have mod8 :
      ((z % 2251799813685248) >>> 44) % 128
        = (z % 2251799813685248) >>> 44 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply Nat.mod_lt z (by simp)
  rw [mod8, Nat.shiftRight_eq_div_pow]
  have := Nat.div_add_mod (z % 2^51) (2^44)
  simp [add_comm] at this
  simp [this]

lemma bytes_mod255 (bytes : Array U8 32#usize) :(U8x32_as_Nat bytes % 2^255) =
 ( ∑ i ∈ Finset.range 31, 2^(8 * i) * (bytes[i]!).val
 + 2^(8 * 31) * ( (bytes.val[31].val)%2
 + 2 ^ 1 * ((bytes.val[31].val >>> 1)%2)
 + 2 ^ 2 * ((bytes.val[31].val >>>2)%2 )
 + 2 ^3 * ((bytes.val[31].val >>>3)%2 )
 + 2 ^4 * ((bytes.val[31].val >>>4)%2 )
 + 2 ^5 * ((bytes.val[31].val >>>5)%2 )
 + 2 ^6 * ((bytes.val[31].val >>>6)%2))) %2^255 := by
  have mod8:  (bytes.val[31]).val % 2^8 = (bytes.val[31]).val := by
   apply  Nat.mod_eq_of_lt
   scalar_tac
  have := @powTwo_seven_block_split 1 8 (bytes.val[31].val) (by simp)
  rw [mod8] at this
  simp at this
  simp [this]
  simp_all [U8x32_as_Nat, Finset.sum_range_succ]
  rw [← Nat.ModEq, Nat.modEq_iff_dvd]
  simp
  have := Nat.div_add_mod ((bytes.val[31]).val) 128
  rw [← this]
  simp [mul_add]
  simp [← mul_assoc]

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
  have mod8 :
      (bytes.val[31]).val % 2^8 = (bytes.val[31]).val := by
    apply Nat.mod_eq_of_lt
    scalar_tac
  have := @powTwo_seven_block_split 1 8 (bytes.val[31].val) (by simp)
  rw [mod8] at this
  simp at this
  simp [this]
  have sum := bytes_lt 31 bytes
  have := Nat.mod_lt (bytes.val[31]!).val (by simp : 0 < 128)
  have := Nat.le_pred_of_lt this
  have := Nat.mul_le_mul_left (2 ^ (8 * 31)) this
  have := Nat.add_le_add (Nat.le_pred_of_lt sum) this
  simp at this
  apply Nat.lt_of_le_of_lt this
  simp

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
  rw [bytes_mod255]
  apply Nat.mod_eq_of_lt
  apply bytes_mod_lt


set_option maxHeartbeats 100000000000 in
-- simp_alll heavy


@[progress]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    ∃ result, from_bytes bytes = ok result ∧
    Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ∧
    result.IsValid := by
  unfold from_bytes
  progress*
  refine ⟨?_, ?_⟩
  swap
  · -- IsValid: each limb is (value &&& low_51_bit_mask) so < 2^51 < 2^54
    have h_mask_lt : (↑low_51_bit_mask : ℕ) < 2 ^ 54 := by
      rw [low_51_bit_mask_post_1, i_post_1];
      simp only [Nat.shiftLeft_eq, Nat.one_mul, U64.size_eq]
      try scalar_tac

    have and_mask_lt : ∀ (x : U64), (↑(x &&& low_51_bit_mask) : ℕ) < 2 ^ 54 := by
      intro x
      have : (↑(x &&& low_51_bit_mask) : ℕ) = ↑x &&& ↑low_51_bit_mask := by
        simp only [UScalar.val_and]

      rw [this]; exact lt_of_le_of_lt Nat.and_le_right h_mask_lt
    simp only [FieldElement51.IsValid, Array.make]
    intro j hj
    interval_cases j
    · simp only [Array.getElem!_Nat_eq, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.ofNat_pos, getElem!_pos, List.getElem_cons_zero]
      rw [i2_post_1];
      exact and_mask_lt i1
    · simp only [Array.getElem!_Nat_eq, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [i5_post_1]; exact and_mask_lt i4
    · simp only [Array.getElem!_Nat_eq, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLT, getElem!_pos, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [i8_post_1]; exact and_mask_lt i7
    · simp only [Array.getElem!_Nat_eq, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.reduceLT, getElem!_pos, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [i11_post_1]; exact and_mask_lt i10
    · simp only [Array.getElem!_Nat_eq, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      Nat.lt_add_one, getElem!_pos, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [i14_post_1]; exact and_mask_lt i13

  -- Congruence proof (unchanged):
  rw[bytes_mod255_eq]
  simp_all[Field51_as_Nat, Finset.sum_range_succ,Array.make, U64.size, U64.numBits,]
  have := land_pow_two_sub_one_eq_mod i1 51
  simp at this
  rw[this]
  have := land_pow_two_sub_one_eq_mod i4 51
  have := land_pow_two_sub_one_eq_mod i7 51
  have := land_pow_two_sub_one_eq_mod i10 51
  have := land_pow_two_sub_one_eq_mod i13 51
  simp_all[]
  have eqb6:= @powTwo_8_block_split 1 51 (bytes.val[6]).val (by simp)
  have :  (bytes.val[6]).val < 2^(8 *1) := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb6
  have :  (bytes.val[6]).val < 2^51 := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb6
  rw[← eqb6]
  iterate  4 (clear this)
  clear eqb6
  have eqb12:= @powTwo_8_block_split 1 51 (bytes.val[12]).val (by simp)
  have :  (bytes.val[12]).val < 2^(8 *1) := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb12
  have :  (bytes.val[12]).val < 2^51 := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb12
  rw[← eqb12]
  iterate  4 (clear this)
  clear eqb12
  have eqb19:= @powTwo_8_block_split 1 51 (bytes.val[19]).val (by simp)
  have :  (bytes.val[19]).val < 2^(8 *1) := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb19
  have :  (bytes.val[19]).val < 2^51 := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb19
  rw[← eqb19]
  iterate  4 (clear this)
  clear eqb19
  have eqb25:= @powTwo_8_block_split 1 51 (bytes.val[25]).val (by simp)
  have :  (bytes.val[25]).val < 2^(8 *1) := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb25
  have :  (bytes.val[25]).val < 2^51 := by scalar_tac
  have := Nat.mod_eq_of_lt this
  rw[this] at eqb25
  rw[← eqb25]
  iterate  4 (clear this)
  clear eqb25
  have eq0: i1.val % 2 ^ 8 = (bytes.val[0]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have : i< 64:= by apply lt_trans hi (by simp)
     have := i1_post i this
     have div8: i / 8 = 0 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8] at this
     have this1:= Nat.testBit_mod_two_pow (i1.val) 8 i
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq1: (i1.val % 2^ 51) >>> 8 % 2 ^ 8 = (bytes.val[1]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 8
     have : 8+i< 64:= by apply lt_trans this (by simp)
     have := i1_post (8+i) this
     have div8: (8+i) / 8 = 1 := by scalar_tac
     have mod8' : (8 + i ) % 8 = i % 8 := by simp
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow ((i1.val % 2^ 51) >>> 8) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i1.val) 51 (8+i)
     have : 8+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 8) (by simp)
     simp[this] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq2: ((i1.val % 2^51) >>> 16) % 2 ^ 8 = (bytes.val[2]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 16
     have : 16+i< 64:= by apply lt_trans this (by simp)
     have := i1_post (16+i) this
     have div8: (16+i) / 8 = 2 := by scalar_tac
     have mod8' : (16 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow ((i1.val % 2^ 51) >>> 16) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i1.val) 51 (16+i)
     have : 16+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 16) (by simp)
     simp[this] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq3: ((i1.val % 2^51) >>> 24) % 2 ^ 8 = (bytes.val[3]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 24
     have : 24+i< 64:= by apply lt_trans this (by simp)
     have := i1_post (24+i) this
     have div8: (24 +i) / 8 = 3 := by scalar_tac
     have mod8' : (24 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow ((i1.val % 2^ 51) >>> 24) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i1.val) 51 (24+i)
     have : 24+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 24) (by simp)
     simp[this] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq4: ((i1.val % 2^51) >>> 32) % 2 ^ 8 = (bytes.val[4]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 32
     have : 32 + i< 64:= by apply lt_trans this (by simp)
     have := i1_post (32+i) this
     have div8: (32 +i) / 8 = 4 := by scalar_tac
     have mod8' : (32 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow ((i1.val % 2^ 51) >>> 32) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i1.val) 51 (32+i)
     have : 32+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 32) (by simp)
     simp[this] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq5: ((i1.val % 2^51) >>> 40) % 2 ^ 8 = (bytes.val[5]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 40
     have : 40 + i< 64:= by apply lt_trans this (by simp)
     have := i1_post (40+i) this
     have div8: (40 +i) / 8 = 5 := by scalar_tac
     have mod8' : (40 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow ((i1.val % 2^ 51) >>> 40) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i1.val) 51 (40 + i)
     have : 40 + i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 40) (by simp)
     simp[this] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq60: ((i1.val % 2 ^ 51) >>> 48)%2 = (bytes.val[6])%2 := by
     have := Nat.toNat_testBit ((i1.val % 2 ^ 51) >>> 48) 0
     have := Nat.toNat_testBit ((bytes.val[6])) 0
     have := i1_post 48 (by simp)
     have := Nat.testBit_mod_two_pow (i1.val) 51 48
     simp_all
  have eq61: ((i1.val % 2 ^ 51) >>> 48 >>> 1) % 2 = ((bytes.val[6]).val >>> 1) %2 := by
     have := Nat.toNat_testBit ((i1.val % 2 ^ 51) >>> 48 >>> 1) 0
     have := Nat.toNat_testBit ((bytes.val[6]).val >>> 1) 0
     have := i1_post 49 (by simp)
     have := Nat.testBit_mod_two_pow (i1.val) 51 49
     simp_all
  have eq62: ((i1.val % 2 ^ 51) >>> 48 >>> 2) % 2 = ((bytes.val[6]).val >>> 2) %2 := by
     have := Nat.toNat_testBit ((i1.val % 2 ^ 51) >>> 48 >>> 2) 0
     have := Nat.toNat_testBit ((bytes.val[6]).val >>> 2) 0
     have := i1_post 50 (by simp)
     have := Nat.testBit_mod_two_pow (i1.val) 51 50
     simp_all
  have eqi1:= powTwo_block_split_51 i1.val
  rw[eq0, eq1, eq2, eq3, eq4, eq5, eq60, eq61, eq62] at eqi1
  simp at eqi1
  rw[← eqi1]
  clear eq0 eq1 eq2 eq3 eq4 eq5 eq60 eq61 eq62 eqi1 this
  clear this
  clear this
  clear this
  clear this
  simp[add_assoc, mul_add, ← mul_assoc]
  simp [← add_assoc]
  -- continue bit-block extraction
  have eq63: ((i3.val >>>3) )% 2^1 = ((bytes.val[6].val)>>>3)%2 := by
     have := Nat.toNat_testBit ((i3.val >>>3) % 2 ^ 5) 0
     have := Nat.toNat_testBit ((bytes.val[6].val)>>>3) 0
     have := i3_post 3 (by simp)
     simp_all
  have eq64: (((i3.val >>>3) % 2 ^51)   >>> 1 )% 2 ^1 = ((bytes.val[6].val)>>>4)%2 := by
     have := i3_post 4 (by simp)
     have mod_pow1:= Nat.testBit_mod_two_pow (i3.val  >>> 3) 51 1
     simp at mod_pow1
     have := Nat.toNat_testBit (((i3.val >>>3) % 2^51)   >>>1) 0
     have := Nat.toNat_testBit ((bytes.val[6].val)>>>4) 0
     simp_all
  have eq65: (((i3.val >>>3) % 2 ^51)   >>> 2 )% 2 ^1 = ((bytes.val[6].val)>>>5)%2 := by
     have := i3_post 5 (by simp)
     have mod_pow1:= Nat.testBit_mod_two_pow (i3.val  >>> 3) 51 2
     simp at mod_pow1
     have := Nat.toNat_testBit (((i3.val >>>3) % 2^51)   >>>2) 0
     have := Nat.toNat_testBit ((bytes.val[6].val)>>>5) 0
     simp_all
  have eq66: (((i3.val >>>3) % 2 ^51)   >>> 3 )% 2 ^1 = ((bytes.val[6].val)>>> 6)%2 := by
     have := i3_post 6 (by simp)
     have mod_pow1:= Nat.testBit_mod_two_pow (i3.val  >>> 3) 51 3
     simp at mod_pow1
     have := Nat.toNat_testBit (((i3.val >>>3) % 2^51)   >>>3) 0
     have := Nat.toNat_testBit ((bytes.val[6].val)>>>6) 0
     simp_all
  have eq67: (((i3.val >>>3) % 2 ^51)   >>> 4 )% 2 ^1 = ((bytes.val[6].val)>>> 7)%2 := by
     have := i3_post 7 (by simp)
     have mod_pow1:= Nat.testBit_mod_two_pow (i3.val  >>> 3) 51 4
     simp at mod_pow1
     have := Nat.toNat_testBit (((i3.val >>>3) % 2^51)   >>> 4) 0
     have := Nat.toNat_testBit ((bytes.val[6].val)>>> 7) 0
     simp_all
  have eq1: ((i3.val >>>3) % 2^ 51) >>> 5 % 2 ^ 8 = (bytes.val[7]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 8
     have : 8+i< 64:= by apply lt_trans this (by simp)
     have := i3_post (8+i) this
     have div8: (8+i) / 8 = 1 := by scalar_tac
     have mod8' : (8 + i ) % 8 = i % 8 := by simp
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i3.val >>>3) % 2^ 51) >>> 5) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i3.val >>>3) 51 (5+i)
     have : 5+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 5) (by simp)
     simp[this, (by scalar_tac : 3 + (5 + i)= 8 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq2: ((i3.val >>>3) % 2^ 51) >>> 13 % 2 ^ 8 = (bytes.val[8]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 16
     have : 16+i< 64:= by apply lt_trans this (by simp)
     have := i3_post (16+i) this
     have div8: (16+i) / 8 = 2 := by scalar_tac
     have mod8' : (16 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i3.val >>>3) % 2^ 51) >>> 13) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i3.val >>>3) 51 (13+i)
     have : 13+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 13) (by simp)
     simp[this, (by scalar_tac : 3 + (13 + i)= 16 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq3: ((i3.val >>>3) % 2^ 51) >>> 21 % 2 ^ 8 = (bytes.val[9]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 24
     have : 24+i< 64:= by apply lt_trans this (by simp)
     have := i3_post (24+i) this
     have div8: (24+i) / 8 = 3 := by scalar_tac
     have mod8' : (24 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i3.val >>>3) % 2^ 51) >>> 21) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i3.val >>>3) 51 (21+i)
     have : 21+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 21) (by simp)
     simp[this, (by scalar_tac : 3 + (21 + i)= 24 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq4: ((i3.val >>>3) % 2^ 51) >>> 29 % 2 ^ 8 = (bytes.val[10]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 32
     have : 32+i< 64:= by apply lt_trans this (by simp)
     have := i3_post (32+i) this
     have div8: (32+i) / 8 = 4 := by scalar_tac
     have mod8' : (32 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i3.val >>>3) % 2^ 51) >>> 29) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i3.val >>>3) 51 (29+i)
     have : 29+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 29) (by simp)
     simp[this, (by scalar_tac : 3 + (29 + i)= 32 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq5: ((i3.val >>>3) % 2^ 51) >>> 37 % 2 ^ 8 = (bytes.val[11]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 40
     have : 40+i< 64:= by apply lt_trans this (by simp)
     have := i3_post (40+i) this
     have div8: (40+i) / 8 = 5 := by scalar_tac
     have mod8' : (40 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i3.val >>>3) % 2^ 51) >>> 37) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i3.val >>>3) 51 (37+i)
     have : 37+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 37) (by simp)
     simp[this, (by scalar_tac : 3 + (37 + i)= 40 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq120: (((i3.val>>> 3) % 2 ^ 51) >>> 45)%2 = (bytes.val[12])%2 := by
     have := Nat.toNat_testBit (((i3.val >>>3) % 2 ^ 51) >>> 45) 0
     have := Nat.toNat_testBit ((bytes.val[12])) 0
     have := i3_post 45 (by simp)
     have := Nat.testBit_mod_two_pow (i3.val >>>3) 51 45
     simp_all
  have eq121: (((i3.val>>> 3) % 2 ^ 51) >>> 45 >>> 1)%2 = ((bytes.val[12].val) >>> 1)%2 := by
     have := Nat.toNat_testBit (((i3.val >>>3) % 2 ^ 51) >>> 45 >>> 1) 0
     have := Nat.toNat_testBit ((bytes.val[12].val)>>> 1) 0
     have := i3_post 46 (by simp)
     have := Nat.testBit_mod_two_pow (i3.val >>>3) 51 46
     simp_all
  have eq122: (((i3.val>>> 3) % 2 ^ 51) >>> 45 >>> 2)%2 = ((bytes.val[12].val) >>> 2)%2 := by
     have := Nat.toNat_testBit (((i3.val >>>3) % 2 ^ 51) >>> 45 >>> 2) 0
     have := Nat.toNat_testBit ((bytes.val[12].val)>>> 2) 0
     have := i3_post 46 (by simp)
     have := Nat.testBit_mod_two_pow (i3.val >>>3) 51 47
     simp_all
  have eq123: (((i3.val>>> 3) % 2 ^ 51) >>> 45 >>> 3)%2 = ((bytes.val[12].val) >>> 3)%2 := by
     have := Nat.toNat_testBit (((i3.val >>>3) % 2 ^ 51) >>> 45 >>> 3) 0
     have := Nat.toNat_testBit ((bytes.val[12].val)>>> 3) 0
     have := i3_post 46 (by simp)
     have := Nat.testBit_mod_two_pow (i3.val >>>3) 51 48
     simp_all
  have eq124: (((i3.val>>> 3) % 2 ^ 51) >>> 45 >>> 4)%2 = ((bytes.val[12].val) >>> 4)%2 := by
     have := Nat.toNat_testBit (((i3.val >>>3) % 2 ^ 51) >>> 45 >>> 4) 0
     have := Nat.toNat_testBit ((bytes.val[12].val)>>> 4) 0
     have := i3_post 46 (by simp)
     have := Nat.testBit_mod_two_pow (i3.val >>>3) 51 49
     simp_all
  have eq125: (((i3.val>>> 3) % 2 ^ 51) >>> 45 >>> 5)%2 = ((bytes.val[12].val) >>> 5)%2 := by
     have := Nat.toNat_testBit (((i3.val >>>3) % 2 ^ 51) >>> 45 >>> 5) 0
     have := Nat.toNat_testBit ((bytes.val[12].val)>>> 5) 0
     have := i3_post 46 (by simp)
     have := Nat.testBit_mod_two_pow (i3.val >>>3) 51 50
     simp_all
  have eqi3:= powTwo_block_split_51_remain5  (i3.val >>>3)
  have := @powTwo_five_block_split 1 51 (i3.val >>> 3) (by simp)
  rw[eq1, eq2, eq3, eq4, eq5, ← this] at eqi3
  rw[eq63, eq64, eq65, eq66, eq67] at eqi3
  rw[eq120, eq121, eq122, eq123, eq124, eq125] at eqi3
  simp at eqi3
  rw[← eqi3]
  clear eq1 eq2 eq3 eq4 eq5 eq63 eq64 eq65 eq66 eq67 eq120 eq121 eq122 eq123 eq124 eq125 eqi3 this
  have eq126: ((i6.val >>>6) )% 2^1 = ((bytes.val[12].val)>>>6)%2 := by
     have := Nat.toNat_testBit ((i6.val >>>6) % 2 ^ 5) 0
     have := Nat.toNat_testBit ((bytes.val[12].val)>>>6) 0
     have := i6_post 6 (by simp)
     simp_all
  have eq127: (((i6.val >>>6) % 2 ^51)   >>> 1 )% 2 ^1 = ((bytes.val[12].val)>>>7)%2 := by
     have := i3_post 7 (by simp)
     have mod_pow1:= Nat.testBit_mod_two_pow (i6.val  >>> 6) 51 1
     simp at mod_pow1
     have := Nat.toNat_testBit (((i6.val >>>6) % 2^51)   >>>1) 0
     have := Nat.toNat_testBit ((bytes.val[12].val)>>>7) 0
     simp_all
  have eq1: ((i6.val >>>6) % 2^ 51) >>> 2 % 2 ^ 8 = (bytes.val[13]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 8
     have : 8+i< 64:= by apply lt_trans this (by simp)
     have := i6_post (8+i) this
     have div8: (8+i) / 8 = 1 := by scalar_tac
     have mod8' : (8 + i ) % 8 = i % 8 := by simp
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i6.val >>>6) % 2^ 51) >>> 2) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i6.val >>>6) 51 (2+i)
     have : 2+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 2) (by simp)
     simp[this, (by scalar_tac : 6 + (2 + i)= 8 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq2: ((i6.val >>>6) % 2^ 51) >>> 10 % 2 ^ 8 = (bytes.val[14]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 16
     have : 16+i< 64:= by apply lt_trans this (by simp)
     have := i6_post (16+i) this
     have div8: (16+i) / 8 = 2 := by scalar_tac
     have mod8' : (16 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i6.val >>>6) % 2^ 51) >>> 10) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i6.val >>>6) 51 (10+i)
     have : 10+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 10) (by simp)
     simp[this, (by scalar_tac : 6 + (10 + i)= 16 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq3: ((i6.val >>>6) % 2^ 51) >>> 18 % 2 ^ 8 = (bytes.val[15]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 24
     have : 24+i< 64:= by apply lt_trans this (by simp)
     have := i6_post (24+i) this
     have div8: (24+i) / 8 = 3 := by scalar_tac
     have mod8' : (24 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i6.val >>>6) % 2^ 51) >>> 18) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i6.val >>>6) 51 (18+i)
     have : 18+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 18) (by simp)
     simp[this, (by scalar_tac : 6 + (18 + i)= 24 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq4: ((i6.val >>>6) % 2^ 51) >>> 26 % 2 ^ 8 = (bytes.val[16]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 32
     have : 32+i< 64:= by apply lt_trans this (by simp)
     have := i6_post (32+i) this
     have div8: (32+i) / 8 = 4 := by scalar_tac
     have mod8' : (32 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i6.val >>>6) % 2^ 51) >>> 26) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i6.val >>>6) 51 (26+i)
     have : 26+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 26) (by simp)
     simp[this, (by scalar_tac : 6 + (26 + i)= 32 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq5: ((i6.val >>>6) % 2^ 51) >>> 34 % 2 ^ 8 = (bytes.val[17]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 40
     have : 40+i< 64:= by apply lt_trans this (by simp)
     have := i6_post (40+i) this
     have div8: (40+i) / 8 = 5 := by scalar_tac
     have mod8' : (40 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i6.val >>>6) % 2^ 51) >>> 34) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i6.val >>>6) 51 (34+i)
     have : 34+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 34) (by simp)
     simp[this, (by scalar_tac : 6 + (34 + i)= 40 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq6: ((i6.val >>>6) % 2^ 51) >>> 42 % 2 ^ 8 = (bytes.val[18]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 48
     have : 48+i< 64:= by apply lt_trans this (by simp)
     have := i6_post (48+i) this
     have div8: (48+i) / 8 = 6 := by scalar_tac
     have mod8' : (48 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i6.val >>>6) % 2^ 51) >>> 42) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i6.val >>>6) 51 (42+i)
     have : 42+i< 51:= by apply lt_trans (Nat.add_lt_add_left hi 42) (by simp)
     simp[this, (by scalar_tac : 6 + (42 + i)= 48 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq190: (((i6.val>>> 6) % 2 ^ 51) >>> 50)%2 = (bytes.val[19])%2 := by
     have := Nat.toNat_testBit (((i6.val >>>6) % 2 ^ 51) >>> 50) 0
     have := Nat.toNat_testBit ((bytes.val[19])) 0
     have := i6_post 50 (by simp)
     have := Nat.testBit_mod_two_pow (i6.val >>>6) 51 50
     simp_all
  have eqi6:= powTwo_block_split_51_remain2  (i6.val >>>6)
  have := @powTwo_two_block_split 1 51 (i6.val >>> 6) (by simp)
  rw[eq1, eq2, eq3, eq4, eq5, eq6, ← this] at eqi6
  rw[eq126, eq127] at eqi6
  rw[eq190] at eqi6
  simp at eqi6
  rw[← eqi6]
  clear eq1 eq2 eq3 eq4 eq5 eq6 eq126 eq127 eq190 eqi6 this
  have eq191: ((i9.val >>>1) )% 2^1 = ((bytes.val[19].val)>>>1)%2 := by
     have := Nat.toNat_testBit ((i9.val >>>1) % 2 ^ 1) 0
     have := Nat.toNat_testBit ((bytes.val[19].val)>>>1) 0
     have := i6_post 9 (by simp)
     simp_all
  have eq192: (((i9.val >>>1) % 2 ^51)   >>> 1 )% 2 ^1 = ((bytes.val[19].val)>>>2)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i9.val  >>> 1) 51 1
     simp at mod_pow1
     have := Nat.toNat_testBit (((i9.val >>>1) % 2^51)   >>>1) 0
     have := Nat.toNat_testBit ((bytes.val[19].val)>>>2) 0
     simp_all
  have eq193: (((i9.val >>>1) % 2 ^51)   >>> 2 )% 2 ^1 = ((bytes.val[19].val)>>>3)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i9.val  >>> 1) 51 2
     simp at mod_pow1
     have := Nat.toNat_testBit (((i9.val >>>1) % 2^51)   >>>2) 0
     have := Nat.toNat_testBit ((bytes.val[19].val)>>>3) 0
     simp_all
  have eq194: (((i9.val >>>1) % 2 ^51)   >>> 3 )% 2 ^1 = ((bytes.val[19].val) >>> 4)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i9.val  >>> 1) 51 3
     simp at mod_pow1
     have := Nat.toNat_testBit (((i9.val >>>1) % 2^51)   >>> 3) 0
     have := Nat.toNat_testBit ((bytes.val[19].val) >>> 4) 0
     simp_all
  have eq195: (((i9.val >>>1) % 2 ^51)   >>> 4 )% 2 ^1 = ((bytes.val[19].val) >>> 5)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i9.val  >>> 1) 51 4
     simp at mod_pow1
     have := Nat.toNat_testBit (((i9.val >>>1) % 2^51)   >>> 4) 0
     have := Nat.toNat_testBit ((bytes.val[19].val) >>> 5) 0
     simp_all
  have eq196: (((i9.val >>>1) % 2 ^51)   >>> 5 )% 2 ^1 = ((bytes.val[19].val) >>> 6)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i9.val  >>> 1) 51 5
     simp at mod_pow1
     have := Nat.toNat_testBit (((i9.val >>>1) % 2^51)   >>> 5) 0
     have := Nat.toNat_testBit ((bytes.val[19].val) >>> 6) 0
     simp_all
  have eq197: (((i9.val >>>1) % 2 ^51)   >>> 6 )% 2 ^1 = ((bytes.val[19].val) >>> 7)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i9.val  >>> 1) 51 6
     simp at mod_pow1
     have := Nat.toNat_testBit (((i9.val >>>1) % 2^51)   >>> 6) 0
     have := Nat.toNat_testBit ((bytes.val[19].val) >>> 7) 0
     simp_all
  have eq1: ((i9.val >>>1) % 2^ 51) >>> 7 % 2 ^ 8 = (bytes.val[20]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 8
     have : 8+i< 64:= by apply lt_trans this (by simp)
     have := i9_post (8+i) this
     have div8: (8+i) / 8 = 1 := by scalar_tac
     have mod8' : (8 + i ) % 8 = i % 8 := by simp
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i9.val >>> 1) % 2^ 51) >>> 7) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i9.val >>>1) 51 (7+i)
     have : 7 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 7) (by simp)
     simp[this, (by scalar_tac : 1 + (7 + i)= 8 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq2: ((i9.val >>>1) % 2^ 51) >>> 15 % 2 ^ 8 = (bytes.val[21]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 16
     have : 16 + i< 64:= by apply lt_trans this (by simp)
     have := i9_post (16 + i) this
     have div8: (16 + i) / 8 = 2 := by scalar_tac
     have mod8' : (16 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i9.val >>> 1) % 2^ 51) >>> 15) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i9.val >>>1) 51 (15+i)
     have : 15 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 15) (by simp)
     simp[this, (by scalar_tac : 1 + (15 + i)= 16 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq3: ((i9.val >>>1) % 2^ 51) >>> 23 % 2 ^ 8 = (bytes.val[22]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 24
     have : 24 + i< 64:= by apply lt_trans this (by simp)
     have := i9_post (24 + i) this
     have div8: (24 + i) / 8 = 3 := by scalar_tac
     have mod8' : (24 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i9.val >>> 1) % 2^ 51) >>> 23) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i9.val >>>1) 51 (23 + i)
     have : 23 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 23) (by simp)
     simp[this, (by scalar_tac : 1 + (23 + i)= 24 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq4: ((i9.val >>>1) % 2^ 51) >>> 31 % 2 ^ 8 = (bytes.val[23]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 32
     have : 32 + i< 64:= by apply lt_trans this (by simp)
     have := i9_post (32 + i) this
     have div8: (32 + i) / 8 = 4 := by scalar_tac
     have mod8' : (32 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i9.val >>> 1) % 2 ^ 51) >>> 31) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i9.val >>>1) 51 (31 + i)
     have : 31 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 31) (by simp)
     simp[this, (by scalar_tac : 1 + (31 + i)= 32 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq5: ((i9.val >>>1) % 2^ 51) >>> 39 % 2 ^ 8 = (bytes.val[24]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 40
     have : 40 + i< 64:= by apply lt_trans this (by simp)
     have := i9_post (40 + i) this
     have div8: (40 + i) / 8 = 5 := by scalar_tac
     have mod8' : (40 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i9.val >>> 1) % 2 ^ 51) >>> 39) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i9.val >>>1) 51 (39 + i)
     have : 39 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 39) (by simp)
     simp[this, (by scalar_tac : 1 + (39 + i)= 40 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq250: (((i9.val >>> 1) % 2 ^ 51) >>> 47)%2 = (bytes.val[25])%2 := by
     have := Nat.toNat_testBit (((i9.val >>> 1) % 2 ^ 51) >>> 47) 0
     have := Nat.toNat_testBit ((bytes.val[25])) 0
     have := i9_post 47 (by simp)
     have := Nat.testBit_mod_two_pow (i9.val >>> 1) 51 47
     simp_all
  have eq251: (((i9.val >>> 1) % 2 ^ 51) >>> 47 >>> 1)%2 = ((bytes.val[25].val) >>> 1)%2 := by
     have := Nat.toNat_testBit (((i9.val >>> 1) % 2 ^ 51) >>> 47 >>> 1) 0
     have := Nat.toNat_testBit ((bytes.val[25].val) >>> 1) 0
     have := i9_post 48 (by simp)
     have := Nat.testBit_mod_two_pow (i9.val >>> 1) 51 48
     simp_all
  have eq252: (((i9.val >>> 1) % 2 ^ 51) >>> 47 >>> 2)%2 = ((bytes.val[25].val) >>> 2)%2 := by
     have := Nat.toNat_testBit (((i9.val >>> 1) % 2 ^ 51) >>> 47 >>> 2) 0
     have := Nat.toNat_testBit ((bytes.val[25].val) >>> 2) 0
     have := i9_post 49 (by simp)
     have := Nat.testBit_mod_two_pow (i9.val >>> 1) 51 49
     simp_all
  have eq253: (((i9.val >>> 1) % 2 ^ 51) >>> 47 >>> 3)%2 = ((bytes.val[25].val) >>> 3)%2 := by
     have := Nat.toNat_testBit (((i9.val >>> 1) % 2 ^ 51) >>> 47 >>> 3) 0
     have := Nat.toNat_testBit ((bytes.val[25].val) >>> 3) 0
     have := i9_post 50 (by simp)
     have := Nat.testBit_mod_two_pow (i9.val >>> 1) 51 50
     simp_all
  have eqi9:= powTwo_block_split_51_remain7  (i9.val >>> 1)
  have := @powTwo_seven_block_split 1 51 (i9.val >>> 1) (by simp)
  rw[eq1, eq2, eq3, eq4, eq5, ← this] at eqi9
  rw[eq191, eq192, eq193, eq194, eq195, eq196, eq197] at eqi9
  rw[eq250, eq251, eq252, eq253] at eqi9
  simp at eqi9
  rw[← eqi9]
  clear eq1 eq2 eq3 eq4 eq5 eq191 eq192 eq193 eq194
  clear eq195 eq196 eq197 eq250 eq251 eq252 eq253 eqi9 this
  have eq254: ((i12.val >>> 12) )% 2^1 = ((bytes.val[25].val)>>>4)%2 := by
     have := Nat.toNat_testBit ((i12.val >>> 12) % 2 ^ 1) 0
     have := Nat.toNat_testBit ((bytes.val[25].val)>>>4) 0
     have := i12_post 9 (by simp)
     simp_all
  have eq255: (((i12.val >>> 12) % 2 ^51)   >>> 1 )% 2 ^1 = ((bytes.val[25].val)>>>5)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i12.val  >>> 12) 51 1
     simp at mod_pow1
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2^51)   >>> 1) 0
     have := Nat.toNat_testBit ((bytes.val[25].val)>>>5) 0
     simp_all
  have eq256: (((i12.val >>> 12) % 2 ^51)   >>> 2 )% 2 ^1 = ((bytes.val[25].val)>>> 6)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i12.val  >>> 12) 51 2
     simp at mod_pow1
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2^51)   >>> 2) 0
     have := Nat.toNat_testBit ((bytes.val[25].val)>>> 6) 0
     simp_all
  have eq257: (((i12.val >>> 12) % 2 ^51)   >>> 3 )% 2 ^1 = ((bytes.val[25].val)>>> 7)%2 := by
     have mod_pow1:= Nat.testBit_mod_two_pow (i12.val  >>> 12) 51 3
     simp at mod_pow1
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2^51)   >>> 3) 0
     have := Nat.toNat_testBit ((bytes.val[25].val)>>> 7) 0
     simp_all
  have eq1: ((i12.val >>> 12) % 2^ 51) >>> 4 % 2 ^ 8 = (bytes.val[26]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 16
     have : 16+i< 64:= by apply lt_trans this (by simp)
     have := i12_post (16+i) this
     have div8: (16+i) / 8 = 2 := by scalar_tac
     have mod8' : (16 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i12.val >>> 12) % 2^ 51) >>> 4) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i12.val >>> 12) 51 (4+i)
     have : 4 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 4) (by simp)
     simp[this, (by scalar_tac : 12 + (4 + i)= 16 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq2: ((i12.val >>> 12) % 2^ 51) >>> 12 % 2 ^ 8 = (bytes.val[27]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 24
     have : 24+i< 64:= by apply lt_trans this (by simp)
     have := i12_post (24 + i) this
     have div8: (24+i) / 8 = 3 := by scalar_tac
     have mod8' : (24 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i12.val >>> 12) % 2^ 51) >>> 12) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i12.val >>> 12) 51 (12+i)
     have : 12 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 12) (by simp)
     simp[this, (by scalar_tac : 12 + (12 + i)= 24 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq3: ((i12.val >>> 12) % 2^ 51) >>> 20 % 2 ^ 8 = (bytes.val[28]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 32
     have : 32+i< 64:= by apply lt_trans this (by simp)
     have := i12_post (32 + i) this
     have div8: (32+i) / 8 = 4 := by scalar_tac
     have mod8' : (32 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i12.val >>> 12) % 2^ 51) >>> 20) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i12.val >>> 12) 51 (20+i)
     have : 20 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 20) (by simp)
     simp[this, (by scalar_tac : 12 + (20 + i)= 32 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq4: ((i12.val >>> 12) % 2^ 51) >>> 28 % 2 ^ 8 = (bytes.val[29]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 40
     have : 40+i< 64:= by apply lt_trans this (by simp)
     have := i12_post (40 + i) this
     have div8: (40+i) / 8 = 5 := by scalar_tac
     have mod8' : (40 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i12.val >>> 12) % 2^ 51) >>> 28) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i12.val >>> 12) 51 (28+i)
     have : 28 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 28) (by simp)
     simp[this, (by scalar_tac : 12 + (28 + i)= 40 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq5: ((i12.val >>> 12) % 2^ 51) >>> 36 % 2 ^ 8 = (bytes.val[30]).val := by
   apply eq_of_testBit_eq
   · intro i hi
     have:= Nat.add_lt_add_left hi 48
     have : 48+i< 64:= by apply lt_trans this (by simp)
     have := i12_post (48 + i) this
     have div8: (48+i) / 8 = 6 := by scalar_tac
     have mod8' : (48 + i ) % 8 = i % 8 := by scalar_tac
     have mod8:= Nat.mod_eq_of_lt hi
     simp[div8, mod8, mod8'] at this
     have mod_pow1:= Nat.testBit_mod_two_pow (((i12.val >>> 12) % 2^ 51) >>> 36) 8 i
     simp[hi] at mod_pow1
     have mod_pow2:= Nat.testBit_mod_two_pow (i12.val >>> 12) 51 (36+i)
     have : 36 + i < 51:= by apply lt_trans (Nat.add_lt_add_left hi 36) (by simp)
     simp[this, (by scalar_tac : 12 + (36 + i)= 48 +i)] at mod_pow2
     simp_all
   · apply Nat.mod_lt
     simp
   · scalar_tac
  have eq310: (((i12.val>>> 12) % 2 ^ 51) >>> 44)%2 = (bytes.val[31])%2 := by
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2 ^ 51) >>> 44) 0
     have := Nat.toNat_testBit ((bytes.val[31])) 0
     have := i3_post 44 (by simp)
     have := Nat.testBit_mod_two_pow (i12.val >>> 12) 51 44
     simp_all
  have eq311: (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 1)%2 = ((bytes.val[31].val) >>> 1)%2 := by
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 1) 0
     have := Nat.toNat_testBit ((bytes.val[31].val) >>> 1) 0
     have := i12_post 45 (by simp)
     have := Nat.testBit_mod_two_pow (i12.val >>> 12) 51 45
     simp_all
  have eq312: (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 2)%2 = ((bytes.val[31].val) >>> 2)%2 := by
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 2) 0
     have := Nat.toNat_testBit ((bytes.val[31].val) >>> 2) 0
     have := i12_post 46 (by simp)
     have := Nat.testBit_mod_two_pow (i12.val >>> 12) 51 46
     simp_all
  have eq313: (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 3)%2 = ((bytes.val[31].val) >>> 3)%2 := by
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 3) 0
     have := Nat.toNat_testBit ((bytes.val[31].val) >>> 3) 0
     have := i12_post 47 (by simp)
     have := Nat.testBit_mod_two_pow (i12.val >>> 12) 51 47
     simp_all
  have eq314: (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 4)%2 = ((bytes.val[31].val) >>> 4)%2 := by
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 4) 0
     have := Nat.toNat_testBit ((bytes.val[31].val) >>> 4) 0
     have := i12_post 48 (by simp)
     have := Nat.testBit_mod_two_pow (i12.val >>> 12) 51 48
     simp_all
  have eq315: (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 5)%2 = ((bytes.val[31].val) >>> 5)%2 := by
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 5) 0
     have := Nat.toNat_testBit ((bytes.val[31].val) >>> 5) 0
     have := i12_post 49 (by simp)
     have := Nat.testBit_mod_two_pow (i12.val >>> 12) 51 49
     simp_all
  have eq316: (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 6)%2 = ((bytes.val[31].val) >>> 6)%2 := by
     have := Nat.toNat_testBit (((i12.val >>> 12) % 2 ^ 51) >>> 44 >>> 6) 0
     have := Nat.toNat_testBit ((bytes.val[31].val) >>> 6) 0
     have := i12_post 50 (by simp)
     have := Nat.testBit_mod_two_pow (i12.val >>> 12) 51 50
     simp_all
  have eqi12:= powTwo_block_split_51_remain4  (i12.val >>> 12)
  have := @powTwo_four_block_split 1 51 (i12.val >>> 12) (by simp)
  rw[eq1, eq2, eq3, eq4, eq5, ← this] at eqi12
  rw[eq254, eq255, eq256, eq257] at eqi12
  rw[eq310, eq311, eq312, eq313, eq314, eq315, eq316] at eqi12
  simp at eqi12
  rw[← eqi12]
  clear eq1 eq2 eq3 eq4 eq5 eq254 eq255 eq256 eq257 eq310 eq311 eq312 eq313 eq314 eq315 eq316 eqi12
  simp[add_assoc, mul_add, ← mul_assoc]
  iterate  65 (apply Nat.ModEq.add_left)
  apply Nat.ModEq.rfl

end curve25519_dalek.backend.serial.u64.field.FieldElement51
