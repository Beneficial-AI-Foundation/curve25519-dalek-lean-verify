/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes


/-! # to_bytes

Specification and proof for `FieldElement51::to_bytes`.

Much of the proof and aux lemmas contributed by Son Ho.

This function converts a field element to its canonical 32-byte little-endian representation.
It performs reduction modulo 2^255-19 and encodes the result as bytes.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

set_option linter.style.setOption false
set_option pp.rawOnError true

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

-- TODO: generalize and add to the standard library
@[local simp]
theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  simp only [UScalar.cast, UScalarTy.U64_numBits_eq, UScalarTy.U8_numBits_eq,
    Aeneas.Bvify.U64.UScalar_bv, BitVec.truncate_eq_setWidth]
  simp only [UScalar.val]
  simp only [UScalarTy.U8_numBits_eq, BitVec.toNat_setWidth, UScalar.bv_toNat,
    UScalarTy.U64_numBits_eq, Aeneas.Bvify.U64.UScalar_bv]


/- ## Spec for `to_bytes` -/


/- Byte-by-byte specification for `to_bytes` -/



@[ext] lemma U8.ext {a b : U8} (h : a.bv = b.bv) : a = b := by
  cases a
  cases b
  cases h
  rfl

@[simp] lemma zero_bv : U8.bv 0#u8 = 0 := rfl



lemma masks_spec : 1 <<< 51 % U64.size - 1 = 2 ^ 51 - 1 := by
  scalar_tac




theorem lsb_or_leftShift_eq_lsb {n : ℕ} (a b : ℕ) (hn : n < 3) (ha : a < 2 ^ 51) :
  ((a >>> 48 ||| b <<< 3 % U64.size) % 2 ^ 8) >>> n % 2 = (a >>> 48) >>> n % 2 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 48 % 2 ^ 8) >>> n) ((b <<< 3 % U64.size % 2 ^ 8) >>> n) 1
  rw[(by simp : 2 ^ 1 =2)] at this
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 48) % 256 =(a / 2 ^ 48) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  rw[this]
  have h1 :  b * 2 ^ 3 % 256 / 2 ^ n % 2 = 0 := by
    interval_cases n
    all_goals grind
  rw[h1]
  grind




theorem lsb_or_leftShift_eq_lsbI {n a : ℕ} (b : ℕ) (hn : 3 ≤ n) (ha : a < 2 ^ 51) :
  ((a >>> 48 ||| b <<< 3 % U64.size) % 2 ^ 8) >>> n  = ((b <<< 3) %  2 ^ 8) >>> n  := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 48) % 256 =(a / 2 ^ 48) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  have  :  (a / 2 ^ 48) % 256 / 2 ^ n = a / 2 ^ (48+ n) := by
    rw[this]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h1 :  (a / 2 ^ 48) % 256 / 2 ^ n = 0 := by
    rw[this]
    simp
    apply lt_of_lt_of_le ha
    apply Nat.pow_le_pow_right <;> omega
  rw[h1]
  grind




theorem lsb_or_leftShift_eq_lsbI_45 {n a : ℕ} (b : ℕ) (hn : 6 ≤ n) (ha : a < 2 ^ 51) :
  ((a >>> 45 ||| b <<< 6 % U64.size) % 2 ^ 8) >>> n  = ((b <<< 6) %  2 ^ 8) >>> n  := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 45) % 256 =(a / 2 ^ 45) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  have  :  (a / 2 ^ 45) % 256 / 2 ^ n = a / 2 ^ (45+ n) := by
    rw[this]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h1 :  (a / 2 ^ 45) % 256 / 2 ^ n = 0 := by
    rw[this]
    simp
    apply lt_of_lt_of_le ha
    apply Nat.pow_le_pow_right <;> omega
  rw[h1]
  grind




theorem lsb_or_leftShift_eq_lsbI_50 {n a : ℕ} (b : ℕ) (hn : 1 ≤ n) (ha : a < 2 ^ 51) :
  ((a >>> 50 ||| b <<< 1 % U64.size) % 2 ^ 8) >>> n  = ((b <<< 1) %  2 ^ 8) >>> n  := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 50) % 256 =(a / 2 ^ 50) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  have  :  (a / 2 ^ 50) % 256 / 2 ^ n = a / 2 ^ (50+ n) := by
    rw[this]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h1 :  (a / 2 ^ 50) % 256 / 2 ^ n = 0 := by
    rw[this]
    simp
    apply lt_of_lt_of_le ha
    apply Nat.pow_le_pow_right <;> omega
  rw[h1]
  grind


theorem lsb_or_leftShift_eq_lsbI_47 {n a : ℕ} (b : ℕ) (hn : 4 ≤ n) (ha : a < 2 ^ 51) :
  ((a >>> 47 ||| b <<< 4 % U64.size) % 2 ^ 8) >>> n  = ((b <<< 4) %  2 ^ 8) >>> n  := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 47) % 256 =(a / 2 ^ 47) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  have  :  (a / 2 ^ 47) % 256 / 2 ^ n = a / 2 ^ (47 + n) := by
    rw[this]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h1 :  (a / 2 ^ 47) % 256 / 2 ^ n = 0 := by
    rw[this]
    simp
    apply lt_of_lt_of_le ha
    apply Nat.pow_le_pow_right <;> omega
  rw[h1]
  grind

theorem lsb_or_leftShift_eq_lsb_45 {n : ℕ} (a b : ℕ) (hn : n < 6) (ha : a < 2 ^ 51) :
  ((a >>> 45 ||| b <<< 6 % U64.size) % 2 ^ 8) >>> n % 2 = ((a >>> 45)) >>> n % 2 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 45 % 2 ^ 8) >>> n) ((b <<< 6 % U64.size % 2 ^ 8) >>> n) 1
  rw[(by simp : 2 ^ 1 =2)] at this
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 45) % 256 =(a / 2 ^ 45) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  rw[this]
  have h1 :  b * 2 ^ 6 % 256 / 2 ^ n % 2 = 0 := by
    interval_cases n
    all_goals grind
  rw[h1]
  grind




theorem lsb_or_leftShift_eq_lsb_50 {n : ℕ} (a b : ℕ) (hn : n < 1) (ha : a < 2 ^ 51) :
  ((a >>> 50 ||| b <<< 1 % U64.size) % 2 ^ 8) >>> n % 2 = ((a >>> 50) % 2^ 8) >>> n % 2 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 50 % 2 ^ 8) >>> n) ((b <<< 1 % U64.size % 2 ^ 8) >>> n) 1
  rw[(by simp : 2 ^ 1 =2)] at this
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 50) % 256 =(a / 2 ^ 50) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  rw[this]
  have h1 :  b * 2 ^ 1 % 256 / 2 ^ n % 2 = 0 := by
    interval_cases n
    all_goals grind
  rw[h1]
  grind




theorem lsb_or_leftShift_eq_lsb_47 {n : ℕ} (a b : ℕ) (hn : n < 4) (ha : a < 2 ^ 51) :
  ((a >>> 47 ||| b <<< 4 % U64.size) % 2 ^ 8) >>> n % 2 = (a >>> 47) >>> n % 2 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 47 % 2 ^ 8) >>> n) ((b <<< 4 % U64.size % 2 ^ 8) >>> n) 1
  rw[(by simp : 2 ^ 1 =2)] at this
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : (a / 2 ^ 47) % 256 =(a / 2 ^ 47) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans ha
    simp
  rw[this]
  have h1 :  b * 2 ^ 4 % 256 / 2 ^ n % 2 = 0 := by
    interval_cases n
    all_goals grind
  rw[h1]
  grind


lemma eq_one_lt_two {a : ℕ} (hna : ¬(a =0)) (ha : a < 2) :
    a = 1 :=  by omega


lemma eq_one_or_zero_lt_two {a : ℕ} (ha : a < 2) :
    a = 1 ∨ a = 0 :=  by omega



theorem bitvec_mask_shift_and_zero (a : ℕ) :
    BitVec.ofNat 8 ((a &&& (2^51 - 1)) >>> 44) &&& 128#8 = 0#8 := by
  have h1 : a &&& (2^51 - 1) < 2^51 := by
    apply Nat.and_lt_two_pow
    omega
  have h2 : (a &&& (2^51 - 1)) >>> 44 < 2^7 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    calc a &&& (2^51 - 1) < 2^51 := h1
      _ = 2^44 * 2^7 := by norm_num
  simp only [BitVec.ofNat]
  ext i hi
  interval_cases i
  any_goals simp
  apply Nat.testBit_lt_two_pow
  have h3 : ((a &&& (2^51 - 1)) >>> 44) % 256 = (a &&& (2^51 - 1)) >>> 44 := by
    apply Nat.mod_eq_of_lt
    grind
  rw[(by simp: 2251799813685247 = 2 ^ 51 -1), h3]
  apply h2





/- **Spec for `backend.serial.u64.field.FieldElement51.to_bytes`**:

This function converts a field element to its canonical 32-byte little-endian representation.
The implementation performs reduction modulo p = 2^255-19 to ensure the result is in
canonical form.

The algorithm:
1. Reduces the field element using `reduce` to ensure all limbs are within bounds
2. Performs a final conditional reduction to ensure the result is < p
3. Packs the 5 limbs (each 51 bits) into 32 bytes in little-endian format

Specification:
- The function succeeds (no panic)
- The natural number interpretation of the byte array is congruent to the field element value modulo p
- The byte array represents the unique canonical form (0 ≤ value < p)
-/

set_option maxHeartbeats 10000000000000 in
-- simp_all heavy

@[progress]
theorem to_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    ∃ result, to_bytes self = ok result ∧
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p := by
  unfold to_bytes
  progress*
  · -- BEGIN TASK
    expand fe_post_1 with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5
    suffices h: i14.val ≤ 2 ^ 64-1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
    · have : i15.val= (fe[1]!).val := by simp_all
      rw[this]
      scalar_tac
    · rw[i14_post_1, Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      simp[i13_post, limbs_post, i11_post, i_post]
      suffices h: q4.val ≤ (2 ^ 51 * (2 ^ 64 - 1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
      ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19
      · scalar_tac
      · rw[q4_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[i9_post, i8_post]
        suffices h: q3.val ≤ (2 ^ 51 * (2 ^ 64 - 1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
      ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19 - 2 ^ 51 + (2 ^ 13 - 1) * 19
        · scalar_tac
        · rw[q3_post_1, Nat.shiftRight_eq_div_pow]
          apply Nat.div_le_of_le_mul
          rw[i7_post, i6_post]
          suffices h: q2.val ≤ 2 ^ 51 *
    ((2 ^ 51 * (2 ^ 64 - 1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
      (2 ^ 13 - 1) * 19) -  2 ^ 51 + (2 ^ 13 - 1) * 19
          · scalar_tac
          · rw[q2_post_1, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            rw[i5_post, i4_post]
            suffices h : q1.val ≤ 2 ^ 51 *
            (2 ^ 51 * ((2 ^ 51 * (2 ^ 64 - 1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
            (2 ^ 13 - 1) * 19) - 2 ^ 51 +
            (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19
            · scalar_tac
            · rw[q1_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[i3_post, i2_post]
              suffices h : q.val ≤ 2 ^ 51 *
              (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 64 - 1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
                  (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) -
                  2 ^ 51 + (2 ^ 13 - 1) * 19
              · scalar_tac
              · rw[q_post_1, Nat.shiftRight_eq_div_pow]
                apply Nat.div_le_of_le_mul
                rw[i1_post, i_post]
                scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5
    suffices h: i20.val ≤ 2 ^ 64-1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
    · have : i21.val= (fe[2]!).val := by simp_all
      rw[this]
      scalar_tac
    · rw[i20_post_1, Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      simp[i19_post, limbs2_post, limbs1_post, i16_post]
      suffices h: i14.val ≤ 41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
      · have : i15.val= (fe[1]!).val := by simp_all
        rw[this]
        scalar_tac
      · rw[i14_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        simp[i13_post, limbs_post, i11_post, i_post]
        suffices h: q4.val ≤ (2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
        ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19
        · scalar_tac
        · rw[q4_post_1, Nat.shiftRight_eq_div_pow]
          apply Nat.div_le_of_le_mul
          rw[i9_post, i8_post]
          suffices h: q3.val ≤ (2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
          ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19 - 2 ^ 51 + (2 ^ 13 - 1) * 19
          · scalar_tac
          · rw[q3_post_1, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            rw[i7_post, i6_post]
            suffices h: q2.val ≤ 2 ^ 51 *
            ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
            (2 ^ 13 - 1) * 19) -  2 ^ 51 + (2 ^ 13 - 1) * 19
            · scalar_tac
            · rw[q2_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[i5_post, i4_post]
              suffices h : q1.val ≤ 2 ^ 51 *
              (2 ^ 51 * ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
              (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19
              · scalar_tac
              · rw[q1_post_1, Nat.shiftRight_eq_div_pow]
                apply Nat.div_le_of_le_mul
                rw[i3_post, i2_post]
                suffices h : q.val ≤ 2 ^ 51 *
                (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
                  (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) -
                  2 ^ 51 + (2 ^ 13 - 1) * 19
                · scalar_tac
                · rw[q_post_1, Nat.shiftRight_eq_div_pow]
                  apply Nat.div_le_of_le_mul
                  rw[i1_post, i_post]
                  scalar_tac

    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5
    suffices h: i26.val ≤ 2 ^ 64-1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
    · have : i27.val= (fe[3]!).val := by simp_all
      rw[this]
      scalar_tac
    · rw[i26_post_1, Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      simp[i25_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post, i22_post]
      suffices h: i20.val ≤ 41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
      · have : i21.val= (fe[2]!).val := by simp_all
        rw[this]
        scalar_tac
      · rw[i20_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        simp[i19_post, limbs2_post, limbs1_post, i16_post]
        suffices h: i14.val ≤ 41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
        · have : i15.val= (fe[1]!).val := by simp_all
          rw[this]
          scalar_tac
        · rw[i14_post_1, Nat.shiftRight_eq_div_pow]
          apply Nat.div_le_of_le_mul
          simp[i13_post, limbs_post, i11_post, i_post]
          suffices h: q4.val ≤ (2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
          ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19
          · scalar_tac
          · rw[q4_post_1, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            rw[i9_post, i8_post]
            suffices h: q3.val ≤ (2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
            ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19 - 2 ^ 51 + (2 ^ 13 - 1) * 19
            · scalar_tac
            · rw[q3_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[i7_post, i6_post]
              suffices h: q2.val ≤ 2 ^ 51 *
              ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
              (2 ^ 13 - 1) * 19) -  2 ^ 51 + (2 ^ 13 - 1) * 19
              · scalar_tac
              · rw[q2_post_1, Nat.shiftRight_eq_div_pow]
                apply Nat.div_le_of_le_mul
                rw[i5_post, i4_post]
                suffices h : q1.val ≤ 2 ^ 51 *
                (2 ^ 51 * ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
                (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19
                · scalar_tac
                · rw[q1_post_1, Nat.shiftRight_eq_div_pow]
                  apply Nat.div_le_of_le_mul
                  rw[i3_post, i2_post]
                  suffices h : q.val ≤ 2 ^ 51 *
                  (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
                    (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) -
                    2 ^ 51 + (2 ^ 13 - 1) * 19
                  · scalar_tac
                  · rw[q_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[i1_post, i_post]
                    scalar_tac
    -- END TASK
  · -- BEGIN TASK
    expand fe_post_1 with 5
    suffices h: i32.val ≤ 2 ^ 64-1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
    · have : i33.val= (fe[4]!).val := by simp_all
      rw[this]
      scalar_tac
    · rw[i32_post_1, Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      simp[i31_post, limbs6_post, limbs5_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post, i28_post]
      suffices h: i26.val ≤ 2 ^ 64-1 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
      · have : i27.val= (fe[3]!).val := by simp_all
        rw[this]
        scalar_tac
      · rw[i26_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        simp[i25_post, limbs4_post, limbs3_post, limbs2_post, limbs1_post, i22_post]
        suffices h: i20.val ≤ 41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
        · have : i21.val= (fe[2]!).val := by simp_all
          rw[this]
          scalar_tac
        · rw[i20_post_1, Nat.shiftRight_eq_div_pow]
          apply Nat.div_le_of_le_mul
          simp[i19_post, limbs2_post, limbs1_post, i16_post]
          suffices h: i14.val ≤ 41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)
          · have : i15.val= (fe[1]!).val := by simp_all
            rw[this]
            scalar_tac
          · rw[i14_post_1, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            simp[i13_post, limbs_post, i11_post, i_post]
            suffices h: q4.val ≤ (2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
            ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19
            · scalar_tac
            · rw[q4_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[i9_post, i8_post]
              suffices h: q3.val ≤ (2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) -
              ( 2 ^ 51 + (2 ^ 13 - 1) * 19))/19 - 2 ^ 51 + (2 ^ 13 - 1) * 19
              · scalar_tac
              · rw[q3_post_1, Nat.shiftRight_eq_div_pow]
                apply Nat.div_le_of_le_mul
                rw[i7_post, i6_post]
                suffices h: q2.val ≤ 2 ^ 51 *
                ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
                (2 ^ 13 - 1) * 19) -  2 ^ 51 + (2 ^ 13 - 1) * 19
                · scalar_tac
                · rw[q2_post_1, Nat.shiftRight_eq_div_pow]
                  apply Nat.div_le_of_le_mul
                  rw[i5_post, i4_post]
                  suffices h : q1.val ≤ 2 ^ 51 *
                  (2 ^ 51 * ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
                  (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19
                  · scalar_tac
                  · rw[q1_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[i3_post, i2_post]
                    suffices h : q.val ≤ 2 ^ 51 *
                    (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (41533304265877357663032979985793024 - (2 ^ 51 + (2 ^ 13 - 1) * 19)) - (2 ^ 51 + (2 ^ 13 - 1) * 19)) / 19 - 2 ^ 51 +
                      (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) - 2 ^ 51 + (2 ^ 13 - 1) * 19) -
                      2 ^ 51 + (2 ^ 13 - 1) * 19
                    · scalar_tac
                    · rw[q_post_1, Nat.shiftRight_eq_div_pow]
                      apply Nat.div_le_of_le_mul
                      rw[i1_post, i_post]
                      scalar_tac
    -- END TASK
  · -- BEGIN TASK
    apply U8.ext
    simp[i116_post_2]
    simp_all
    simp[BitVec.setWidth]
    rw[low_51_bit_mask_post_1]
    have := bitvec_mask_shift_and_zero (i34.val)
    simp at this
    clear *- this
    simp[U64.size, U64.numBits, this]
    -- END TASK
  · -- BEGIN TASK
    have limbs7_eq_q4: limbs7.val[4].val >>> 51 = q4.val := by
      by_cases h: q4.val =0
      · -- BEGIN TASK
        simp[h]
        simp_all
        apply (by simp : ∀ a: ℕ, a ≤ 0 → a=0 )
        conv_rhs => rw[←q4_post_1]
        simp[Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_div_right
        simp
        apply Nat.div_le_div_right
        simp
        apply Nat.div_le_div_right
        simp
        apply Nat.div_le_div_right
        simp
        apply Nat.div_le_div_right
        simp
        -- END TASK
      · -- BEGIN TASK
        simp_all
        simp[Nat.shiftRight_eq_div_pow]
        apply (by simp : ∀ a b, a =b → a/ 2^ 51 = b/ 2 ^ 51)
        simp
        apply (by simp : ∀ a b, a =b → a/ 2^ 51 = b/ 2 ^ 51)
        simp
        apply (by simp : ∀ a b, a =b → a/ 2^ 51 = b/ 2 ^ 51)
        simp
        apply (by simp : ∀ a b, a =b → a/ 2^ 51 = b/ 2 ^ 51)
        simp
        apply (by simp : ∀ a b, a =b → a/ 2^ 51 = b/ 2 ^ 51)
        simp
        apply eq_one_lt_two
        · -- BEGIN TASK
          clear *- h
          scalar_tac
          -- END TASK

        · -- BEGIN TASK
          clear *- h fe_post_1
          apply Nat.div_lt_of_lt_mul
          expand fe_post_1 with 5; scalar_tac
          -- END TASK
        -- END TASK
    have q4_lt_2: q4.val < 2 := by
      simp_all
      clear *- fe_post_1
      simp[Nat.shiftRight_eq_div_pow]
      expand fe_post_1 with 5; scalar_tac


    have sum_lt1: i.val  +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val) < 2 * p - 2* 19 - 1  := by
        simp_all
        clear *- fe_post_1 q4_lt_2
        unfold p
        expand fe_post_1 with 5; scalar_tac

    have sum_lt_2p: i.val  +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val) + 19 * q4.val < 2 * p  := by
        clear *- sum_lt1 q4_lt_2
        have := (Nat.mul_lt_mul_left (by simp : 0 < 19)).mpr q4_lt_2
        have := Nat.add_lt_add sum_lt1 this
        apply lt_trans this
        unfold p
        simp

    have sum_eq:
      limbs.val[0].val % 2 ^ 51 +
      2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
      2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51)+
      2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51)+
      2 ^ (4 * 51) * (limbs7.val[4].val % 2 ^ 51)
      + 2 ^ (5 * 51) * (limbs7.val[4].val >>> 51)
      = i.val  +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val) +  19 * q4.val
        := by
      clear *- i11_post i10_post limbs1_post limbs_post i16_post i14_post_1 i13_post i22_post i20_post_1 i19_post limbs3_post limbs2_post limbs7_post  limbs6_post i34_post i32_post_1 i31_post limbs5_post limbs4_post i28_post i26_post_1 i25_post
      calc
       limbs.val[0].val % 2 ^ 51 +
        2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51) +
        2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51) +
        2 ^ (4 * 51) * (limbs7.val[4].val % 2 ^ 51) +
        2 ^ (5 * 51) * (limbs7.val[4].val >>> 51)
        = limbs.val[0].val % 2 ^ 51 +
        2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51) +
        2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51) +
        2 ^ (4 * 51) * (limbs7.val[4].val % 2 ^ 51 +
        2 ^ 51 * (limbs7.val[4].val >>> 51) ) := by
           grind
       _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51) +
        2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51) +
        2 ^ (4 * 51) * (limbs7.val[4].val)
        := by
          simp
          rw[Nat.shiftRight_eq_div_pow]
          apply   Nat.mod_add_div

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51) +
        2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51) +
        2 ^ (4 * 51) * (i33.val + limbs5.val[3].val >>> 51)
        := by
          simp[limbs7_post, limbs6_post, i34_post, i32_post_1, i31_post]

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51) +
        2 ^ (3 * 51) * ((limbs5.val[3].val % 2 ^ 51) +
        2 ^ 51 * (limbs5.val[3].val >>> 51) ) +
        2 ^ (4 * 51) * (i33.val)
        := by grind

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51) +
        2 ^ (3 * 51) * (limbs5.val[3].val) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp
          rw[Nat.shiftRight_eq_div_pow]
          apply   Nat.mod_add_div

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51) +
        2 ^ (3 * 51) * (i27.val + limbs3.val[2].val >>> 51) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp[limbs5_post, limbs4_post, i28_post, i26_post_1, i25_post]


        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * ((limbs3.val[2].val % 2 ^ 51) +
        2 ^ 51 * limbs3.val[2].val >>> 51
        ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by grind

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (limbs3.val[2].val) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp
          rw[Nat.shiftRight_eq_div_pow]
          apply   Nat.mod_add_div

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
        2 ^ (2 * 51) * (i21.val + limbs1.val[1].val >>> 51) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp[limbs3_post, limbs2_post, i22_post, i20_post_1, i19_post]

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val % 2 ^ 51 + 2 ^ 51 * limbs1.val[1].val >>> 51) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by grind

        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (limbs1.val[1].val ) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp
          rw[Nat.shiftRight_eq_div_pow]
          apply   Nat.mod_add_div


        _ =  limbs.val[0].val % 2 ^ 51 +
          2 ^ 51 * (i15.val +limbs.val[0].val >>> 51 ) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp[limbs1_post, i16_post, i14_post_1, i13_post]

        _ =  limbs.val[0].val % 2 ^ 51 + 2^ 51 * (limbs.val[0].val >>> 51) +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by grind

        _ =  limbs.val[0].val +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp
          rw[Nat.shiftRight_eq_div_pow]
          apply   Nat.mod_add_div

        _ =  i.val +  19 * q4.val +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        := by
          simp[limbs_post, i11_post, i10_post]

        _ =  i.val  +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val) +  19 * q4.val
        := by
          grind

    rw[← sum_eq] at sum_lt_2p

    have lt_p: limbs.val[0].val % 2 ^ 51 +
      2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
      2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51)+
      2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51)+
      2 ^ (4 * 51) * (limbs7.val[4].val % 2 ^ 51) < p := by
      have h:= eq_one_or_zero_lt_two q4_lt_2
      rcases h with h | h
      · -- BEGIN TASK
        rw[limbs7_eq_q4, h] at sum_lt_2p
        clear *- sum_lt_2p
        unfold p
        unfold p at sum_lt_2p
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        have : (limbs7.val)[4].val < 2 ^ 51 := by
         simp_all
         rw[Nat.shiftRight_eq_div_pow] at q4_post_1
         simp at q4_post_1
         scalar_tac
        have : (limbs7.val)[4].val < 2 ^ 51 -1
         ∨ (limbs7.val)[4].val= 2 ^ 51 -1 := by grind
        rcases this with h | h
        · -- BEGIN TASK
          clear *- h
          have := Nat.mod_lt (limbs.val)[0] (by simp : 0 < 2 ^ 51)
          have := Nat.mod_lt (limbs1.val)[1] (by simp : 0 < 2 ^ 51)
          have := Nat.mod_lt (limbs3.val)[2] (by simp : 0 < 2 ^ 51)
          have := Nat.mod_lt (limbs5.val)[3] (by simp : 0 < 2 ^ 51)
          unfold p
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          have : (fe.val)[4].val+ limbs5.val[3].val >>>51  = (limbs7.val)[4].val := by
            clear h
            simp_all
          have : (fe.val)[4].val  ≤  2 ^51 - 1 := by grind
          have h1: (fe.val)[4].val  <  2 ^51 - 1 ∨ (fe.val)[4].val  =  2 ^51 - 1 := by grind
          rcases h1 with h1 | h1
          · -- BEGIN TASK
            simp_all
            clear *- h1 fe_post_1
            unfold p
            expand fe_post_1 with 5; scalar_tac
            -- END TASK
          · -- BEGIN TASK
            have : limbs5.val[3].val >>>51 = 0:= by grind
            simp[Nat.shiftRight_eq_div_pow] at this
            have : (limbs5.val)[3].val < 2 ^ 51 -1
              ∨ (limbs5.val)[3].val= 2 ^ 51 -1 := by grind
            rcases this with h | h
            · -- BEGIN TASK
              clear *- h
              have := Nat.mod_lt (limbs.val)[0] (by simp : 0 < 2 ^ 51)
              have := Nat.mod_lt (limbs1.val)[1] (by simp : 0 < 2 ^ 51)
              have := Nat.mod_lt (limbs3.val)[2] (by simp : 0 < 2 ^ 51)
              unfold p
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              have : (fe.val)[3].val+ limbs3.val[2].val >>>51  = (limbs5.val)[3].val := by
                clear h
                simp_all
              have : (fe.val)[3].val  ≤  2 ^51 - 1 := by grind
              have h1: (fe.val)[3].val  <  2 ^51 - 1 ∨ (fe.val)[3].val  =  2 ^51 - 1 := by grind
              rcases h1 with h1 | h1
              · -- BEGIN TASK
                simp_all
                clear *- h1 fe_post_1
                unfold p
                expand fe_post_1 with 5; scalar_tac
                -- END TASK
              · -- BEGIN TASK
                have : limbs3.val[2].val >>>51 = 0:= by grind
                simp[Nat.shiftRight_eq_div_pow] at this
                have : (limbs3.val)[2].val < 2 ^ 51 -1
                  ∨ (limbs3.val)[2].val= 2 ^ 51 -1 := by grind
                rcases this with h | h
                · -- BEGIN TASK
                  clear *- h
                  have := Nat.mod_lt (limbs.val)[0] (by simp : 0 < 2 ^ 51)
                  have := Nat.mod_lt (limbs1.val)[1] (by simp : 0 < 2 ^ 51)
                  unfold p
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                  have : (fe.val)[2].val+ limbs1.val[1].val >>>51  = (limbs3.val)[2].val := by
                    clear h
                    simp_all
                  have : (fe.val)[2].val  ≤  2 ^51 - 1 := by grind
                  have h1: (fe.val)[2].val  <  2 ^51 - 1 ∨ (fe.val)[2].val  =  2 ^51 - 1 := by grind
                  rcases h1 with h1 | h1
                  · -- BEGIN TASK
                    simp_all
                    clear *- h1 fe_post_1
                    unfold p
                    expand fe_post_1 with 5; scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    have : limbs1.val[1].val >>>51 = 0:= by grind
                    simp[Nat.shiftRight_eq_div_pow] at this
                    have : (limbs1.val)[1].val < 2 ^ 51 -1
                      ∨ (limbs1.val)[1].val= 2 ^ 51 -1 := by grind
                    rcases this with h | h
                    · -- BEGIN TASK
                      clear *- h
                      have := Nat.mod_lt (limbs.val)[0] (by simp : 0 < 2 ^ 51)
                      unfold p
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                      have : (fe.val)[1].val+ limbs.val[0].val >>>51  = (limbs1.val)[1].val := by
                        clear h
                        simp_all
                      have : (fe.val)[1].val  ≤  2 ^51 - 1 := by grind
                      have h1: (fe.val)[1].val  <  2 ^51 - 1 ∨ (fe.val)[1].val  =  2 ^51 - 1 := by grind
                      rcases h1 with h1 | h1
                      · -- BEGIN TASK
                        simp_all
                        clear *- h1 fe_post_1
                        unfold p
                        expand fe_post_1 with 5; scalar_tac
                        -- END TASK
                      · have : limbs.val[0].val >>>51 = 0:= by grind
                        simp[Nat.shiftRight_eq_div_pow] at this
                        simp_all
                        clear *- this q4_post_1
                        have := Nat.mod_eq_of_lt this
                        rw[this]
                        have h1: (fe.val)[0].val  <  2 ^51 - 19 ∨ 2 ^51 - 19 ≤ (fe.val)[0].val      := by grind
                        rcases h1 with h1 | h1
                        · -- BEGIN TASK
                          unfold p
                          scalar_tac
                          -- END TASK
                        · scalar_tac
                       -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK
      -- END TASK


















    have eq_mod_p_1:
      limbs.val[0].val % 2 ^ 51 +
      2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
      2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51)+
      2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51)+
      2 ^ (4 * 51) * (limbs7.val[4].val % 2 ^ 51)
      ≡ i.val +
        2 ^ 51 * (i15.val) +
        2 ^ (2 * 51) * (i21.val ) +
        2 ^ (3 * 51) * (i27.val ) +
        2 ^ (4 * 51) * (i33.val)
        [MOD p]  := by
        apply Nat.ModEq.add_right_cancel' (2 ^ (5 * 51) * (limbs7.val[4].val >>> 51))
        rw[sum_eq, limbs7_eq_q4]
        apply Nat.ModEq.add_left
        apply Nat.ModEq.mul_right
        unfold p
        rw [Nat.ModEq]
        norm_num

    have : U8x32_as_Nat s32 =
      limbs.val[0].val % 2 ^ 51 +
      2 ^ 51 * (limbs1.val[1].val % 2 ^ 51) +
      2 ^ (2 * 51) * (limbs3.val[2].val % 2 ^ 51)+
      2 ^ (3 * 51) * (limbs5.val[3].val % 2 ^ 51)+
      2 ^ (4 * 51) * (limbs7.val[4].val % 2 ^ 51) := by

        simp[U8x32_as_Nat, Finset.sum_range_succ]

        have eq0: s32.val[0].val= limbs.val[0].val >>> 0 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i40_post, i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]
        rw[eq0]
        clear eq0

        have eq1: s32.val[1].val= (limbs.val[0].val % 2 ^ 51) >>> 8 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i42_post, i41_post_1, i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]

        rw[eq1]
        clear eq1

        have eq2: s32.val[2].val= (limbs.val[0].val % 2 ^ 51) >>> 16 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i44_post, i43_post_1, i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]

        rw[eq2]
        clear eq2



        have eq3: s32.val[3].val= (limbs.val[0].val % 2 ^ 51) >>> 24 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i46_post, i45_post_1, i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]

        rw[eq3]
        clear eq3
        have eq4: s32.val[4].val= (limbs.val[0].val % 2 ^ 51) >>> 32 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i48_post, i47_post_1, i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]

        rw[eq4]
        clear eq4


        have eq5: s32.val[5].val= (limbs.val[0].val % 2 ^ 51) >>> 40 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i50_post, i49_post_1, i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]

        rw[eq5]
        clear eq5


        have : i39.val < 2 ^51 := by
          simp[i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          apply Nat.mod_lt
          simp

        have eq6_0:= @lsb_or_leftShift_eq_lsb 0 (i39.val) (i52.val) (by simp) this


        have eq60: s32.val[6].val % 2 = (limbs.val[0].val % 2 ^ 51) >>> 48 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_0
          rw[eq6_0]
          simp[i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]



        have eq6_1:= @lsb_or_leftShift_eq_lsb 1 (i39.val) (i52.val) (by simp) this


        have eq61: s32.val[6].val >>> 1 % 2 = ((limbs.val[0].val % 2 ^ 51) >>> 48 ) >>>1 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_1
          rw[eq6_1]
          simp[i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]





        have eq6_2:= @lsb_or_leftShift_eq_lsb 2 (i39.val) (i52.val) (by simp) this


        have eq62: s32.val[6].val >>> 2 % 2 = ((limbs.val[0].val % 2 ^ 51) >>> 48) >>>2 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_2
          rw[eq6_2]
          simp[i39_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[limbs3_post, limbs2_post, limbs1_post, limbs_post,]
          simp[i18_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i17_post, limbs1_post, limbs_post]






        have eq6_3:= lsb_or_leftShift_eq_lsbI (i52.val) (by simp : 3 ≤ 3) this
        have eq6_4:= lsb_or_leftShift_eq_lsbI (i52.val) (by simp : 3 ≤ 4) this
        have eq6_5:= lsb_or_leftShift_eq_lsbI (i52.val) (by simp : 3 ≤ 5) this
        have eq6_6:= lsb_or_leftShift_eq_lsbI (i52.val) (by simp : 3 ≤ 6) this
        have eq6_7:= lsb_or_leftShift_eq_lsbI (i52.val) (by simp : 3 ≤ 7) this





        have eq63: s32.val[6].val >>> 3 % 2 = (limbs1.val[1].val % 2 ^ 51) % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_3
          rw[eq6_3]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]
          clear *-
          scalar_tac



        have eq64: s32.val[6].val >>> 4 % 2 = (limbs1.val[1].val % 2 ^ 51) >>> 1 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_4
          rw[eq6_4]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]
          clear *-
          scalar_tac


        have eq65: s32.val[6].val >>> 5 % 2 = (limbs1.val[1].val % 2 ^ 51) >>> 2 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_5
          rw[eq6_5]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]
          clear *-
          scalar_tac

        have eq66: s32.val[6].val >>> 6 % 2 = (limbs1.val[1].val % 2 ^ 51) >>> 3 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_6
          rw[eq6_6]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]
          clear *-
          scalar_tac


        have eq67: s32.val[6].val >>> 7 % 2 = (limbs1.val[1].val % 2 ^ 51) >>> 4 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i55_post, i54_post_1, i51_post_1, i53_post_1]
          simp at eq6_7
          rw[eq6_7]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]
          clear *-
          scalar_tac

        have eqi6:= powTwo_8_block_split (s32.val[6].val ) (by simp : 8 * 1 < 51)
        have s6_lt: s32.val[6].val < 2 ^ 8 := by
          clear *-
          scalar_tac

        have eq6_mod8:= Nat.mod_eq_of_lt s6_lt
        have :  s32.val[6].val < 2 ^ 51 := by
          apply lt_trans s6_lt
          simp
        have eq6_mod51:= Nat.mod_eq_of_lt this


        rw[eq6_mod51, eq6_mod8,
        (by simp : 2 ^ 1 = 2), eq60,
        (by simp : ∀ (a :ℕ), a * 1  = a), eq61, eq62, eq63, eq64, eq65, eq66, eq67] at eqi6
        rw[← eqi6]
        clear eqi6 eq6_mod51 this eq6_mod8 s6_lt eq67 eq66 eq65 eq64 eq63 eq62 eq61 eq60
        clear eq6_7 eq6_6 eq6_5 eq6_4 eq6_3 eq6_2 eq6_1 eq6_0 this



        have eq7: s32.val[7].val = (limbs1.val[1].val % 2 ^ 51) >>> 5 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[s8_post, s7_post, s6_post, s5_post, s4_post,
          s3_post, s2_post, s1_post ]
          simp[i57_post, i56_post_1]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        rw[eq7]
        clear eq7



        have eq8: s32.val[8].val = (limbs1.val[1].val % 2 ^ 51) >>> 13 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i59_post, i58_post_1]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        rw[eq8]
        clear eq8


        have eq9: s32.val[9].val = (limbs1.val[1].val % 2 ^ 51) >>> 21 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i61_post, i60_post_1]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        rw[eq9]
        clear eq9




        have eq10: s32.val[10].val = (limbs1.val[1].val % 2 ^ 51) >>> 29 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i63_post, i62_post_1]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        rw[eq10]
        clear eq10


        have eq11: s32.val[11].val = (limbs1.val[1].val % 2 ^ 51) >>> 37 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i65_post, i64_post_1]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        rw[eq11]
        clear eq11


        have : i52.val < 2 ^51 := by
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          apply Nat.mod_lt
          simp

        have eq12_0:= @lsb_or_leftShift_eq_lsb_45 0 (i52.val) (i67.val) (by simp) this

        have eq120: s32.val[12].val % 2 = (limbs1.val[1].val % 2 ^ 51) >>> 45 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_0
          rw[eq12_0]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]




        have eq12_1:= @lsb_or_leftShift_eq_lsb_45 1 (i52.val) (i67.val) (by simp) this


        have eq121: s32.val[12].val >>> 1 % 2 = ((limbs1.val[1].val % 2 ^ 51) >>> 45) >>>1 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_1
          rw[eq12_1]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        have eq12_2:= @lsb_or_leftShift_eq_lsb_45 2 (i52.val) (i67.val) (by simp) this


        have eq122: s32.val[12].val >>> 2 % 2 = ((limbs1.val[1].val % 2 ^ 51) >>> 45) >>> 2 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_2
          rw[eq12_2]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        have eq12_3:= @lsb_or_leftShift_eq_lsb_45 3 (i52.val) (i67.val) (by simp) this


        have eq123: s32.val[12].val >>> 3 % 2 = ((limbs1.val[1].val % 2 ^ 51) >>> 45) >>> 3 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_3
          rw[eq12_3]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        have eq12_4:= @lsb_or_leftShift_eq_lsb_45 4 (i52.val) (i67.val) (by simp) this


        have eq124: s32.val[12].val >>> 4 % 2 = ((limbs1.val[1].val % 2 ^ 51) >>> 45) >>> 4 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_4
          rw[eq12_4]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]

        have eq12_5:= @lsb_or_leftShift_eq_lsb_45 5 (i52.val) (i67.val) (by simp) this


        have eq125: s32.val[12].val >>> 5 % 2 = ((limbs1.val[1].val % 2 ^ 51) >>> 45) >>> 5 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_5
          rw[eq12_5]
          simp[i52_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i24_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i23_post, limbs3_post, limbs2_post]
        have eq12_6:= lsb_or_leftShift_eq_lsbI_45 (i67.val) (by simp : 6 ≤ 6) this
        have eq12_7:= lsb_or_leftShift_eq_lsbI_45 (i67.val) (by simp : 6 ≤ 7) this
        have eq126: s32.val[12].val >>> 6 % 2 = (limbs3.val[2].val % 2 ^ 51) % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_6
          rw[eq12_6]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]
          clear *-
          scalar_tac
        have eq127: s32.val[12].val >>> 7 % 2 = (limbs3.val[2].val % 2 ^ 51) >>> 1 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i70_post, i69_post_1, i66_post_1, i68_post_1]
          simp at eq12_7
          rw[eq12_7]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]
          clear *-
          scalar_tac
        have eqi12:= powTwo_8_block_split (s32.val[12].val ) (by simp : 8 * 1 < 51)
        have s12_lt: s32.val[12].val < 2 ^ 8 := by
          clear *-
          scalar_tac
        have eq12_mod8:= Nat.mod_eq_of_lt s12_lt
        have :  s32.val[12].val < 2 ^ 51 := by
          apply lt_trans s12_lt
          simp
        have eq12_mod51:= Nat.mod_eq_of_lt this
        rw[eq12_mod51, eq12_mod8,
        (by simp : 2 ^ 1 = 2), eq120,
        (by simp : ∀ (a :ℕ), a * 1  = a), eq121, eq122, eq123, eq124, eq125, eq126, eq127] at eqi12
        rw[← eqi12]
        clear eq12_mod51 this eq12_mod8 s12_lt eqi12 eq127 eq126
        clear eq12_7 eq12_6 eq125 eq12_5 eq124 eq12_4 eq123 eq12_3
        clear eq122 eq12_2 eq121 eq12_1 eq120 eq12_0 this

        have eq13: s32.val[13].val = (limbs3.val[2].val % 2 ^ 51) >>> 2 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i72_post, i71_post_1]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]
        rw[eq13]
        clear eq13
        have eq14: s32.val[14].val = (limbs3.val[2].val % 2 ^ 51) >>> 10 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i74_post, i73_post_1]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]

        rw[eq14]
        clear eq14


        have eq15: s32.val[15].val = (limbs3.val[2].val % 2 ^ 51) >>> 18 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i76_post, i75_post_1]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]

        rw[eq15]
        clear eq15

        have eq16: s32.val[16].val = (limbs3.val[2].val % 2 ^ 51) >>> 26 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i78_post, i77_post_1]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]
        rw[eq16]
        clear eq16
        have eq17: s32.val[17].val = (limbs3.val[2].val % 2 ^ 51) >>> 34 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[s18_post, s17_post, s16_post, s15_post, s14_post,
          s13_post, s12_post, s11_post, s10_post, s9_post]
          simp[i80_post, i79_post_1]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]
        rw[eq17]
        clear eq17
        have eq18: s32.val[18].val = (limbs3.val[2].val % 2 ^ 51) >>> 42 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i82_post, i81_post_1]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]
        rw[eq18]
        clear eq18
        have eqi19:= powTwo_8_block_split (s32.val[19].val ) (by simp : 8 * 1 < 51)
        have s19_lt: s32.val[19].val < 2 ^ 8 := by
          clear *-
          scalar_tac
        have eq19_mod8:= Nat.mod_eq_of_lt s19_lt
        have :  s32.val[19].val < 2 ^ 51 := by
          apply lt_trans s19_lt
          simp
        have eq19_mod51:= Nat.mod_eq_of_lt this
        rw[eq19_mod51, eq19_mod8,
        (by simp : 2 ^ 1 = 2),
        (by simp : ∀ (a :ℕ), a * 1  = a)] at eqi19
        clear eq19_mod51 this eq19_mod8 s19_lt

        have i67_lt: i67.val < 2 ^51 := by
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          apply Nat.mod_lt
          simp


        have eq19_0:= @lsb_or_leftShift_eq_lsb_50 0 (i67.val) (i84.val) (by simp) i67_lt


        have eq190: s32.val[19].val % 2 = (limbs3.val[2].val % 2 ^ 51) >>> 50 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_0
          rw[eq19_0]
          simp[i67_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post]
          simp[i30_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i29_post, limbs5_post, limbs4_post]

        rw[eq190] at  eqi19
        clear eq190 eq19_0





        have eq19_1:= lsb_or_leftShift_eq_lsbI_50 (i84.val) (by simp : 1 ≤ 1) i67_lt

        have eq191: s32.val[19].val >>> 1 % 2 = (limbs5.val[3].val % 2 ^ 51) % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_1
          rw[eq19_1]
          simp[i84_post, limbs9_post, limbs8_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]
          clear *-
          scalar_tac

        rw[eq191] at  eqi19
        clear eq191 eq19_1


        have eq19_2:= lsb_or_leftShift_eq_lsbI_50 (i84.val) (by simp : 1 ≤ 2) i67_lt

        have eq192: s32.val[19].val >>> 2 % 2 = (limbs5.val[3].val % 2 ^ 51) >>> 1 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_2
          rw[eq19_2]
          simp[i84_post, limbs9_post, limbs8_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]
          clear *-
          scalar_tac

        rw[eq192] at  eqi19
        clear eq192 eq19_2

        have eq19_3:= lsb_or_leftShift_eq_lsbI_50 (i84.val) (by simp : 1 ≤ 3) i67_lt

        have eq193: s32.val[19].val >>> 3 % 2 = (limbs5.val[3].val % 2 ^ 51) >>> 2 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_3
          rw[eq19_3]
          simp[i84_post, limbs9_post, limbs8_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]
          clear *-
          scalar_tac

        rw[eq193] at  eqi19
        clear eq193 eq19_3

        have eq19_4:= lsb_or_leftShift_eq_lsbI_50 (i84.val) (by simp : 1 ≤ 4) i67_lt

        have eq194: s32.val[19].val >>> 4 % 2 = (limbs5.val[3].val % 2 ^ 51) >>> 3 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_4
          rw[eq19_4]
          simp[i84_post, limbs9_post, limbs8_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]
          clear *-
          scalar_tac

        rw[eq194] at  eqi19
        clear eq194 eq19_4


        have eq19_5:= lsb_or_leftShift_eq_lsbI_50 (i84.val) (by simp : 1 ≤ 5) i67_lt
        have eq195: s32.val[19].val >>> 5 % 2 = (limbs5.val[3].val % 2 ^ 51) >>> 4 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_5
          rw[eq19_5]
          simp[i84_post, limbs9_post, limbs8_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]
          clear *-
          scalar_tac

        rw[eq195] at  eqi19
        clear eq195 eq19_5


        have eq19_6:= lsb_or_leftShift_eq_lsbI_50 (i84.val) (by simp : 1 ≤ 6) i67_lt
        have eq196: s32.val[19].val >>> 6 % 2 = (limbs5.val[3].val % 2 ^ 51) >>> 5 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_6
          rw[eq19_6]
          simp[i84_post, limbs9_post, limbs8_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]
          clear *-
          scalar_tac

        rw[eq196] at  eqi19
        clear eq196 eq19_6


        have eq19_7:= lsb_or_leftShift_eq_lsbI_50 (i84.val) (by simp : 1 ≤ 7) i67_lt
        have eq197: s32.val[19].val >>> 7 % 2 = (limbs5.val[3].val % 2 ^ 51) >>> 6 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i87_post, i86_post_1, i83_post_1, i85_post_1]
          simp at eq19_7
          rw[eq19_7]
          simp[i84_post, limbs9_post, limbs8_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]
          clear *-
          scalar_tac

        rw[eq197] at  eqi19
        clear eq197 eq19_7

        rw[← eqi19]
        clear eqi19 i67_lt

        have eq20: s32.val[20].val = (limbs5.val[3].val % 2 ^ 51) >>> 7 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i89_post, i88_post_1]
          simp[i84_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]


        rw[eq20]
        clear eq20

        have eq21: s32.val[21].val = (limbs5.val[3].val % 2 ^ 51) >>> 15 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i91_post, i90_post_1]
          simp[i84_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq21]
        clear eq21


        have eq22: s32.val[22].val = (limbs5.val[3].val % 2 ^ 51) >>> 23 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[s23_post, s22_post, s21_post, s20_post, s19_post]
          simp[i93_post, i92_post_1]
          simp[i84_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq22]
        clear eq22

        have eq23: s32.val[23].val = (limbs5.val[3].val % 2 ^ 51) >>> 31 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i95_post, i94_post_1]
          simp[i84_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq23]
        clear eq23

        have eq24: s32.val[24].val = (limbs5.val[3].val % 2 ^ 51) >>> 39 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i97_post, i96_post_1]
          simp[i84_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq24]
        clear eq24

        have eqi25:= powTwo_8_block_split (s32.val[25].val ) (by simp : 8 * 1 < 51)
        have s25_lt: s32.val[25].val < 2 ^ 8 := by
          clear *-
          scalar_tac

        have eq25_mod8:= Nat.mod_eq_of_lt s25_lt
        have :  s32.val[25].val < 2 ^ 51 := by
          apply lt_trans s25_lt
          simp
        have eq25_mod51:= Nat.mod_eq_of_lt this


        rw[eq25_mod51, eq25_mod8,
        (by simp : 2 ^ 1 = 2),
        (by simp : ∀ (a :ℕ), a * 1  = a)] at eqi25
        clear eq25_mod51 this eq25_mod8 s25_lt

        have i84_lt: i84.val < 2 ^51 := by
          simp[i84_post, limbs9_post, limbs8_post,
          limbs7_post, limbs6_post, limbs5_post, limbs4_post]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          apply Nat.mod_lt
          simp


        have eq25_0:= @lsb_or_leftShift_eq_lsb_47 0 (i84.val) (i99.val) (by simp) i84_lt


        have eq250: s32.val[25].val % 2 = (limbs5.val[3].val % 2 ^ 51) >>> 47 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_0
          rw[eq25_0]
          simp[i84_post, limbs9_post, limbs8_post,]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq250] at  eqi25
        clear eq250 eq25_0

        have eq25_1:= @lsb_or_leftShift_eq_lsb_47 1 (i84.val) (i99.val) (by simp) i84_lt


        have eq251: s32.val[25].val >>> 1 % 2 = ((limbs5.val[3].val % 2 ^ 51) >>> 47) >>> 1 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_1
          rw[eq25_1]
          simp[i84_post, limbs9_post, limbs8_post,]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq251] at  eqi25
        clear eq251 eq25_1


        have eq25_2:= @lsb_or_leftShift_eq_lsb_47 2 (i84.val) (i99.val) (by simp) i84_lt


        have eq252: s32.val[25].val >>> 2 % 2 = ((limbs5.val[3].val % 2 ^ 51) >>> 47) >>> 2 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_2
          rw[eq25_2]
          simp[i84_post, limbs9_post, limbs8_post,]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq252] at  eqi25
        clear eq252 eq25_2


        have eq25_3:= @lsb_or_leftShift_eq_lsb_47 3 (i84.val) (i99.val) (by simp) i84_lt


        have eq253: s32.val[25].val >>> 3 % 2 = ((limbs5.val[3].val % 2 ^ 51) >>> 47) >>> 3 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_3
          rw[eq25_3]
          simp[i84_post, limbs9_post, limbs8_post,]
          simp[i36_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i35_post, limbs7_post, limbs6_post]

        rw[eq253] at  eqi25
        clear eq253 eq25_3



        have eq25_4:= lsb_or_leftShift_eq_lsbI_47 (i99.val) (by simp : 4 ≤ 4) i84_lt

        have eq254: s32.val[25].val >>> 4 % 2 = (limbs7.val[4].val % 2 ^ 51) % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_4
          rw[eq25_4]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]
          clear  *-
          scalar_tac

        rw[eq254] at  eqi25
        clear eq254 eq25_4


        have eq25_5:= lsb_or_leftShift_eq_lsbI_47 (i99.val) (by simp : 4 ≤ 5) i84_lt

        have eq255: s32.val[25].val >>> 5 % 2 = (limbs7.val[4].val % 2 ^ 51) >>> 1 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_5
          rw[eq25_5]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]
          clear  *-
          scalar_tac

        rw[eq255] at  eqi25
        clear eq255 eq25_5

        have eq25_6:= lsb_or_leftShift_eq_lsbI_47 (i99.val) (by simp : 4 ≤ 6) i84_lt

        have eq256: s32.val[25].val >>> 6 % 2 = (limbs7.val[4].val % 2 ^ 51) >>> 2 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_6
          rw[eq25_6]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]
          clear  *- i_post
          scalar_tac

        rw[eq256] at  eqi25
        clear eq256 eq25_6


        have eq25_7:= lsb_or_leftShift_eq_lsbI_47 (i99.val) (by simp : 4 ≤ 7) i84_lt

        have eq257: s32.val[25].val >>> 7 % 2 = (limbs7.val[4].val % 2 ^ 51) >>> 3 % 2 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i102_post, i101_post_1, i98_post_1, i100_post_1]
          simp at eq25_7
          rw[eq25_7]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]
          clear  * - i_post
          scalar_tac

        rw[eq257] at  eqi25
        clear eq257 eq25_7

        rw[← eqi25]
        clear eqi25 i84_lt

        have eq26: s32.val[26].val = (limbs7.val[4].val % 2 ^ 51) >>> 4 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i104_post, i103_post_1]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]

        rw[eq26]
        clear eq26


        have eq27: s32.val[27].val = (limbs7.val[4].val % 2 ^ 51) >>> 12 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i106_post, i105_post_1]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]

        rw[eq27]
        clear eq27


        have eq28: s32.val[28].val = (limbs7.val[4].val % 2 ^ 51) >>> 20 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i108_post, i107_post_1]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]

        rw[eq28]
        clear eq28

        have eq29: s32.val[29].val = (limbs7.val[4].val % 2 ^ 51) >>> 28 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i110_post, i109_post_1]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]

        rw[eq29]
        clear eq29


        have eq30: s32.val[30].val = (limbs7.val[4].val % 2 ^ 51) >>> 36 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i112_post, i111_post_1]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]


        rw[eq30]
        clear eq30

        have eq31: s32.val[31].val = (limbs7.val[4].val % 2 ^ 51) >>> 44 % 2^8 := by
          simp[s32_post, s31_post, s30_post, s29_post, s28_post,
          s27_post, s26_post, s25_post,  s24_post,]
          simp[i114_post, i113_post_1]
          simp[i99_post, limbs9_post, limbs8_post]
          simp[i38_post_1]
          rw[low_51_bit_mask_post_1, i12_post_1, masks_spec,
          land_pow_two_sub_one_eq_mod]
          simp[i37_post, limbs8_post]

        rw[eq31]
        clear eq31



        have hlimbs0:= powTwo_block_split_51 limbs.val[0].val
        simp at hlimbs0
        conv_rhs => rw[← hlimbs0]
        clear hlimbs0

        have hlimbs1:= powTwo_block_split_51_remain5 limbs1.val[1].val
        simp at hlimbs1
        have := powTwo_split_block_5 (limbs1.val[1].val) (by simp : 5 * 1 + 0 < 51)
        simp[(by grind : ∀ a, a % 1 = 0)] at this
        simp[← this] at hlimbs1
        conv_rhs => rw[← hlimbs1]
        clear hlimbs1 this

        have hlimbs2:= powTwo_block_split_51_remain2 limbs3.val[2].val
        simp at hlimbs2
        have := powTwo_two_block_split (limbs3.val[2].val) (by simp : 2 * 1 < 51)
        simp at this
        simp[← this] at hlimbs2
        conv_rhs => rw[← hlimbs2]
        clear hlimbs2 this

        have hlimbs3:= powTwo_block_split_51_remain7 limbs5.val[3].val
        simp at hlimbs3
        have := powTwo_seven_block_split (limbs5.val[3].val) (by simp : 7 * 1 < 51)
        simp at this
        simp[← this] at hlimbs3
        conv_rhs => rw[← hlimbs3]
        clear hlimbs3 this

        have hlimbs4:= powTwo_block_split_51_remain4 limbs7.val[4].val
        simp at hlimbs4
        have := powTwo_four_block_split (limbs7.val[4].val) (by simp : 4 * 1 < 51)
        simp at this
        simp[← this] at hlimbs4
        conv_rhs => rw[← hlimbs4]
        clear hlimbs4 this




        simp[mul_add, ← mul_assoc,← add_assoc]
        simp[add_assoc]
        have : ((limbs7.val[4].val % 2251799813685248 ) >>> 44) % 256 = ((limbs7.val[4].val % 2251799813685248 ) >>> 44) := by
          apply Nat.mod_eq_of_lt
          rw[Nat.shiftRight_eq_div_pow]
          apply Nat.div_lt_of_lt_mul
          apply lt_trans _ (by simp: 2 ^ 51 < 2 ^ 44 * 256)
          apply Nat.mod_lt
          simp
        rw[this]

        have l7_lt: ((limbs7.val[4].val % 2251799813685248 ) >>> 44) % 128 = ((limbs7.val[4].val % 2251799813685248 ) >>> 44) := by
          apply Nat.mod_eq_of_lt
          rw[Nat.shiftRight_eq_div_pow]
          apply Nat.div_lt_of_lt_mul
          simp
          apply Nat.mod_lt
          simp

        have l70_lt: ((limbs7.val[4].val % 2251799813685248 ) >>> 44) % 2251799813685248 = ((limbs7.val[4].val % 2251799813685248 ) >>> 44) := by
          apply Nat.mod_eq_of_lt
          rw[Nat.shiftRight_eq_div_pow]
          apply Nat.div_lt_of_lt_mul
          apply lt_trans _ (by simp: 2 ^ 51 < 2 ^ 44 * 2251799813685248)
          apply Nat.mod_lt
          simp


        have := powTwo_seven_block_split (((limbs7.val[4].val) % 2 ^ 51) >>> 44) (by simp : 7 * 1 < 51)
        simp at this
        rw[l7_lt, l70_lt] at this
        conv_lhs => rw[← this]
        simp[mul_add, ← mul_assoc]
        conv_rhs => simp[← add_assoc]
    rw[this]
    constructor
    · -- BEGIN TASK
      apply Nat.ModEq.trans eq_mod_p_1
      simp[Field51_as_Nat, Finset.sum_range_succ]
      simp[Field51_as_Nat, Finset.sum_range_succ] at fe_post_2
      simp_all
      apply Nat.ModEq.symm fe_post_2
      -- END TASK
    · -- BEGIN TASK
      apply lt_p
      -- END TASK

end curve25519_dalek.backend.serial.u64.field.FieldElement51
