/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Tactics

/- # Spec Theorem for `FieldElement51::pow2k`

Specification and proof for `FieldElement51::pow2k`.

This function computes the 2^k-th power of the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

-/


set_option diagnostics.threshold 100000000

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Decomposition Lemma for Squaring in Radix 2^51

This lemma shows how squaring a number in radix 2^51 representation
decomposes modulo p = 2^255 - 19. It's the key algebraic identity
underlying the field squaring operation.
-/



lemma decompose (a0 a1 a2 a3 a4 : ℕ) :
  (a0 +
  2 ^ 51 * a1 +
  2^ (2 * 51) * a2 +
  2^ (3 * 51) * a3 +
  2^ (4 * 51) * a4) ^2
  ≡ a0 * a0 + 2 * (a1 * (19 * a4)+  a2 * (19 * a3)) +
    2 ^ 51 * (a3 * (19 * a3)  + 2 * (a0 * a1  +  a2 * (19 *a4)) ) +
    2 ^ (2 * 51) * (a1 * a1 + 2 * (a0 * a2 +  a4 * (19 * a3))) +
    2 ^ (3 * 51) * ( a4 * (19 * a4) + 2 * (a0 * a3 +  a1 * a2)) +
    2 ^ (4 * 51) * (a2 * a2 + 2 * (a0 * a4 +  a1 * a3))
   [MOD p] := by
  have expand : (a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) ^ 2 =
    a0 ^ 2 +
  2 ^ 51 * (2 * a0 * a1 ) +
  2 ^ (2 * 51) *(a1 ^ 2 + 2 * a0 * a2 ) +
  2 ^ (3 * 51) *(2* a0 * a3 + 2 * a1 * a2 ) +
  2 ^ (4 * 51) *(a2^2 + 2* a0 * a4 + 2 * a1 * a3) +
    2^ 255 *   ((2 * a1 * a4 + 2 * a2 * a3)+
  2 ^ 51 * (  (a3^2 + 2* a2* a4)) +
  2 ^ (2 * 51) *( (2* a3 * a4)) +
  2 ^ (3 * 51) *( a4^2))
     := by ring
  rw[expand]
  have key  : (2:ℕ)^255 ≡ 19 [MOD p] := by
    unfold p
    rw [Nat.ModEq]
    norm_num
  have := Nat.ModEq.mul_right ((2 * a1 * a4 + 2 * a2 * a3)+
  2 ^ 51 * (  (a3^2 + 2* a2* a4)) +
  2 ^ (2 * 51) *( (2* a3 * a4)) +
  2 ^ (3 * 51) *( a4^2)) key
  have := Nat.ModEq.add_left (a0 ^ 2 +
  2 ^ 51 * (2 * a0 * a1 ) +
  2 ^ (2 * 51) *(a1 ^ 2 + 2 * a0 * a2 ) +
  2 ^ (3 * 51) *(2* a0 * a3 + 2 * a1 * a2 ) +
  2 ^ (4 * 51) *(a2^2 + 2* a0 * a4 + 2 * a1 * a3)) this
  apply Nat.ModEq.trans this
  have : a0 ^ 2 + 2 ^ 51 * (2 * a0 * a1) + 2 ^ (2 * 51) * (a1 ^ 2 + 2 * a0 * a2) + 2 ^ (3 * 51) * (2 * a0 * a3 + 2 * a1 * a2) +
      2 ^ (4 * 51) * (a2 ^ 2 + 2 * a0 * a4 + 2 * a1 * a3) +
    19 *
      (2 * a1 * a4 + 2 * a2 * a3 + 2 ^ 51 * (a3 ^ 2 + 2 * a2 * a4) + 2 ^ (2 * 51) * (2 * a3 * a4) +
        2 ^ (3 * 51) * a4 ^ 2) =
    a0 * a0 + 2 * (a1 * (19 * a4)+  a2 * (19 * a3)) +
    2 ^ 51 * (a3 * (19 * a3)  + 2 * (a0 * a1  +  a2 * (19 *a4)) ) +
    2 ^ (2 * 51) * (a1 * a1 + 2 * (a0 * a2 +  a4 * (19 * a3))) +
    2 ^ (3 * 51) * ( a4 * (19 * a4) + 2 * (a0 * a3 +  a1 * a2)) +
    2 ^ (4 * 51) * (a2 * a2 + 2 * (a0 * a4 +  a1 * a3))
   := by grind
  rw[this]








/-! ## Spec for `pow2k.m` (inner limb multiplication)

This is the small helper used inside `pow2k` to multiply two 64-bit limbs
as 128-bit numbers.

- Inputs: two U64 values x and y
- Behavior: cast both to U128 and multiply, returning a U128
- No panic: multiplication in U128 never overflows
- Arithmetic correctness: the returned U128 encodes the product x.val * y.val
-/
@[progress]
theorem pow2k_m_spec (x y : U64) :
    ∃ prod, pow2k.m x y = ok prod ∧ prod.val = x.val * y.val := by
  unfold pow2k.m
  progress*
  simp_all
  have hx: x.val < 2^64:= by scalar_tac
  have hy: y.val < 2^64:= by scalar_tac
  have :=Nat.le_pred_of_lt hy
  have le1:= Nat.mul_le_mul_left (x.val) this
  have := Nat.le_pred_of_lt hx
  have le2:= Nat.mul_le_mul_right ((2 ^ 64).pred) this
  have := le_trans le1 le2
  apply le_trans this
  simp
  scalar_tac


theorem bound_two (a b c d n : ℕ)
  (ha : a < 2 ^ n)
  (hb : b < 2 ^ n)
  (hc : c < 2 ^ n)
  (hd : d < 2 ^ n) :
  a * (19 * b) + c * (19 * d) ≤  2* (2 ^ n).pred * (19 * (2 ^ n).pred):= by
    have := Nat.le_pred_of_lt hb
    have a_le1:= Nat.mul_le_mul_left a (Nat.mul_le_mul_left 19 this)
    have := Nat.mul_le_mul_right (19 * (2 ^ n).pred) (Nat.le_pred_of_lt ha)
    have hab:=le_trans a_le1 this
    have := Nat.le_pred_of_lt hd
    have a_le1:= Nat.mul_le_mul_left c (Nat.mul_le_mul_left 19 this)
    have := Nat.mul_le_mul_right (19 * (2 ^ n).pred) (Nat.le_pred_of_lt hc)
    have hcd:=le_trans a_le1 this
    have re:= add_le_add hab hcd
    have : ∀(a:ℕ), a + a = 2 * a := by scalar_tac
    rw[this,← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc] at re
    rw[← mul_assoc, ← mul_assoc, ← mul_assoc]
    exact re



theorem bound_twoI (a b c d n : ℕ)
  (ha : a < 2 ^ n)
  (hb : b < 2 ^ n)
  (hc : c < 2 ^ n)
  (hd : d < 2 ^ n) :
  a * b + c * (19 * d) ≤   (2 ^ n).pred *  (2 ^ n).pred +(2 ^ n).pred * (19 * (2 ^ n).pred):= by
    have := Nat.le_pred_of_lt hb
    have a_le1:= Nat.mul_le_mul_left a this
    have := Nat.mul_le_mul_right ((2 ^ n).pred) (Nat.le_pred_of_lt ha)
    have hab:=le_trans a_le1 this
    have := Nat.le_pred_of_lt hd
    have a_le1:= Nat.mul_le_mul_left c (Nat.mul_le_mul_left 19 this)
    have := Nat.mul_le_mul_right (19 * (2 ^ n).pred) (Nat.le_pred_of_lt hc)
    have hcd:=le_trans a_le1 this
    have re:= add_le_add hab hcd
    simp[← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc] at re
    rw[← mul_assoc, ← mul_assoc]
    exact re





theorem bound_twoII (a b c d n : ℕ)
  (ha : a < 2 ^ n)
  (hb : b < 2 ^ n)
  (hc : c < 2 ^ n)
  (hd : d < 2 ^ n) :
  a *  b + c *  d ≤  2* (2 ^ n).pred * ((2 ^ n).pred):= by
    have := Nat.le_pred_of_lt hb
    have a_le1:= Nat.mul_le_mul_left a this
    have := Nat.mul_le_mul_right ((2 ^ n).pred) (Nat.le_pred_of_lt ha)
    have hab:=le_trans a_le1 this
    have := Nat.le_pred_of_lt hd
    have a_le1:= Nat.mul_le_mul_left c this
    have := Nat.mul_le_mul_right ( (2 ^ n).pred) (Nat.le_pred_of_lt hc)
    have hcd:=le_trans a_le1 this
    have re:= add_le_add hab hcd
    have : ∀(a:ℕ), a + a = 2 * a := by scalar_tac
    rw[this,← mul_assoc] at re
    exact re

lemma LOW_51_BIT_MASK_spec : pow2k.LOW_51_BIT_MASK.val = 2 ^ 51 -1 := by
    unfold pow2k.LOW_51_BIT_MASK
    decide


lemma land_pow_two_sub_one_eq_mod (a n : Nat) :
    a &&& (2^n - 1) = a % 2^n := by
  induction n generalizing a
  · simp
    scalar_tac
  · simp

/-
natural language description:

    • Computes the 2^k-th power of a field element a in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs
    • This generalizes the square operation: applying pow2k(a, k) computes a^(2^k)

natural language specs:

    • The function always succeeds (no panic) when k > 0
    • Field51_as_Nat(result) ≡ Field51_as_Nat(a)^(2^k) (mod p)
    • Each limb of the result is bounded: result[i] < 2^51 for all i < 5
-/

/- **Spec and proof concerning the recursive loop `backend.serial.u64.field.FieldElement51.pow2k_loop`**:
- Runs exactly k iterations of “square-and-reduce” when k > 0
- The result, when converted to a natural number, is congruent to the input raised to the (2^k)-th power modulo p
- Input bounds: each input limb < 2^54 (as required by the underlying square routine)
- Output bounds after each iteration: each limb < 2^52

This mirrors the style used for other loop specifications (e.g. `square2_loop_spec`),
but adapts the mathematical statement to repeated squaring.
-/










set_option maxHeartbeats 10000000000000 in
-- progress* heavy

@[progress]
theorem pow2k_loop_spec (k : ℕ) (k' : U32) (a : Array U64 5#usize)
    (hk : 0 < k) (eqk : k'.val = k)
    (h_bounds : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k_loop k' a = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by

  expand h_bounds with 5
  have a1423:= bound_two (a[1]!.val) (a[4]!.val) (a[2]!.val) (a[3]!.val) 54
     (h_bounds_1) (h_bounds_4) (h_bounds_2) (h_bounds_3)
  have a0124:= bound_twoI (a[0]!.val) (a[1]!.val) (a[2]!.val) (a[4]!.val) 54
     (h_bounds_0) (h_bounds_1) (h_bounds_2) (h_bounds_4)
  have a0243:= bound_twoI (a[0]!.val) (a[2]!.val) (a[4]!.val) (a[3]!.val) 54
     (h_bounds_0) (h_bounds_2) (h_bounds_4) (h_bounds_3)
  have a0312:= bound_twoII (a[0]!.val) (a[3]!.val) (a[1]!.val) (a[2]!.val) 54
     (h_bounds_0) (h_bounds_3) (h_bounds_1) (h_bounds_2)
  have a0413:= bound_twoII (a[0]!.val) (a[4]!.val) (a[1]!.val) (a[3]!.val) 54
     (h_bounds_0) (h_bounds_4) (h_bounds_1) (h_bounds_3)

  have := Nat.le_pred_of_lt h_bounds_2
  have aa:= mul_le_mul this this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0413 (by simp : 0 ≤  2)
  have a0413I:= add_le_add aa this
  clear this aa
  clear this



  have a_le:= Nat.le_pred_of_lt h_bounds_4
  have := Nat.mul_le_mul_left 19 a_le
  have aa:= mul_le_mul a_le this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0312 (by simp : 0 ≤  2)
  have a0312I:= add_le_add aa this
  clear this aa
  clear this a_le



  have := Nat.le_pred_of_lt h_bounds_1
  have aa:= mul_le_mul this this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0243 (by simp : 0 ≤  2)
  have a0243I:= add_le_add aa this
  clear this aa
  clear this


  have a3_le:= Nat.le_pred_of_lt h_bounds_3
  have := Nat.mul_le_mul_left 19 a3_le
  have aa:= mul_le_mul a3_le this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0124 (by simp : 0 ≤  2)
  have a0124I:= add_le_add aa this
  clear this aa
  clear this a3_le

  have := Nat.le_pred_of_lt h_bounds_0
  have aa:= mul_le_mul this this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a1423 (by simp : 0 ≤  2)
  have a1423I:= add_le_add aa this
  clear this aa
  clear this

  unfold pow2k_loop
  progress*
  · simp_all
    apply le_trans a1423
    scalar_tac
  · simp_all
    have := mul_le_mul_of_nonneg_left a1423 (by simp : 0 ≤  2)
    apply le_trans this
    scalar_tac
  · simp_all
    apply le_trans a1423I
    scalar_tac
  · simp_all
    apply le_trans a0124
    scalar_tac
  · simp_all
    have := mul_le_mul_of_nonneg_left a0124 (by simp : 0 ≤  2)
    apply le_trans this
    scalar_tac
  · simp_all
    apply le_trans a0124I
    scalar_tac
  · simp_all
    apply le_trans a0243
    scalar_tac
  · simp_all
    have := mul_le_mul_of_nonneg_left a0243 (by simp : 0 ≤  2)
    apply le_trans this
    scalar_tac
  · simp_all
    apply le_trans a0243I
    scalar_tac
  · simp_all
    apply le_trans a0312I
    scalar_tac
  · have carry_le: carry.val ≤  (2^ 64 - 2 ^ 51) / 19 := by
      rw[carry_post, UScalar.cast_val_eq, UScalarTy.numBits]
      suffices h : i51.val ≤  (2^ 64 - 2 ^ 51) / 19
      · have i51_mod: i51.val % 2 ^ 64 = i51.val := by
          apply Nat.mod_eq_of_lt
          have : i51.val ≤  2^64-1 := by
            apply le_trans h
            simp
          apply Nat.lt_of_le_pred (by simp) this
        rw[i51_mod]
        apply h
      · rw[i51_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[c41_post]
        set con := (2 ^ 54).pred * (2 ^ 54).pred + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
        have : c4.val ≤ con := by simp_all
        suffices h : i48.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
        · have := add_le_add this h
          scalar_tac
        · rw[i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
          suffices h : i47.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
          · have : i47.val % 2 ^ 128 = i47.val := by
             apply Nat.mod_eq_of_lt
             have : i47.val ≤  2^128-1 := by
              apply le_trans h
              simp[hcon]
             apply Nat.lt_of_le_pred (by simp) this
            rw[this]
            exact h
          · rw[i47_post, UScalar.cast_val_eq, UScalarTy.numBits]
            suffices h : i46.val ≤  2^ 64 - 1
            · have : i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp) h
              rw[this]
              apply le_trans h
              simp[hcon]
            · rw[i46_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[c31_post]
              set con1 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon1
              have : c3.val ≤ con1 := by simp_all
              suffices h : i43.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
              · have := add_le_add this h
                simp_all
              · rw[i43_post, UScalar.cast_val_eq, UScalarTy.numBits]
                suffices h : i42.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
                · have : i42.val % 2 ^ 128 = i42.val := by
                    apply Nat.mod_eq_of_lt
                    have : i42.val ≤  2^128-1 := by
                        apply le_trans h
                        simp[hcon1]
                    apply Nat.lt_of_le_pred (by simp) this
                  rw[this]
                  exact h
                · rw[i42_post, UScalar.cast_val_eq, UScalarTy.numBits]
                  suffices h : i41.val ≤  2^ 64 - 1
                  · have : i41.val % 2 ^ 64 = i41.val := by
                        apply Nat.mod_eq_of_lt
                        apply Nat.lt_of_le_pred (by simp) h
                    rw[this]
                    apply le_trans h
                    simp[hcon1]
                  · rw[i41_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[c21_post]
                    set con2 := (2 ^ 54).pred * (2 ^ 54).pred + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon2
                    have : c2.val ≤ con2 := by simp_all
                    suffices h : i38.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                    · have := add_le_add this h
                      simp_all
                    · rw[i38_post, UScalar.cast_val_eq, UScalarTy.numBits]
                      suffices h : i37.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                      · have : i37.val % 2 ^ 128 = i37.val := by
                          apply Nat.mod_eq_of_lt
                          have : i37.val ≤  2^128-1 := by
                            apply le_trans h
                            simp[hcon2]
                          apply Nat.lt_of_le_pred (by simp) this
                        rw[this]
                        exact h
                      · rw[i37_post, UScalar.cast_val_eq, UScalarTy.numBits]
                        suffices h : i36.val ≤  2^ 64 - 1
                        · have : i36.val % 2 ^ 64 = i36.val := by
                            apply Nat.mod_eq_of_lt
                            apply Nat.lt_of_le_pred (by simp) h
                          rw[this]
                          apply le_trans h
                          simp[hcon2]
                        · rw[i36_post_1, Nat.shiftRight_eq_div_pow]
                          apply Nat.div_le_of_le_mul
                          rw[c11_post]
                          set con3 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon3
                          have : c1.val ≤ con3 := by simp_all
                          suffices h : i33.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                          · have := add_le_add this h
                            simp_all
                          · rw[i33_post, UScalar.cast_val_eq, UScalarTy.numBits]
                            suffices h : i32.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                            · have : i32.val % 2 ^ 128 = i32.val := by
                                    apply Nat.mod_eq_of_lt
                                    have : i32.val ≤  2^128-1 := by
                                        apply le_trans h
                                        simp[hcon3]
                                    apply Nat.lt_of_le_pred (by simp) this
                              rw[this]
                              exact h
                            · rw[i32_post, UScalar.cast_val_eq, UScalarTy.numBits]
                              suffices h : i31.val ≤  2^ 64 - 1
                              · have : i31.val % 2 ^ 64 = i31.val := by
                                        apply Nat.mod_eq_of_lt
                                        apply Nat.lt_of_le_pred (by simp) h
                                rw[this]
                                apply le_trans h
                                simp[hcon3]
                              · rw[i31_post_1, Nat.shiftRight_eq_div_pow]
                                apply Nat.div_le_of_le_mul
                                simp_all
                                apply le_trans a1423I
                                simp
    have h : carry.val ≤  2^ 64 / 19 := by
       apply le_trans carry_le
       simp
    have := Nat.mul_le_mul_right 19 h
    scalar_tac
  · have carry_le: carry.val ≤  (2^ 64 - 2 ^ 51) / 19 := by
      rw[carry_post, UScalar.cast_val_eq, UScalarTy.numBits]
      suffices h : i51.val ≤  (2^ 64 - 2 ^ 51) / 19
      · have i51_mod: i51.val % 2 ^ 64 = i51.val := by
          apply Nat.mod_eq_of_lt
          have : i51.val ≤  2^64-1 := by
            apply le_trans h
            simp
          apply Nat.lt_of_le_pred (by simp) this
        rw[i51_mod]
        apply h
      · rw[i51_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[c41_post]
        set con := (2 ^ 54).pred * (2 ^ 54).pred + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
        have : c4.val ≤ con := by simp_all
        suffices h : i48.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
        · have := add_le_add this h
          scalar_tac
        · rw[i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
          suffices h : i47.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
          · have : i47.val % 2 ^ 128 = i47.val := by
             apply Nat.mod_eq_of_lt
             have : i47.val ≤  2^128-1 := by
              apply le_trans h
              simp[hcon]
             apply Nat.lt_of_le_pred (by simp) this
            rw[this]
            exact h
          · rw[i47_post, UScalar.cast_val_eq, UScalarTy.numBits]
            suffices h : i46.val ≤  2^ 64 - 1
            · have : i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp) h
              rw[this]
              apply le_trans h
              simp[hcon]
            · rw[i46_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[c31_post]
              set con1 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon1
              have : c3.val ≤ con1 := by simp_all
              suffices h : i43.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
              · have := add_le_add this h
                simp_all
              · rw[i43_post, UScalar.cast_val_eq, UScalarTy.numBits]
                suffices h : i42.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
                · have : i42.val % 2 ^ 128 = i42.val := by
                    apply Nat.mod_eq_of_lt
                    have : i42.val ≤  2^128-1 := by
                        apply le_trans h
                        simp[hcon1]
                    apply Nat.lt_of_le_pred (by simp) this
                  rw[this]
                  exact h
                · rw[i42_post, UScalar.cast_val_eq, UScalarTy.numBits]
                  suffices h : i41.val ≤  2^ 64 - 1
                  · have : i41.val % 2 ^ 64 = i41.val := by
                        apply Nat.mod_eq_of_lt
                        apply Nat.lt_of_le_pred (by simp) h
                    rw[this]
                    apply le_trans h
                    simp[hcon1]
                  · rw[i41_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[c21_post]
                    set con2 := (2 ^ 54).pred * (2 ^ 54).pred + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon2
                    have : c2.val ≤ con2 := by simp_all
                    suffices h : i38.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                    · have := add_le_add this h
                      simp_all
                    · rw[i38_post, UScalar.cast_val_eq, UScalarTy.numBits]
                      suffices h : i37.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                      · have : i37.val % 2 ^ 128 = i37.val := by
                          apply Nat.mod_eq_of_lt
                          have : i37.val ≤  2^128-1 := by
                            apply le_trans h
                            simp[hcon2]
                          apply Nat.lt_of_le_pred (by simp) this
                        rw[this]
                        exact h
                      · rw[i37_post, UScalar.cast_val_eq, UScalarTy.numBits]
                        suffices h : i36.val ≤  2^ 64 - 1
                        · have : i36.val % 2 ^ 64 = i36.val := by
                            apply Nat.mod_eq_of_lt
                            apply Nat.lt_of_le_pred (by simp) h
                          rw[this]
                          apply le_trans h
                          simp[hcon2]
                        · rw[i36_post_1, Nat.shiftRight_eq_div_pow]
                          apply Nat.div_le_of_le_mul
                          rw[c11_post]
                          set con3 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon3
                          have : c1.val ≤ con3 := by simp_all
                          suffices h : i33.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                          · have := add_le_add this h
                            simp_all
                          · rw[i33_post, UScalar.cast_val_eq, UScalarTy.numBits]
                            suffices h : i32.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                            · have : i32.val % 2 ^ 128 = i32.val := by
                                    apply Nat.mod_eq_of_lt
                                    have : i32.val ≤  2^128-1 := by
                                        apply le_trans h
                                        simp[hcon3]
                                    apply Nat.lt_of_le_pred (by simp) this
                              rw[this]
                              exact h
                            · rw[i32_post, UScalar.cast_val_eq, UScalarTy.numBits]
                              suffices h : i31.val ≤  2^ 64 - 1
                              · have : i31.val % 2 ^ 64 = i31.val := by
                                        apply Nat.mod_eq_of_lt
                                        apply Nat.lt_of_le_pred (by simp) h
                                rw[this]
                                apply le_trans h
                                simp[hcon3]
                              · rw[i31_post_1, Nat.shiftRight_eq_div_pow]
                                apply Nat.div_le_of_le_mul
                                simp_all
                                apply le_trans a1423I
                                simp
    have : i55.val < 2 ^ 51 := by
      simp_all
      rw[LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod,
      UScalar.cast_val_eq, UScalarTy.numBits]
      apply Nat.mod_lt  (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
    have h : i54.val ≤ 2 ^ 64  - 2 ^ 51 := by
     simp_all
     have := Nat.mul_le_mul_right 19 carry_le
     apply le_trans this
     simp
    have := add_le_add this h
    simp_all
    rw[LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits]
    rw[LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits] at this
    scalar_tac
  · have carry_le: carry.val ≤  (2^ 64 - 2 ^ 51) / 19 := by
      rw[carry_post, UScalar.cast_val_eq, UScalarTy.numBits]
      suffices h : i51.val ≤  (2^ 64 - 2 ^ 51) / 19
      · have i51_mod: i51.val % 2 ^ 64 = i51.val := by
          apply Nat.mod_eq_of_lt
          have : i51.val ≤  2^64-1 := by
            apply le_trans h
            simp
          apply Nat.lt_of_le_pred (by simp) this
        rw[i51_mod]
        apply h
      · rw[i51_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[c41_post]
        set con := (2 ^ 54).pred * (2 ^ 54).pred + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
        have : c4.val ≤ con := by simp_all
        suffices h : i48.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
        · have := add_le_add this h
          scalar_tac
        · rw[i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
          suffices h : i47.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
          · have : i47.val % 2 ^ 128 = i47.val := by
             apply Nat.mod_eq_of_lt
             have : i47.val ≤  2^128-1 := by
              apply le_trans h
              simp[hcon]
             apply Nat.lt_of_le_pred (by simp) this
            rw[this]
            exact h
          · rw[i47_post, UScalar.cast_val_eq, UScalarTy.numBits]
            suffices h : i46.val ≤  2^ 64 - 1
            · have : i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp) h
              rw[this]
              apply le_trans h
              simp[hcon]
            · rw[i46_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[c31_post]
              set con1 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon1
              have : c3.val ≤ con1 := by simp_all
              suffices h : i43.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
              · have := add_le_add this h
                simp_all
              · rw[i43_post, UScalar.cast_val_eq, UScalarTy.numBits]
                suffices h : i42.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
                · have : i42.val % 2 ^ 128 = i42.val := by
                    apply Nat.mod_eq_of_lt
                    have : i42.val ≤  2^128-1 := by
                        apply le_trans h
                        simp[hcon1]
                    apply Nat.lt_of_le_pred (by simp) this
                  rw[this]
                  exact h
                · rw[i42_post, UScalar.cast_val_eq, UScalarTy.numBits]
                  suffices h : i41.val ≤  2^ 64 - 1
                  · have : i41.val % 2 ^ 64 = i41.val := by
                        apply Nat.mod_eq_of_lt
                        apply Nat.lt_of_le_pred (by simp) h
                    rw[this]
                    apply le_trans h
                    simp[hcon1]
                  · rw[i41_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[c21_post]
                    set con2 := (2 ^ 54).pred * (2 ^ 54).pred + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon2
                    have : c2.val ≤ con2 := by simp_all
                    suffices h : i38.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                    · have := add_le_add this h
                      simp_all
                    · rw[i38_post, UScalar.cast_val_eq, UScalarTy.numBits]
                      suffices h : i37.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                      · have : i37.val % 2 ^ 128 = i37.val := by
                          apply Nat.mod_eq_of_lt
                          have : i37.val ≤  2^128-1 := by
                            apply le_trans h
                            simp[hcon2]
                          apply Nat.lt_of_le_pred (by simp) this
                        rw[this]
                        exact h
                      · rw[i37_post, UScalar.cast_val_eq, UScalarTy.numBits]
                        suffices h : i36.val ≤  2^ 64 - 1
                        · have : i36.val % 2 ^ 64 = i36.val := by
                            apply Nat.mod_eq_of_lt
                            apply Nat.lt_of_le_pred (by simp) h
                          rw[this]
                          apply le_trans h
                          simp[hcon2]
                        · rw[i36_post_1, Nat.shiftRight_eq_div_pow]
                          apply Nat.div_le_of_le_mul
                          rw[c11_post]
                          set con3 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon3
                          have : c1.val ≤ con3 := by simp_all
                          suffices h : i33.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                          · have := add_le_add this h
                            simp_all
                          · rw[i33_post, UScalar.cast_val_eq, UScalarTy.numBits]
                            suffices h : i32.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                            · have : i32.val % 2 ^ 128 = i32.val := by
                                    apply Nat.mod_eq_of_lt
                                    have : i32.val ≤  2^128-1 := by
                                        apply le_trans h
                                        simp[hcon3]
                                    apply Nat.lt_of_le_pred (by simp) this
                              rw[this]
                              exact h
                            · rw[i32_post, UScalar.cast_val_eq, UScalarTy.numBits]
                              suffices h : i31.val ≤  2^ 64 - 1
                              · have : i31.val % 2 ^ 64 = i31.val := by
                                        apply Nat.mod_eq_of_lt
                                        apply Nat.lt_of_le_pred (by simp) h
                                rw[this]
                                apply le_trans h
                                simp[hcon3]
                              · rw[i31_post_1, Nat.shiftRight_eq_div_pow]
                                apply Nat.div_le_of_le_mul
                                simp_all
                                apply le_trans a1423I
                                simp
    simp_all
    rw[LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod,
      UScalar.cast_val_eq, UScalarTy.numBits,
      land_pow_two_sub_one_eq_mod,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits]
    have := Nat.mod_lt  (c11.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
    suffices h: ((c0.val % 2 ^ 64) % 2 ^ 51 +
    (i51.val % 2 ^ 64) * 19) >>> 51 ≤ 2 ^ 64 - 2 ^ 51
    · have := add_le_add  (Nat.le_pred_of_lt this) h
      apply le_trans this
      simp[U64.max, U64.numBits]
    · rw[ Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      have := Nat.mod_lt  (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
      suffices h: i51.val % 2 ^ 64 * 19 ≤ 2 ^ 51 * (2 ^ 64 - 2 ^ 51) - 2 ^ 51
      · have := Nat.mod_lt  (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
        have := add_le_add (Nat.le_pred_of_lt this) h
        apply le_trans this
        simp
      · rw[UScalar.cast_val_eq, UScalarTy.numBits] at carry_le
        have := Nat.mul_le_mul_right 19 carry_le
        apply le_trans this
        simp
  · have hi31_lt : i31.val ≤  2^ 64 - 1 := by
     rw[i31_post_1, Nat.shiftRight_eq_div_pow]
     apply Nat.div_le_of_le_mul
     simp_all
     apply le_trans a1423I
     simp
    have hi36_lt : i36.val ≤  2^ 64 - 1 := by
                          rw[i36_post_1, Nat.shiftRight_eq_div_pow]
                          apply Nat.div_le_of_le_mul
                          rw[c11_post]
                          set con3 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon3
                          have : c1.val ≤ con3 := by simp_all
                          suffices h : i33.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                          · have := add_le_add this h
                            simp_all
                          · rw[i33_post, UScalar.cast_val_eq, UScalarTy.numBits]
                            suffices h : i32.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                            · have : i32.val % 2 ^ 128 = i32.val := by
                                    apply Nat.mod_eq_of_lt
                                    have : i32.val ≤  2^128-1 := by
                                        apply le_trans h
                                        simp[hcon3]
                                    apply Nat.lt_of_le_pred (by simp) this
                              rw[this]
                              exact h
                            · rw[i32_post, UScalar.cast_val_eq, UScalarTy.numBits]
                              suffices h : i31.val ≤  2^ 64 - 1
                              · have : i31.val % 2 ^ 64 = i31.val := by
                                        apply Nat.mod_eq_of_lt
                                        apply Nat.lt_of_le_pred (by simp) h
                                rw[this]
                                apply le_trans h
                                simp[hcon3]
                              · simp_all
    have  hi41_lt : i41.val ≤  2^ 64 - 1 := by
                    rw[i41_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[c21_post]
                    set con2 := (2 ^ 54).pred * (2 ^ 54).pred + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon2
                    have : c2.val ≤ con2 := by simp_all
                    suffices h : i38.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                    · have := add_le_add this h
                      simp_all
                    · rw[i38_post, UScalar.cast_val_eq, UScalarTy.numBits]
                      suffices h : i37.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                      · have : i37.val % 2 ^ 128 = i37.val := by
                          apply Nat.mod_eq_of_lt
                          have : i37.val ≤  2^128-1 := by
                            apply le_trans h
                            simp[hcon2]
                          apply Nat.lt_of_le_pred (by simp) this
                        rw[this]
                        exact h
                      · rw[i37_post, UScalar.cast_val_eq, UScalarTy.numBits]
                        suffices h : i36.val ≤  2^ 64 - 1
                        · have : i36.val % 2 ^ 64 = i36.val := by
                            apply Nat.mod_eq_of_lt
                            apply Nat.lt_of_le_pred (by simp) h
                          rw[this]
                          apply le_trans h
                          simp[hcon2]
                        · simp_all
    have hi46_lt : i46.val ≤  2^ 64 - 1 := by
              rw[i46_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[c31_post]
              set con1 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon1
              have : c3.val ≤ con1 := by simp_all
              suffices h : i43.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
              · have := add_le_add this h
                simp_all
              · rw[i43_post, UScalar.cast_val_eq, UScalarTy.numBits]
                suffices h : i42.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
                · have : i42.val % 2 ^ 128 = i42.val := by
                    apply Nat.mod_eq_of_lt
                    have : i42.val ≤  2^128-1 := by
                        apply le_trans h
                        simp[hcon1]
                    apply Nat.lt_of_le_pred (by simp) this
                  rw[this]
                  exact h
                · rw[i42_post, UScalar.cast_val_eq, UScalarTy.numBits]
                  suffices h : i41.val ≤  2^ 64 - 1
                  · have : i41.val % 2 ^ 64 = i41.val := by
                        apply Nat.mod_eq_of_lt
                        apply Nat.lt_of_le_pred (by simp) h
                    rw[this]
                    apply le_trans h
                    simp[hcon1]
                  · simp_all
    have  hi51_lt0 : i51.val ≤  (2^ 64 - 2 ^ 51) / 19 := by
        rw[i51_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[c41_post]
        set con := (2 ^ 54).pred * (2 ^ 54).pred + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
        have : c4.val ≤ con := by simp_all
        suffices h : i48.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
        · have := add_le_add this h
          scalar_tac
        · rw[i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
          suffices h : i47.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
          · have : i47.val % 2 ^ 128 = i47.val := by
             apply Nat.mod_eq_of_lt
             have : i47.val ≤  2^128-1 := by
              apply le_trans h
              simp[hcon]
             apply Nat.lt_of_le_pred (by simp) this
            rw[this]
            exact h
          · rw[i47_post, UScalar.cast_val_eq, UScalarTy.numBits]
            suffices h : i46.val ≤  2^ 64 - 1
            · have : i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp) h
              rw[this]
              apply le_trans h
              simp[hcon]
            · simp_all
    have  hi51_lt : i51.val ≤  2^ 64 - 1 := by
     apply le_trans hi51_lt0
     simp
    constructor
    · simp_all[Field51_as_Nat, Finset.sum_range_succ]
      rw[LOW_51_BIT_MASK_spec,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,]
      simp[UScalar.cast_val_eq, UScalarTy.numBits]
      have : (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
          2 ^ 51 * (c11.val % 2^51 + (c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
          2^(2 * 51) * (c21.val % 2 ^51) +
          2^(3 * 51) * (c31.val % 2^51) +
          2^(4* 51) * (c41.val % 2^51)
          = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
          2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
          2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
          2 ^ (3 * 51) * ((c3.val + i41 % 2 ^ 64) % 2 ^51) +
          2 ^ (4 * 51) * ((c4.val + i46 % 2 ^ 64) % 2 ^51) := by
        calc
         (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
          2 ^ 51 * (c11.val % 2^51 + (c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
          2^(2 * 51) * (c21.val % 2 ^51) +
          2^(3 * 51) * (c31.val % 2^51) +
          2^(4* 51) * (c41.val % 2^51)
          = (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
          2 ^ 51 * ((c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
          2 ^ 51 * (c11.val % 2^51 ) +
          2^(2 * 51) * (c21.val % 2 ^51) +
          2^(3 * 51) * (c31.val % 2^51) +
          2^(4* 51) * (c41.val % 2^51)
          := by ring
          _ =  (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
          2 ^ 51 * (c11.val % 2^51 ) +
          2 ^ (2 * 51) * (c21.val % 2 ^51) +
          2 ^ (3 * 51) * (c31.val % 2^51) +
          2 ^ (4 * 51) * (c41.val % 2^51)
           := by
            simp[Nat.shiftRight_eq_div_pow]
            have := Nat.mod_add_div (c0.val % 2 ^51 + i51.val % 2^64 * 19)  (2 ^ 51)
            simp at this
            rw[this]
          _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
          2 ^ 51 * (c11.val % 2^51)  +
          2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
          2 ^ (3 * 51) * (c31.val % 2^51) +
          2 ^ (4 * 51) * (c41.val % 2^51)
           := by simp[c21_post, c2_post, UScalar.cast_val_eq, UScalarTy.numBits]
          _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
          2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
          2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
          2 ^ (3 * 51) * (c31.val % 2^51) +
          2 ^ (4 * 51) * (c41.val % 2^51)
           := by simp[c11_post, c1_post, UScalar.cast_val_eq, UScalarTy.numBits]
          _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
          2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
          2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
          2 ^ (3 * 51) * ((c3.val + i41 % 2 ^ 64) % 2 ^51) +
          2 ^ (4 * 51) * (c41.val % 2^51)
           := by simp[c31_post, c3_post, UScalar.cast_val_eq, UScalarTy.numBits]
          _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
          2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
          2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
          2 ^ (3 * 51) * ((c3.val + i41 % 2 ^ 64) % 2 ^51) +
          2 ^ (4 * 51) * ((c4.val + i46 % 2 ^ 64) % 2 ^51)
           := by
             simp[c41_post, c4_post, UScalar.cast_val_eq, UScalarTy.numBits]
      have : (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
          2 ^ 51 * (c11.val % 2^51 + (c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
          2^(2 * 51) * (c21.val % 2 ^51) +
          2^(3 * 51) * (c31.val % 2^51) +
          2^(4* 51) * (c41.val % 2^51)
          =
        (c0.val % 2 ^51 + i51.val  * 19)  +
          2 ^ 51 * ((c1.val + i31  ) % 2^51)  +
          2 ^ (2 * 51) * ((c2.val + i36 ) % 2 ^51) +
          2 ^ (3 * 51) * ((c3.val + i41 ) % 2 ^51) +
          2 ^ (4 * 51) * ((c4.val + i46 ) % 2 ^51) := by
        have hi31_mod: i31.val % 2 ^ 64 = i31.val := by
            apply Nat.mod_eq_of_lt
            apply Nat.lt_of_le_pred (by simp)
            simp_all
        have hi36_mod: i36.val % 2 ^ 64 = i36.val := by
            apply Nat.mod_eq_of_lt
            apply Nat.lt_of_le_pred (by simp)
            simp_all
        have hi41_mod: i41.val % 2 ^ 64 = i41.val := by
            apply Nat.mod_eq_of_lt
            apply Nat.lt_of_le_pred (by simp)
            simp_all
        have hi46_mod: i46.val % 2 ^ 64 = i46.val := by
            apply Nat.mod_eq_of_lt
            apply Nat.lt_of_le_pred (by simp)
            simp_all
        have hi51_mod : i51.val % 2 ^ 64 = i51.val := by
            apply Nat.mod_eq_of_lt
            apply Nat.lt_of_le_pred (by simp)
            simp_all
        rw[this, hi31_mod, hi36_mod, hi41_mod, hi46_mod, hi51_mod]
      have eq_mod1: ↑c0 % 2 ^ 51 + ↑i51 * 19 +
      2 ^ 51 * ((↑c1 + ↑i31) % 2 ^ 51) +
      2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
      2 ^ (3 * 51) * ((↑c3 + ↑i41) % 2 ^ 51) +
      2 ^ (4 * 51) * ((↑c4 + ↑i46) % 2 ^ 51)
      ≡ ↑c0 % 2 ^ 51  +
      2 ^ 51 * ((↑c1 + ↑i31) % 2 ^ 51) +
      2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
      2 ^ (3 * 51) * ((↑c3 + ↑i41) % 2 ^ 51) +
      2 ^ (4 * 51) * ((↑c4 + ↑i46) % 2 ^ 51 + 2 ^ 51 * i51.val)  [MOD p] := by
        have key  : 19 ≡ (2:ℕ)^255 [MOD p] := by
          unfold p
          rw [Nat.ModEq]
          norm_num
        have := Nat.ModEq.mul_left i51.val key
        have := Nat.ModEq.add_right (2 ^ 51 * ((↑c1 + ↑i31) % 2 ^ 51) + 2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
      2 ^ (3 * 51) * ((↑c3 + ↑i41) % 2 ^ 51) +
      2 ^ (4 * 51) * ((↑c4 + ↑i46) % 2 ^ 51)) this
        have := Nat.ModEq.add_left (↑c0 % 2 ^ 51) this
        rw[← add_assoc, ← add_assoc, ← add_assoc
        , ← add_assoc] at this
        apply Nat.ModEq.trans this
        have : c0.val % 2 ^ 51 + (i51.val * 2 ^ 255 +
      (2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
      2 ^ (2 * 51) * ((c2.val + i36.val) % 2 ^ 51) +
          2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51) +
        2 ^ (4 * 51) * ((c4.val + i46.val) % 2 ^ 51)))
      = c0.val % 2 ^ 51  +
      2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
      2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
      2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51) +
      2 ^ (4 * 51) * ((c4.val + i46.val) % 2 ^ 51 + 2 ^ 51 * i51.val) := by grind
        rw[this]
      have : i51.val = (c4.val + i46.val)/ 2 ^ 51   := by
           have hi46_mod: i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp)
                simp_all
           rw[i51_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi46_mod, Nat.shiftRight_eq_div_pow]
           simp_all
      have : (c4.val + i46.val) % 2 ^ 51 + 2 ^ 51 * i51.val
      = (c4.val + i46.val) := by
          rw[this]
          apply Nat.mod_add_div
      rw[this] at eq_mod1
      have : c0.val % 2 ^ 51  +
      2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
      2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
      2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51) +
      2 ^ (4 * 51) * ((c4.val + i46.val))
      = c0.val % 2 ^ 51  +
      2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
      2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
      2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51 +  2 ^ 51 * i46.val) +
      2 ^ (4 * 51) * c4.val  := by grind
      rw[this] at eq_mod1
      have : i46.val = (c3.val + i41.val)/ 2 ^ 51   := by
           have hi41_mod: i41.val % 2 ^ 64 = i41.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp)
                simp_all
           rw[i46_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi41_mod, Nat.shiftRight_eq_div_pow]
           simp_all
      have : (c3.val + i41.val) % 2 ^ 51 + 2 ^ 51 * i46.val
      = (c3.val + i41.val) := by
          rw[this]
          apply Nat.mod_add_div
      rw[this] at eq_mod1
      have : c0.val % 2 ^ 51  +
      2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
      2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
      2 ^ (3 * 51) * (c3.val + i41.val ) +
      2 ^ (4 * 51) * c4.val
      = c0.val % 2 ^ 51  +
      2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
      2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51 + 2 ^ 51 * i41.val) +
      2 ^ (3 * 51) * c3.val  +
      2 ^ (4 * 51) * c4.val  := by grind
      rw[this] at eq_mod1
      have : i41.val = (c2.val + i36.val)/ 2 ^ 51   := by
           have hi36_mod: i36.val % 2 ^ 64 = i36.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp)
                simp_all
           rw[i41_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi36_mod, Nat.shiftRight_eq_div_pow]
           simp_all
      have : (c2.val + i36.val) % 2 ^ 51 + 2 ^ 51 * i41.val
      = (c2.val + i36.val) := by
          rw[this]
          apply Nat.mod_add_div
      rw[this] at eq_mod1
      have : c0.val % 2 ^ 51  +
      2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
      2 ^ (2 * 51) * (c2.val + i36.val) +
      2 ^ (3 * 51) * c3.val +
      2 ^ (4 * 51) * c4.val
      = c0.val % 2 ^ 51  +
      2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51 + 2 ^ 51 * i36.val) +
      2 ^ (2 * 51) * c2.val +
      2 ^ (3 * 51) * c3.val  +
      2 ^ (4 * 51) * c4.val  := by grind
      rw[this] at eq_mod1
      have : i36.val = (c1.val + i31.val)/ 2 ^ 51   := by
           have hi31_mod: i31.val % 2 ^ 64 = i31.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp)
                simp_all
           rw[i36_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi31_mod, Nat.shiftRight_eq_div_pow]
           simp_all
      have : (c1.val + i31.val) % 2 ^ 51 + 2 ^ 51 * i36.val
      = (c1.val + i31.val) := by
          rw[this]
          apply Nat.mod_add_div
      rw[this] at eq_mod1
      have : c0.val % 2 ^ 51  +
      2 ^ 51 * (c1.val + i31.val) +
      2 ^ (2 * 51) * c2.val +
      2 ^ (3 * 51) * c3.val  +
      2 ^ (4 * 51) * c4.val
      = (c0.val % 2 ^ 51  +  2 ^ 51 * i31.val) +
      2 ^ 51 * c1.val  +
      2 ^ (2 * 51) * c2.val +
      2 ^ (3 * 51) * c3.val +
      2 ^ (4 * 51) * c4.val
         := by grind
      rw[this] at eq_mod1
      have : i31.val = c0.val / 2 ^ 51   := by
           rw[i31_post_1, Nat.shiftRight_eq_div_pow, c0_post]
      have : (c0.val) % 2 ^ 51 + 2 ^ 51 * i31.val
      = c0.val := by
          rw[this]
          apply Nat.mod_add_div
      rw[this] at eq_mod1
      simp_all
      apply Nat.ModEq.trans eq_mod1
      have : k =1 := by
        grind
      rw[this]
      have : (a[0].val + 2^ 51 * a[1].val + 2^(2* 51) * a[2].val
        + 2^(3* 51) * a[3].val
      + 2^(4* 51) * a[4].val) ^ 2 ^ 1 =(a[0].val + 2^ 51 * a[1].val + 2^(2* 51) * a[2].val
        + 2^(3* 51) * a[3].val
      + 2^(4* 51) * a[4].val) ^ 2 := by
        grind
      simp
      have :=decompose a[0].val a[1].val a[2].val a[3].val a[4].val
      apply Nat.ModEq.symm
      apply Nat.ModEq.trans this
      simp
      apply Nat.ModEq.rfl
    · intro i hi
      interval_cases i
      · simp
        suffices h : i62.val < 2 ^ 51
        · apply lt_trans h
          simp
        · simp[i62_post_1]
          rw[LOW_51_BIT_MASK_spec,
          land_pow_two_sub_one_eq_mod]
          apply Nat.mod_lt
          simp
      · simp
        rw[a7_post]
        simp_all
        rw[
         LOW_51_BIT_MASK_spec,
                land_pow_two_sub_one_eq_mod,
                Nat.shiftRight_eq_div_pow,
                UScalar.cast_val_eq, UScalarTy.numBits,
                UScalar.cast_val_eq, UScalarTy.numBits,
                UScalar.cast_val_eq, UScalarTy.numBits]
        suffices h : (((c0.val % 2 ^ 64) &&& 2 ^ 51 - 1) +
                (i51.val % 2 ^ 64) * 19) / 2 ^ 51 < 2 ^ 52 - (2 ^ 51)
        · have := Nat.mod_lt (c11.val % 2^ 64 % 2 ^ 64) (by simp :0 < 2^ 51)
          have := Nat.add_lt_add this h
          simp at this
          simp
          apply this
        · apply Nat.div_lt_of_lt_mul
          suffices h: i51.val % 2 ^ 64 * 19 < 2 ^ 51 * (2 ^ 52 - 2 ^ 51) - 2 ^ 51
          · rw[land_pow_two_sub_one_eq_mod]
            have := Nat.mod_lt (c0.val % 2^ 64 % 2 ^ 64) (by simp :0 < 2^ 51)
            have := Nat.add_lt_add this h
            simp at this
            simp
            apply this
          · have hi51_mod : i51.val % 2 ^ 64 = i51.val := by
              apply Nat.mod_eq_of_lt
              apply Nat.lt_of_le_pred (by simp)
              simp_all
            rw[hi51_mod]
            have := Nat.lt_succ_of_le hi51_lt0
            have := (Nat.mul_lt_mul_right (by simp: 0<19)).mpr this
            simp[i51_post_1]
            apply lt_trans this
            simp
      · simp_all
        apply lt_trans _ (by simp : 2^ 51 < 2 ^ 52)
        rw[ LOW_51_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod]
        apply Nat.mod_lt
        simp
      · simp_all
        apply lt_trans _ (by simp : 2^ 51 < 2 ^ 52)
        rw[ LOW_51_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod]
        apply Nat.mod_lt
        simp
      · simp_all
        apply lt_trans _ (by simp : 2^ 51 < 2 ^ 52)
        rw[ LOW_51_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod]
        apply Nat.mod_lt
        simp
  · have hi31_lt : i31.val ≤  2^ 64 - 1 := by
     rw[i31_post_1, Nat.shiftRight_eq_div_pow]
     apply Nat.div_le_of_le_mul
     simp_all
     apply le_trans a1423I
     simp
    have hi36_lt : i36.val ≤  2^ 64 - 1 := by
                          rw[i36_post_1, Nat.shiftRight_eq_div_pow]
                          apply Nat.div_le_of_le_mul
                          rw[c11_post]
                          set con3 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon3
                          have : c1.val ≤ con3 := by simp_all
                          suffices h : i33.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                          · have := add_le_add this h
                            simp_all
                          · rw[i33_post, UScalar.cast_val_eq, UScalarTy.numBits]
                            suffices h : i32.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                            · have : i32.val % 2 ^ 128 = i32.val := by
                                    apply Nat.mod_eq_of_lt
                                    have : i32.val ≤  2^128-1 := by
                                        apply le_trans h
                                        simp[hcon3]
                                    apply Nat.lt_of_le_pred (by simp) this
                              rw[this]
                              exact h
                            · rw[i32_post, UScalar.cast_val_eq, UScalarTy.numBits]
                              suffices h : i31.val ≤  2^ 64 - 1
                              · have : i31.val % 2 ^ 64 = i31.val := by
                                        apply Nat.mod_eq_of_lt
                                        apply Nat.lt_of_le_pred (by simp) h
                                rw[this]
                                apply le_trans h
                                simp[hcon3]
                              · simp_all
    have  hi41_lt : i41.val ≤  2^ 64 - 1 := by
                    rw[i41_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[c21_post]
                    set con2 := (2 ^ 54).pred * (2 ^ 54).pred + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon2
                    have : c2.val ≤ con2 := by simp_all
                    suffices h : i38.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                    · have := add_le_add this h
                      simp_all
                    · rw[i38_post, UScalar.cast_val_eq, UScalarTy.numBits]
                      suffices h : i37.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                      · have : i37.val % 2 ^ 128 = i37.val := by
                          apply Nat.mod_eq_of_lt
                          have : i37.val ≤  2^128-1 := by
                            apply le_trans h
                            simp[hcon2]
                          apply Nat.lt_of_le_pred (by simp) this
                        rw[this]
                        exact h
                      · rw[i37_post, UScalar.cast_val_eq, UScalarTy.numBits]
                        suffices h : i36.val ≤  2^ 64 - 1
                        · have : i36.val % 2 ^ 64 = i36.val := by
                            apply Nat.mod_eq_of_lt
                            apply Nat.lt_of_le_pred (by simp) h
                          rw[this]
                          apply le_trans h
                          simp[hcon2]
                        · simp_all
    have hi46_lt : i46.val ≤  2^ 64 - 1 := by
              rw[i46_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[c31_post]
              set con1 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon1
              have : c3.val ≤ con1 := by simp_all
              suffices h : i43.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
              · have := add_le_add this h
                simp_all
              · rw[i43_post, UScalar.cast_val_eq, UScalarTy.numBits]
                suffices h : i42.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
                · have : i42.val % 2 ^ 128 = i42.val := by
                    apply Nat.mod_eq_of_lt
                    have : i42.val ≤  2^128-1 := by
                        apply le_trans h
                        simp[hcon1]
                    apply Nat.lt_of_le_pred (by simp) this
                  rw[this]
                  exact h
                · rw[i42_post, UScalar.cast_val_eq, UScalarTy.numBits]
                  suffices h : i41.val ≤  2^ 64 - 1
                  · have : i41.val % 2 ^ 64 = i41.val := by
                        apply Nat.mod_eq_of_lt
                        apply Nat.lt_of_le_pred (by simp) h
                    rw[this]
                    apply le_trans h
                    simp[hcon1]
                  · simp_all
    have  hi51_lt0 : i51.val ≤  (2^ 64 - 2 ^ 51) / 19 := by
        rw[i51_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[c41_post]
        set con := (2 ^ 54).pred * (2 ^ 54).pred + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
        have : c4.val ≤ con := by simp_all
        suffices h : i48.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
        · have := add_le_add this h
          scalar_tac
        · rw[i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
          suffices h : i47.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
          · have : i47.val % 2 ^ 128 = i47.val := by
             apply Nat.mod_eq_of_lt
             have : i47.val ≤  2^128-1 := by
              apply le_trans h
              simp[hcon]
             apply Nat.lt_of_le_pred (by simp) this
            rw[this]
            exact h
          · rw[i47_post, UScalar.cast_val_eq, UScalarTy.numBits]
            suffices h : i46.val ≤  2^ 64 - 1
            · have : i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp) h
              rw[this]
              apply le_trans h
              simp[hcon]
            · simp_all
    have  hi51_lt : i51.val ≤  2^ 64 - 1 := by
     apply le_trans hi51_lt0
     simp
    intro i hi
    interval_cases i
    · simp
      suffices h : i62.val < 2 ^ 51
      · apply lt_trans h
        simp
      · simp[i62_post_1]
        rw[LOW_51_BIT_MASK_spec,
        land_pow_two_sub_one_eq_mod]
        apply Nat.mod_lt
        simp
    · simp
      rw[a7_post]
      simp_all
      rw[
         LOW_51_BIT_MASK_spec,
                land_pow_two_sub_one_eq_mod,
                Nat.shiftRight_eq_div_pow,
                UScalar.cast_val_eq, UScalarTy.numBits,
                UScalar.cast_val_eq, UScalarTy.numBits,
                UScalar.cast_val_eq, UScalarTy.numBits]
      suffices h : (((c0.val % 2 ^ 64) &&& 2 ^ 51 - 1) +
                (i51.val % 2 ^ 64) * 19) / 2 ^ 51 < 2 ^ 54 - (2 ^ 51)
      · have := Nat.mod_lt (c11.val % 2^ 64 % 2 ^ 64) (by simp :0 < 2^ 51)
        have := Nat.add_lt_add this h
        simp at this
        simp
        apply this
      · apply Nat.div_lt_of_lt_mul
        suffices h: i51.val % 2 ^ 64 * 19 < 2 ^ 51 * (2 ^ 52 - 2 ^ 51) - 2 ^ 51
        · rw[land_pow_two_sub_one_eq_mod]
          have := Nat.mod_lt (c0.val % 2^ 64 % 2 ^ 64) (by simp :0 < 2^ 51)
          have := Nat.add_lt_add this h
          simp at this
          simp
          apply lt_trans this
          simp
        · have hi51_mod : i51.val % 2 ^ 64 = i51.val := by
              apply Nat.mod_eq_of_lt
              apply Nat.lt_of_le_pred (by simp)
              simp_all
          rw[hi51_mod]
          have := Nat.lt_succ_of_le hi51_lt0
          have := (Nat.mul_lt_mul_right (by simp: 0<19)).mpr this
          simp[i51_post_1]
          apply lt_trans this
          simp
    · simp_all
      apply lt_trans _ (by simp : 2^ 51 < 2 ^ 54)
      rw[ LOW_51_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod]
      apply Nat.mod_lt
      simp
    · simp_all
      apply lt_trans _ (by simp : 2^ 51 < 2 ^ 54)
      rw[ LOW_51_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod]
      apply Nat.mod_lt
      simp
    · simp_all
      apply lt_trans _ (by simp : 2^ 51 < 2 ^ 54)
      rw[ LOW_51_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod]
      apply Nat.mod_lt
      simp
  · have hi31_lt : i31.val ≤  2^ 64 - 1 := by
      rw[i31_post_1, Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      simp_all
      apply le_trans a1423I
      simp
    have hi36_lt : i36.val ≤  2^ 64 - 1 := by
                          rw[i36_post_1, Nat.shiftRight_eq_div_pow]
                          apply Nat.div_le_of_le_mul
                          rw[c11_post]
                          set con3 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon3
                          have : c1.val ≤ con3 := by simp_all
                          suffices h : i33.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                          · have := add_le_add this h
                            simp_all
                          · rw[i33_post, UScalar.cast_val_eq, UScalarTy.numBits]
                            suffices h : i32.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con3
                            · have : i32.val % 2 ^ 128 = i32.val := by
                                    apply Nat.mod_eq_of_lt
                                    have : i32.val ≤  2^128-1 := by
                                        apply le_trans h
                                        simp[hcon3]
                                    apply Nat.lt_of_le_pred (by simp) this
                              rw[this]
                              exact h
                            · rw[i32_post, UScalar.cast_val_eq, UScalarTy.numBits]
                              suffices h : i31.val ≤  2^ 64 - 1
                              · have : i31.val % 2 ^ 64 = i31.val := by
                                        apply Nat.mod_eq_of_lt
                                        apply Nat.lt_of_le_pred (by simp) h
                                rw[this]
                                apply le_trans h
                                simp[hcon3]
                              · simp_all
    have  hi41_lt : i41.val ≤  2^ 64 - 1 := by
                    rw[i41_post_1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[c21_post]
                    set con2 := (2 ^ 54).pred * (2 ^ 54).pred + 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (19 * (2 ^ 54).pred)) with hcon2
                    have : c2.val ≤ con2 := by simp_all
                    suffices h : i38.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                    · have := add_le_add this h
                      simp_all
                    · rw[i38_post, UScalar.cast_val_eq, UScalarTy.numBits]
                      suffices h : i37.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con2
                      · have : i37.val % 2 ^ 128 = i37.val := by
                          apply Nat.mod_eq_of_lt
                          have : i37.val ≤  2^128-1 := by
                            apply le_trans h
                            simp[hcon2]
                          apply Nat.lt_of_le_pred (by simp) this
                        rw[this]
                        exact h
                      · rw[i37_post, UScalar.cast_val_eq, UScalarTy.numBits]
                        suffices h : i36.val ≤  2^ 64 - 1
                        · have : i36.val % 2 ^ 64 = i36.val := by
                            apply Nat.mod_eq_of_lt
                            apply Nat.lt_of_le_pred (by simp) h
                          rw[this]
                          apply le_trans h
                          simp[hcon2]
                        · simp_all
    have hi46_lt : i46.val ≤  2^ 64 - 1 := by
              rw[i46_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[c31_post]
              set con1 := (2 ^ 54).pred * (19 * (2 ^ 54).pred) + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon1
              have : c3.val ≤ con1 := by simp_all
              suffices h : i43.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
              · have := add_le_add this h
                simp_all
              · rw[i43_post, UScalar.cast_val_eq, UScalarTy.numBits]
                suffices h : i42.val ≤ 2 ^ 51 * (2 ^ 64 - 1) - con1
                · have : i42.val % 2 ^ 128 = i42.val := by
                    apply Nat.mod_eq_of_lt
                    have : i42.val ≤  2^128-1 := by
                        apply le_trans h
                        simp[hcon1]
                    apply Nat.lt_of_le_pred (by simp) this
                  rw[this]
                  exact h
                · rw[i42_post, UScalar.cast_val_eq, UScalarTy.numBits]
                  suffices h : i41.val ≤  2^ 64 - 1
                  · have : i41.val % 2 ^ 64 = i41.val := by
                        apply Nat.mod_eq_of_lt
                        apply Nat.lt_of_le_pred (by simp) h
                    rw[this]
                    apply le_trans h
                    simp[hcon1]
                  · simp_all
    have  hi51_lt0 : i51.val ≤  (2^ 64 - 2 ^ 51) / 19 := by
        rw[i51_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[c41_post]
        set con := (2 ^ 54).pred * (2 ^ 54).pred + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
        have : c4.val ≤ con := by simp_all
        suffices h : i48.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
        · have := add_le_add this h
          scalar_tac
        · rw[i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
          suffices h : i47.val ≤  2 ^ 51 * ((2^ 64 - 2 ^ 51) / 19) - con
          · have : i47.val % 2 ^ 128 = i47.val := by
             apply Nat.mod_eq_of_lt
             have : i47.val ≤  2^128-1 := by
              apply le_trans h
              simp[hcon]
             apply Nat.lt_of_le_pred (by simp) this
            rw[this]
            exact h
          · rw[i47_post, UScalar.cast_val_eq, UScalarTy.numBits]
            suffices h : i46.val ≤  2^ 64 - 1
            · have : i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                apply Nat.lt_of_le_pred (by simp) h
              rw[this]
              apply le_trans h
              simp[hcon]
            · simp_all
    have  hi51_lt : i51.val ≤  2^ 64 - 1 := by
      apply le_trans hi51_lt0
      simp
    · constructor
      · suffices  h:Field51_as_Nat (a7.set 0#usize i62) ≡ Field51_as_Nat a ^ 2  [MOD p]
        · rw[eqk] at res_post_1
          have := Nat.ModEq.pow (2^ (k-1) ) h
          have := Nat.ModEq.trans res_post_1 this
          apply Nat.ModEq.trans this
          rw[← pow_mul]
          have : 2 * 2 ^ (k -1) = 2 ^ ((k -1) +1) := by grind
          rw[this]
          have : (k - 1) + 1 = k:= by grind
          rw[this]
        ·   simp_all[Field51_as_Nat, Finset.sum_range_succ]
            rw[LOW_51_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,]
            simp[UScalar.cast_val_eq, UScalarTy.numBits]
            have : (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
                2 ^ 51 * (c11.val % 2^51 + (c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
                2^(2 * 51) * (c21.val % 2 ^51) +
                2^(3 * 51) * (c31.val % 2^51) +
                2^(4* 51) * (c41.val % 2^51)
                =
              (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
                2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
                2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
                2 ^ (3 * 51) * ((c3.val + i41 % 2 ^ 64) % 2 ^51) +
                2 ^ (4 * 51) * ((c4.val + i46 % 2 ^ 64) % 2 ^51) := by
              calc
              (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
                2 ^ 51 * (c11.val % 2^51 + (c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
                2^(2 * 51) * (c21.val % 2 ^51) +
                2^(3 * 51) * (c31.val % 2^51) +
                2^(4* 51) * (c41.val % 2^51)
                =     (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
                2 ^ 51 * ((c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
                2 ^ 51 * (c11.val % 2^51 ) +
                2^(2 * 51) * (c21.val % 2 ^51) +
                2^(3 * 51) * (c31.val % 2^51) +
                2^(4* 51) * (c41.val % 2^51)
                := by ring
                _ =  (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
                2 ^ 51 * (c11.val % 2^51 ) +
                2 ^ (2 * 51) * (c21.val % 2 ^51) +
                2 ^ (3 * 51) * (c31.val % 2^51) +
                2 ^ (4 * 51) * (c41.val % 2^51)
                := by
                  simp[Nat.shiftRight_eq_div_pow]
                  have := Nat.mod_add_div (c0.val % 2 ^51 + i51.val % 2^64 * 19)  (2 ^ 51)
                  simp at this
                  rw[this]
                _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
                2 ^ 51 * (c11.val % 2^51)  +
                2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
                2 ^ (3 * 51) * (c31.val % 2^51) +
                2 ^ (4 * 51) * (c41.val % 2^51)
                := by
                  simp[c21_post, c2_post, UScalar.cast_val_eq, UScalarTy.numBits]
                _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
                2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
                2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
                2 ^ (3 * 51) * (c31.val % 2^51) +
                2 ^ (4 * 51) * (c41.val % 2^51)
                := by
                  simp[c11_post, c1_post, UScalar.cast_val_eq, UScalarTy.numBits]
                _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
                2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
                2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
                2 ^ (3 * 51) * ((c3.val + i41 % 2 ^ 64) % 2 ^51) +
                2 ^ (4 * 51) * (c41.val % 2^51)
                := by
                  simp[c31_post, c3_post, UScalar.cast_val_eq, UScalarTy.numBits]
                _ = (c0.val % 2 ^51 + i51.val % 2 ^ 64 * 19)  +
                2 ^ 51 * ((c1.val + i31 % 2 ^ 64 ) % 2^51)  +
                2 ^ (2 * 51) * ((c2.val + i36 % 2 ^ 64) % 2 ^51) +
                2 ^ (3 * 51) * ((c3.val + i41 % 2 ^ 64) % 2 ^51) +
                2 ^ (4 * 51) * ((c4.val + i46 % 2 ^ 64) % 2 ^51)
                := by
                  simp[c41_post, c4_post, UScalar.cast_val_eq, UScalarTy.numBits]
            have : (c0.val + i51.val % 2 ^ 64 * 19) % 2 ^ 51 +
                2 ^ 51 * (c11.val % 2^51 + (c0.val % 2 ^51 + i51.val % 2^64 * 19) >>> 51) +
                2^(2 * 51) * (c21.val % 2 ^51) +
                2^(3 * 51) * (c31.val % 2^51) +
                2^(4* 51) * (c41.val % 2^51)
                =
              (c0.val % 2 ^51 + i51.val  * 19)  +
                2 ^ 51 * ((c1.val + i31  ) % 2^51)  +
                2 ^ (2 * 51) * ((c2.val + i36 ) % 2 ^51) +
                2 ^ (3 * 51) * ((c3.val + i41 ) % 2 ^51) +
                2 ^ (4 * 51) * ((c4.val + i46 ) % 2 ^51) := by
              have hi31_mod: i31.val % 2 ^ 64 = i31.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
              have hi36_mod: i36.val % 2 ^ 64 = i36.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
              have hi41_mod: i41.val % 2 ^ 64 = i41.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
              have hi46_mod: i46.val % 2 ^ 64 = i46.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
              have hi51_mod : i51.val % 2 ^ 64 = i51.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
              rw[this, hi31_mod, hi36_mod, hi41_mod, hi46_mod, hi51_mod]
            have eq_mod1: ↑c0 % 2 ^ 51 + ↑i51 * 19 +
            2 ^ 51 * ((↑c1 + ↑i31) % 2 ^ 51) +
            2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
            2 ^ (3 * 51) * ((↑c3 + ↑i41) % 2 ^ 51) +
            2 ^ (4 * 51) * ((↑c4 + ↑i46) % 2 ^ 51)
            ≡ ↑c0 % 2 ^ 51  +
            2 ^ 51 * ((↑c1 + ↑i31) % 2 ^ 51) +
            2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
            2 ^ (3 * 51) * ((↑c3 + ↑i41) % 2 ^ 51) +
            2 ^ (4 * 51) * ((↑c4 + ↑i46) % 2 ^ 51 + 2 ^ 51 * i51.val)  [MOD p] := by
              have key  : 19 ≡ (2:ℕ)^255 [MOD p] := by
                unfold p
                rw [Nat.ModEq]
                norm_num
              have := Nat.ModEq.mul_left i51.val key
              have := Nat.ModEq.add_right (2 ^ 51 * ((↑c1 + ↑i31) % 2 ^ 51) + 2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
            2 ^ (3 * 51) * ((↑c3 + ↑i41) % 2 ^ 51) +
            2 ^ (4 * 51) * ((↑c4 + ↑i46) % 2 ^ 51)) this
              have := Nat.ModEq.add_left (↑c0 % 2 ^ 51) this
              rw[← add_assoc, ← add_assoc, ← add_assoc
              , ← add_assoc] at this
              apply Nat.ModEq.trans this
              have : c0.val % 2 ^ 51 + (i51.val * 2 ^ 255 +
            (2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
            2 ^ (2 * 51) * ((c2.val + i36.val) % 2 ^ 51) +
                2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51) +
              2 ^ (4 * 51) * ((c4.val + i46.val) % 2 ^ 51)))
            = c0.val % 2 ^ 51  +
            2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
            2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
            2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51) +
            2 ^ (4 * 51) * ((c4.val + i46.val) % 2 ^ 51 + 2 ^ 51 * i51.val) := by grind
              rw[this]
            have : i51.val = (c4.val + i46.val)/ 2 ^ 51   := by
                have hi46_mod: i46.val % 2 ^ 64 = i46.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
                rw[i51_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi46_mod, Nat.shiftRight_eq_div_pow]
                simp_all
            have : (c4.val + i46.val) % 2 ^ 51 + 2 ^ 51 * i51.val
            = (c4.val + i46.val) := by
                rw[this]
                apply Nat.mod_add_div
            rw[this] at eq_mod1
            have : c0.val % 2 ^ 51  +
            2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
            2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
            2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51) +
            2 ^ (4 * 51) * ((c4.val + i46.val))
            = c0.val % 2 ^ 51  +
            2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
            2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
            2 ^ (3 * 51) * ((c3.val + i41.val) % 2 ^ 51 +  2 ^ 51 * i46.val) +
            2 ^ (4 * 51) * c4.val  := by grind
            rw[this] at eq_mod1
            have : i46.val = (c3.val + i41.val)/ 2 ^ 51   := by
                have hi41_mod: i41.val % 2 ^ 64 = i41.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
                rw[i46_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi41_mod, Nat.shiftRight_eq_div_pow]
                simp_all
            have : (c3.val + i41.val) % 2 ^ 51 + 2 ^ 51 * i46.val
            = (c3.val + i41.val) := by
                rw[this]
                apply Nat.mod_add_div
            rw[this] at eq_mod1
            have : c0.val % 2 ^ 51  +
            2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
            2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51) +
            2 ^ (3 * 51) * (c3.val + i41.val ) +
            2 ^ (4 * 51) * c4.val
            = c0.val % 2 ^ 51  +
            2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
            2 ^ (2 * 51) * ((↑c2 + ↑i36) % 2 ^ 51 + 2 ^ 51 * i41.val) +
            2 ^ (3 * 51) * c3.val  +
            2 ^ (4 * 51) * c4.val  := by grind
            rw[this] at eq_mod1
            have : i41.val = (c2.val + i36.val)/ 2 ^ 51   := by
                have hi36_mod: i36.val % 2 ^ 64 = i36.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
                rw[i41_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi36_mod, Nat.shiftRight_eq_div_pow]
                simp_all
            have : (c2.val + i36.val) % 2 ^ 51 + 2 ^ 51 * i41.val
            = (c2.val + i36.val) := by
                rw[this]
                apply Nat.mod_add_div
            rw[this] at eq_mod1
            have : c0.val % 2 ^ 51  +
            2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51) +
            2 ^ (2 * 51) * (c2.val + i36.val) +
            2 ^ (3 * 51) * c3.val +
            2 ^ (4 * 51) * c4.val
            = c0.val % 2 ^ 51  +
            2 ^ 51 * ((c1.val + i31.val) % 2 ^ 51 + 2 ^ 51 * i36.val) +
            2 ^ (2 * 51) * c2.val +
            2 ^ (3 * 51) * c3.val  +
            2 ^ (4 * 51) * c4.val  := by grind
            rw[this] at eq_mod1
            have : i36.val = (c1.val + i31.val)/ 2 ^ 51   := by
                have hi31_mod: i31.val % 2 ^ 64 = i31.val := by
                      apply Nat.mod_eq_of_lt
                      apply Nat.lt_of_le_pred (by simp)
                      simp_all
                rw[i36_post_1, UScalar.cast_val_eq, UScalarTy.numBits, hi31_mod, Nat.shiftRight_eq_div_pow]
                simp_all
            have : (c1.val + i31.val) % 2 ^ 51 + 2 ^ 51 * i36.val
            = (c1.val + i31.val) := by
                rw[this]
                apply Nat.mod_add_div
            rw[this] at eq_mod1
            have : c0.val % 2 ^ 51  +
            2 ^ 51 * (c1.val + i31.val) +
            2 ^ (2 * 51) * c2.val +
            2 ^ (3 * 51) * c3.val  +
            2 ^ (4 * 51) * c4.val
            = (c0.val % 2 ^ 51  +  2 ^ 51 * i31.val) +
            2 ^ 51 * c1.val  +
            2 ^ (2 * 51) * c2.val +
            2 ^ (3 * 51) * c3.val +
            2 ^ (4 * 51) * c4.val
              := by grind
            rw[this] at eq_mod1
            have : i31.val = c0.val / 2 ^ 51   := by
                rw[i31_post_1, Nat.shiftRight_eq_div_pow, c0_post]
            have : (c0.val) % 2 ^ 51 + 2 ^ 51 * i31.val
            = c0.val := by
                rw[this]
                apply Nat.mod_add_div
            rw[this] at eq_mod1
            simp_all
            apply Nat.ModEq.trans eq_mod1
            have :=decompose a[0].val a[1].val a[2].val a[3].val a[4].val
            apply Nat.ModEq.symm
            apply Nat.ModEq.trans this
            simp
            apply Nat.ModEq.rfl
      · exact  res_post_2

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.pow2k`**:
- No panic (always returns successfully) when k > 0
- The result, when converted to a natural number, is congruent to the input raised to the (2^k)-th power modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^52
-/


@[progress]
theorem pow2k_spec (a : Array U64 5#usize) (k : U32) (hk : 0 < k.val)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k a k = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52)
    := by
  unfold pow2k
  progress*
  simp_all

end curve25519_dalek.backend.serial.u64.field.FieldElement51
