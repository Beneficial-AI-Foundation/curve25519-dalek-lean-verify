/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Tactics

/- # Spec Theorem for `FieldElement51::pow2k`

Specification and proof for `FieldElement51::pow2k`.

This function computes the 2^k-th power lof the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

-/


set_option diagnostics.threshold 100000000

open Aeneas
open scoped Aeneas
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
    pow2k.m x y ⦃ prod => prod.val = x.val * y.val ⦄ := by
  sorry


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
    pow2k_loop k' a ⦃ r =>
      Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k) [MOD p] ∧
      (∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by
  sorry

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.pow2k`**:
- No panic (always returns successfully) when k > 0
- The result, when converted to a natural number, is congruent to the input raised to the (2^k)-th power modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^52
-/


@[progress]
theorem pow2k_spec (a : Array U64 5#usize) (k : U32) (hk : 0 < k.val)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    pow2k a k ⦃ r =>
      Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
      (∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
