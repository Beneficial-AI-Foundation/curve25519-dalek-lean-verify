/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.BitList_C
import Curve25519Dalek.Aux

/-! # Spec Theorem for `Scalar52::to_bytes` -- Option C (bridge lemma approach)

This is an alternative proof of `to_bytes_spec` that uses a single Nat-level bridge lemma
instead of BitList step specs. The bridge lemma (`to_bytes_bridge` in `Math.BitList_C`)
takes 32 Nat-level byte hypotheses and proves `U8x32_as_Nat = Scalar52_as_Nat` directly.
-/

set_option linter.style.whitespace false

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52.v_c
attribute [local simp] Array.length_eq

/-! ## Helper: non-overlapping Nat-OR equals addition -/

private lemma testBit_add_mul_pow_low (b q k i : Nat) (hb : b < 2 ^ k) (hi : i < k) :
    (b + 2 ^ k * q).testBit i = b.testBit i := by
  have h1 : (b + 2 ^ k * q) % 2 ^ k = b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have h2 := Nat.testBit_mod_two_pow (b + 2 ^ k * q) k i
  rw [h1] at h2; simp [hi] at h2; exact h2.symm

private lemma testBit_add_mul_pow_high (b q k i : Nat) (hb : b < 2 ^ k) (hi : k ≤ i) :
    (b + 2 ^ k * q).testBit i = (2 ^ k * q).testBit i := by
  set n := i - k
  have hi_eq : i = n + k := by omega
  rw [hi_eq, Nat.testBit_add, Nat.testBit_add]
  congr 1
  rw [Nat.add_mul_div_left _ _ (by positivity : (0 : Nat) < 2 ^ k),
      Nat.div_eq_of_lt hb, Nat.zero_add,
      Nat.mul_div_cancel_left _ (by positivity : (0 : Nat) < 2 ^ k)]

private theorem nat_or_eq_add (a b k : Nat) (ha : a % 2 ^ k = 0) (hb : b < 2 ^ k) :
    a ||| b = a + b := by
  have ha_low : ∀ j, j < k → a.testBit j = false := by
    intro j hj; have h1 := Nat.testBit_mod_two_pow a k j; rw [ha] at h1; simp_all
  have hb_high : ∀ j, j ≥ k → b.testBit j = false := by
    intro j hj
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hj))
  have ha_eq : a = 2 ^ k * (a / 2 ^ k) := by have := Nat.div_add_mod a (2 ^ k); omega
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
  by_cases hi : i < k
  · rw [ha_low i hi, Bool.false_or, ha_eq, Nat.add_comm]
    exact (testBit_add_mul_pow_low b (a / 2 ^ k) k i hb hi).symm
  · rw [hb_high i (by omega), Bool.or_false, ha_eq, Nat.add_comm]
    exact (testBit_add_mul_pow_high b (a / 2 ^ k) k i hb (by omega)).symm

/-! ## Top limb bound -/

private theorem top_limb_lt (a : Array U64 5#usize) (h : Scalar52_as_Nat a < L) :
    (a : List U64)[4]!.val < 2 ^ 48 := by
  unfold Scalar52_as_Nat at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Array.getElem!_Nat_eq] at h
  have : L < 2 ^ 253 := by unfold L; omega
  have h4 : 2 ^ 208 * (a : List U64)[4]!.val ≤
    (a : List U64)[0]!.val + 2 ^ 52 * (a : List U64)[1]!.val +
    2 ^ 104 * (a : List U64)[2]!.val + 2 ^ 156 * (a : List U64)[3]!.val +
    2 ^ 208 * (a : List U64)[4]!.val := by omega
  omega

/-! ## Main theorem -/

set_option maxHeartbeats 4000000 in
@[step]
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧ U8x32_as_Nat result < L ⦄ := by
  unfold to_bytes
  step*
  -- Limb bounds
  have hl0 : (self : List U64)[0]!.val < 2 ^ 52 := by
    have := h 0 (by omega); simp only [Array.getElem!_Nat_eq] at this; exact this
  have hl1 : (self : List U64)[1]!.val < 2 ^ 52 := by
    have := h 1 (by omega); simp only [Array.getElem!_Nat_eq] at this; exact this
  have hl2 : (self : List U64)[2]!.val < 2 ^ 52 := by
    have := h 2 (by omega); simp only [Array.getElem!_Nat_eq] at this; exact this
  have hl3 : (self : List U64)[3]!.val < 2 ^ 52 := by
    have := h 3 (by omega); simp only [Array.getElem!_Nat_eq] at this; exact this
  have hl4 : (self : List U64)[4]!.val < 2 ^ 48 := top_limb_lt self h'
  -- Derive OR byte values
  have h_i16_val : i16.val = i.val / 2 ^ 48 + i14.val * 2 ^ 4 := by
    have h16eq := i16_post1; rw [UScalar.val_or] at h16eq; rw [h16eq]
    have hsr : i13.val = i.val / 2 ^ 48 := by rw [i13_post1, Nat.shiftRight_eq_div_pow]
    have hsl : i15.val = i14.val * 2 ^ 4 := by
      rw [i15_post1, Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt; have := i14.hmax; scalar_tac
    rw [Nat.lor_comm, nat_or_eq_add i15.val i13.val 4
      (by rw [hsl]; omega) (by rw [hsr, i_post]; omega), hsr, hsl]; ring
  have h_i46_val : i46.val = i30.val / 2 ^ 48 + i44.val * 2 ^ 4 := by
    have h46eq := i46_post1; rw [UScalar.val_or] at h46eq; rw [h46eq]
    have hsr : i43.val = i30.val / 2 ^ 48 := by rw [i43_post1, Nat.shiftRight_eq_div_pow]
    have hsl : i45.val = i44.val * 2 ^ 4 := by
      rw [i45_post1, Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt; have := i44.hmax; scalar_tac
    rw [Nat.lor_comm, nat_or_eq_add i45.val i43.val 4
      (by rw [hsl]; omega) (by rw [hsr, i30_post]; omega), hsr, hsl]; ring
  suffices heq : U8x32_as_Nat result = Scalar52_as_Nat self by exact ⟨heq, heq ▸ h'⟩
  -- Convert U8x32_as_Nat to foldr form
  rw [U8x32_as_Nat_eq_foldr]
  -- Substitute array chain to get the concrete list
  subst result_post s31_post s30_post s29_post s28_post s27_post s26_post s25_post s24_post
  subst s23_post s22_post s21_post s20_post s19_post s18_post s17_post s16_post
  subst s15_post s14_post s13_post s12_post s11_post s10_post s9_post s8_post
  subst s7_post s6_post s5_post s4_post s3_post s2_post s1_post
  -- Normalize the nested set operations on the list using set_cons lemmas
  simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq, Array.repeat,
    List.replicate_succ, List.replicate_zero, List.set_cons_zero, List.set_cons_succ]
  -- Now the list is [i2, i4, i6, ..., i72] and foldr reduces
  simp only [List.foldr_cons, List.foldr_nil]
  -- Substitute cast values
  simp only [i2_post, i4_post, i6_post, i8_post, i10_post, i12_post,
    i17_post, i19_post, i21_post, i23_post, i25_post, i27_post, i29_post,
    i32_post, i34_post, i36_post, i38_post, i40_post, i42_post,
    i47_post, i49_post, i51_post, i53_post, i55_post, i57_post, i59_post,
    i62_post, i64_post, i66_post, i68_post, i70_post, i72_post,
    UScalar.cast_val_eq, UScalarTy.numBits, Nat.reducePow]
  -- Normalize shift values
  simp only [i1_post1, i3_post1, i5_post1, i7_post1, i9_post1, i11_post1,
    i18_post1, i20_post1, i22_post1, i24_post1, i26_post1, i28_post1,
    i31_post1, i33_post1, i35_post1, i37_post1, i39_post1, i41_post1,
    i48_post1, i50_post1, i52_post1, i54_post1, i56_post1, i58_post1,
    i61_post1, i63_post1, i65_post1, i67_post1, i69_post1, i71_post1,
    Nat.shiftRight_eq_div_pow, h_i16_val, h_i46_val]
  -- Inline limb values
  simp only [i_post, i14_post, i30_post, i44_post, i60_post, Nat.pow_zero, Nat.div_one]
  -- Now LHS = foldr expression = Horner form of byte values
  -- RHS = Scalar52_as_Nat = sum of limb * 2^(52*k)
  -- Expand Scalar52_as_Nat
  unfold Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reducePow, Nat.reduceMul, one_mul, Array.getElem!_Nat_eq]
  -- Both sides are now explicit Nat expressions involving div/mod of limbs
  -- The LHS is in Horner form: b0 + 256*(b1 + 256*(b2 + ...))
  -- The RHS is: l0 + 2^52*l1 + 2^104*l2 + 2^156*l3 + 2^208*l4
  -- Apply bridge lemma (in foldr/Horner form this might not match directly)
  -- Let's convert Horner form to sum form first
  ring_nf
  -- Now try the bridge lemma
  exact to_bytes_bridge
    (self : List U64)[0]!.val (self : List U64)[1]!.val
    (self : List U64)[2]!.val (self : List U64)[3]!.val
    (self : List U64)[4]!.val
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hl0 hl1 hl2 hl3 hl4
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end curve25519_dalek.backend.serial.u64.scalar.Scalar52.v_c
