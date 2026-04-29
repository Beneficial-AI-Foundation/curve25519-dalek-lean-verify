/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Scalar.Scalar.ConditionalSelect
import Curve25519Dalek.Specs.Scalar.ReadLeU64Into
import Curve25519Dalek.Specs.Scalar.Scalar.AsRadix16
import Curve25519Dalek.Specs.Scalar.Scalar.ToRadix2wSizeHint

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_2w`

Converts the 256-bit scalar `self` into a `digits_count`-element signed digit
array in radix `2^w` with `w ∈ {5, 6, 7, 8}`, where each digit satisfies
−2^(w−1) ≤ d < 2^(w−1). The case `w = 4` delegates to `as_radix_16`
(see `AsRadix16.lean`). This file also contains the spec for the inner loop
`as_radix_2w_loop`.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

-- `#setup_aeneas_simps` triggers the hash-command linter; suppress it for this file.
set_option linter.hashCommand false
#setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow

namespace curve25519_dalek.scalar.Scalar

private lemma window_sum_step (N i w : ℕ) :
    N % 2 ^ (w * (i + 1)) =
    N % 2 ^ (w * i) + (N / 2 ^ (w * i) % 2 ^ w) * 2 ^ (w * i) := by
  have hpow : 2 ^ (w * (i + 1)) = 2 ^ (w * i) * 2 ^ w := by
    rw [show w * (i + 1) = w * i + w from by ring, pow_add]
  rw [hpow]
  have h1 := Nat.div_add_mod N (2 ^ (w * i))
  have h2 := Nat.div_add_mod (N / 2 ^ (w * i)) (2 ^ w)
  have h3 := Nat.div_add_mod N (2 ^ (w * i) * 2 ^ w)
  have h4 : N / (2 ^ (w * i) * 2 ^ w) = N / 2 ^ (w * i) / 2 ^ w :=
    (Nat.div_div_eq_div_mul N _ _).symm
  have h5 : N / (2 ^ (w * i) * 2 ^ w) * (2 ^ (w * i) * 2 ^ w) =
            N / 2 ^ (w * i) / 2 ^ w * 2 ^ w * 2 ^ (w * i) := by
    rw [h4]; ring
  grind

private lemma window_sum_mod_eq (N K w : ℕ) :
    ∑ i ∈ Finset.range K, (N / 2 ^ (w * i) % 2 ^ w) * 2 ^ (w * i) =
    N % 2 ^ (w * K) := by
  induction K with
  | zero => simp [Nat.mod_one]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have := window_sum_step N K w
    omega

private lemma window_sum_eq (N K w : ℕ) (hN : N < 2 ^ (w * K)) :
    ∑ i ∈ Finset.range K, (N / 2 ^ (w * i) % 2 ^ w) * 2 ^ (w * i) = N := by
  rw [window_sum_mod_eq N K w, Nat.mod_eq_of_lt hN]

private lemma carry_zero_or_one_2w (coef w : ℕ) (h : coef ≤ 2 ^ w) (hw : 0 < w) :
    (coef + 2 ^ (w - 1)) / 2 ^ w = 0 ∨ (coef + 2 ^ (w - 1)) / 2 ^ w = 1 := by
  set H := 2 ^ (w - 1) with hH
  have h2w : H + H = 2 ^ w := by
    rw [hH]; cases w with
    | zero => omega
    | succ w => simp [pow_succ]; ring
  have hH_pos : 0 < H := Nat.two_pow_pos _
  rw [← h2w] at h ⊢
  rcases Nat.lt_or_ge coef H with hlt | hge
  · left
    rw [Nat.div_eq_zero_iff]; right; omega
  · right
    apply Nat.div_eq_of_lt_le <;> omega

private lemma recenter_in_range_2w (coef w : ℕ) (h : coef ≤ 2 ^ w) (hw : 0 < w) :
    let carry' := (coef + 2 ^ (w - 1)) / 2 ^ w;
    -(2 ^ (w - 1) : ℤ) ≤ (coef : ℤ) - carry' * 2 ^ w ∧
    (coef : ℤ) - carry' * 2 ^ w < 2 ^ (w - 1) := by
  simp only
  set H := 2 ^ (w - 1) with hH
  have h2w : H + H = 2 ^ w := by
    rw [hH]; cases w with
    | zero => omega
    | succ w => simp [pow_succ]; ring
  have hH_pos : 0 < H := Nat.two_pow_pos _
  have hcarry := carry_zero_or_one_2w coef w h hw
  rw [← h2w] at h hcarry ⊢
  have hHH : (↑(H + H) : ℤ) = ↑H + ↑H := by push_cast; ring
  constructor
  · rcases hcarry with h0 | h1
    · rw [h0]
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      have hcoef_nn : (0 : ℤ) ≤ coef := by exact_mod_cast Nat.zero_le coef
      have hH_nn : (0 : ℤ) ≤ H := by exact_mod_cast Nat.zero_le H
      linarith
    · have hge : H ≤ coef := by
        have hm := Nat.div_add_mod (coef + H) (H + H)
        have hrem := Nat.mod_lt (coef + H) (show 0 < H + H by omega)
        rw [h1] at hm; omega
      have hge_Z : (H : ℤ) ≤ coef := by exact_mod_cast hge
      rw [h1]
      simp only [Nat.cast_one, one_mul]
      linarith [hHH]
  · rcases hcarry with h0 | h1
    · have hlt : coef < H := by
        have hm := Nat.div_add_mod (coef + H) (H + H)
        have hrem := Nat.mod_lt (coef + H) (show 0 < H + H by omega)
        rw [h0] at hm; omega
      rw [h0]
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      exact_mod_cast hlt
    · have h_Z : (coef : ℤ) ≤ ↑(H + H) := by exact_mod_cast h
      have hH_pos_Z : (0 : ℤ) < H := by exact_mod_cast hH_pos
      rw [h1]
      simp only [Nat.cast_one, one_mul]
      linarith [hHH]

private lemma U64_and_mask_eq_mod (x mask : Std.U64) (w : ℕ)
    (h_mask : mask.val = 2 ^ w - 1) :
    (x &&& mask).val = x.val % 2 ^ w := by
  rw [UScalar.val_and, h_mask, land_pow_two_sub_one_eq_mod]

private lemma add_mul_pow_mod_pow' (q S e w : ℕ) (hew : w ≤ e) :
    (q + S * 2 ^ e) % 2 ^ w = q % 2 ^ w := by
  have hfact : S * 2 ^ e = 2 ^ w * (S * 2 ^ (e - w)) := by
    have h : 2 ^ e = 2 ^ w * 2 ^ (e - w) := by rw [← pow_add]; congr 1; omega
    calc S * 2 ^ e = S * (2 ^ w * 2 ^ (e - w)) := by rw [h]
      _ = 2 ^ w * (S * 2 ^ (e - w)) := by ring
  rw [Nat.add_mod, hfact, Nat.mul_mod_right, add_zero,
      Nat.mod_eq_of_lt (Nat.mod_lt q (Nat.two_pow_pos w))]

private lemma div_add_mul_pow64 (A B r : ℕ) (hr : r ≤ 64) :
    (A + B * 2 ^ 64) / 2 ^ r = A / 2 ^ r + B * 2 ^ (64 - r) := by
  have hr_pos : 0 < 2 ^ r := Nat.two_pow_pos r
  have hAmod := Nat.div_add_mod A (2 ^ r)
  set q := A / 2 ^ r; set rem := A % 2 ^ r
  have hrem_lt : rem < 2 ^ r := Nat.mod_lt A hr_pos
  have h64r' : 2 ^ (64 - r) * 2 ^ r = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hkey : A + B * 2 ^ 64 = (q + B * 2 ^ (64 - r)) * 2 ^ r + rem := by
    nlinarith [hAmod, Nat.two_pow_pos r]
  rw [hkey]
  apply Nat.div_eq_of_lt_le
  · nlinarith [hrem_lt]
  · nlinarith [hrem_lt]

private lemma add_mul_pow_mod_pow (q S r w : ℕ) (hrw : w ≤ 64 - r) :
    (q + S * 2 ^ (64 - r)) % 2 ^ w = q % 2 ^ w :=
  add_mul_pow_mod_pow' q S (64 - r) w hrw

private lemma div_add_mul_pow_of_lt (A B r n : ℕ) (hA : A < 2 ^ n) (hr_pos : 0 < 2 ^ r) :
    (A + B * 2 ^ n) / (2 ^ n * 2 ^ r) = B / 2 ^ r := by
  have hBmod := Nat.div_add_mod B (2 ^ r)
  set q := B / 2 ^ r; set s := B % 2 ^ r
  have hs_lt : s < 2 ^ r := Nat.mod_lt B hr_pos
  have hn_pos : 0 < 2 ^ n := Nat.two_pow_pos n
  apply Nat.div_eq_of_lt_le
  · nlinarith [hBmod, Nat.two_pow_pos n]
  · nlinarith [hBmod, Nat.two_pow_pos n]

private lemma U64_val_lt (x : Std.U64) : x.val < 2 ^ 64 := by
  have := x.hBounds; scalar_tac

private lemma X64_as_Nat_expand (limbs : Array Std.U64 4#usize) :
    X64_as_Nat limbs =
    limbs[0]!.val + 2 ^ 64 * limbs[1]!.val +
    2 ^ 128 * limbs[2]!.val + 2 ^ 192 * limbs[3]!.val := by
  simp only [X64_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  ring

lemma X64_as_Nat_lt_pow256 (limbs : Array Std.U64 4#usize) :
    X64_as_Nat limbs < 2 ^ 256 := by
  rw [X64_as_Nat_expand]
  have h0 := U64_val_lt limbs[0]!; have h1 := U64_val_lt limbs[1]!
  have h2 := U64_val_lt limbs[2]!; have h3 := U64_val_lt limbs[3]!
  nlinarith

lemma X64_window_single_limb
    (limbs : Array Std.U64 4#usize) (bit_offset w : ℕ)
    (hbo_lt : bit_offset < 256) (hfit : bit_offset % 64 + w ≤ 64) :
    X64_as_Nat limbs / 2 ^ bit_offset % 2 ^ w =
    limbs[bit_offset / 64]!.val / 2 ^ (bit_offset % 64) % 2 ^ w := by
  set k := bit_offset / 64; set r := bit_offset % 64
  have hk : bit_offset = 64 * k + r := (Nat.div_add_mod bit_offset 64).symm
  have hk_lt : k < 4 := by simp [k]; omega
  have hr_lt : r < 64 := Nat.mod_lt _ (by norm_num)
  have hrw : w ≤ 64 - r := by omega
  have hL : ∀ j : ℕ, limbs[j]!.val < 2 ^ 64 := fun j => U64_val_lt _
  rw [X64_as_Nat_expand, hk, pow_add]
  interval_cases k
  · simp only [show (64:ℕ)*0=0 from rfl, pow_zero, one_mul]
    rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
        limbs[0]!.val + (limbs[1]!.val + 2^64*(limbs[2]!.val + 2^64*limbs[3]!.val)) * 2^64
        from by ring]
    rw [div_add_mul_pow64 _ _ r (by omega)]
    exact add_mul_pow_mod_pow' _ _ (64-r) w hrw
  · simp only [show (64:ℕ)*1=64 from rfl]
    rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
        limbs[0]!.val + (limbs[1]!.val + (limbs[2]!.val + 2^64*limbs[3]!.val) * 2^64) * 2^64
        from by ring]
    rw [div_add_mul_pow_of_lt limbs[0]!.val _ r 64 (hL 0) (Nat.two_pow_pos r)]
    rw [div_add_mul_pow64 _ _ r (by omega)]
    exact add_mul_pow_mod_pow' _ _ (64-r) w hrw
  · simp only [show (64:ℕ)*2=128 from rfl]
    rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
        (limbs[0]!.val + 2^64*limbs[1]!.val) +
        (limbs[2]!.val + limbs[3]!.val * 2^64) * 2^128 from by ring]
    rw [div_add_mul_pow_of_lt _ _ r 128
        (by nlinarith [hL 0, hL 1]) (Nat.two_pow_pos r)]
    rw [show (limbs[2]!.val + limbs[3]!.val * 2^64) = limbs[2]!.val + limbs[3]!.val * 2^64 from rfl]
    rw [div_add_mul_pow64 _ _ r (by omega)]
    exact add_mul_pow_mod_pow' _ _ (64-r) w hrw
  · simp only [show (64:ℕ)*3=192 from rfl]
    rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
        (limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val) +
        limbs[3]!.val * 2^192 from by ring]
    rw [div_add_mul_pow_of_lt _ _ r 192
        (by nlinarith [hL 0, hL 1, hL 2]) (Nat.two_pow_pos r)]

private lemma X64_window_k3
    (limbs : Array Std.U64 4#usize) (bit_offset w : ℕ)
    (hk3 : bit_offset / 64 = 3) :
    X64_as_Nat limbs / 2 ^ bit_offset % 2 ^ w =
    limbs[3]!.val / 2 ^ (bit_offset % 64) % 2 ^ w := by
  set r := bit_offset % 64
  have hk : bit_offset = 192 + r := by
    have := Nat.div_add_mod bit_offset 64
    rw [hk3] at this; omega
  have hL : ∀ j : ℕ, limbs[j]!.val < 2 ^ 64 := fun j => U64_val_lt _
  rw [X64_as_Nat_expand, hk, show 192 + r = 64 * 3 + r from by ring, pow_add]
  simp only [show (64:ℕ)*3=192 from rfl]
  rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
      (limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val) +
      limbs[3]!.val * 2^192 from by ring]
  rw [div_add_mul_pow_of_lt _ _ r 192
      (by nlinarith [hL 0, hL 1, hL 2]) (Nat.two_pow_pos r)]

private lemma X64_window_cross_limb
    (limbs : Array Std.U64 4#usize) (bit_offset w : ℕ)
    (hbo_lt : bit_offset < 192) (hcross : bit_offset % 64 + w > 64) (hw_le : w ≤ 64) :
    X64_as_Nat limbs / 2 ^ bit_offset % 2 ^ w =
    (limbs[bit_offset / 64]!.val / 2 ^ (bit_offset % 64) +
     limbs[bit_offset / 64 + 1]!.val * 2 ^ (64 - bit_offset % 64)) % 2 ^ w := by
  set k := bit_offset / 64; set r := bit_offset % 64
  have hk : bit_offset = 64 * k + r := (Nat.div_add_mod bit_offset 64).symm
  have hk_lt3 : k < 3 := by simp [k]; omega
  have hr_lt : r < 64 := Nat.mod_lt _ (by norm_num)
  have hL : ∀ j : ℕ, limbs[j]!.val < 2 ^ 64 := fun j => U64_val_lt _
  rw [X64_as_Nat_expand, hk, pow_add]
  interval_cases k
  · simp only [show (64:ℕ)*0=0 from rfl, pow_zero, one_mul]
    rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
        limbs[0]!.val + (limbs[1]!.val + 2^64*(limbs[2]!.val + 2^64*limbs[3]!.val)) * 2^64
        from by ring]
    rw [div_add_mul_pow64 _ _ r (by omega)]
    rw [show (limbs[1]!.val + 2^64*(limbs[2]!.val + 2^64*limbs[3]!.val)) * 2^(64-r) =
        limbs[1]!.val * 2^(64-r) + (limbs[2]!.val + 2^64*limbs[3]!.val) * 2^(128-r) from by
          have h128 : (2:ℕ)^(128-r) = 2^64 * 2^(64-r) := by rw [← pow_add]; congr 1; omega
          rw [h128]; ring]
    rw [show limbs[0]!.val / 2^r + (limbs[1]!.val * 2^(64-r) +
        (limbs[2]!.val + 2^64*limbs[3]!.val) * 2^(128-r)) =
        (limbs[0]!.val / 2^r + limbs[1]!.val * 2^(64-r)) +
        (limbs[2]!.val + 2^64*limbs[3]!.val) * 2^(128-r) from by ring]
    rw [add_mul_pow_mod_pow' _ _ (128-r) w (by omega)]
  · simp only [show (64:ℕ)*1=64 from rfl]
    rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
        limbs[0]!.val + (limbs[1]!.val + (limbs[2]!.val + 2^64*limbs[3]!.val) * 2^64) * 2^64
        from by ring]
    rw [div_add_mul_pow_of_lt limbs[0]!.val _ r 64 (hL 0) (Nat.two_pow_pos r)]
    rw [div_add_mul_pow64 _ _ r (by omega)]
    rw [show (limbs[2]!.val + 2^64*limbs[3]!.val) * 2^(64-r) =
        limbs[2]!.val * 2^(64-r) + limbs[3]!.val * 2^(128-r) from by
          have h128 : (2:ℕ)^(128-r) = 2^64 * 2^(64-r) := by rw [← pow_add]; congr 1; omega
          rw [h128]; ring]
    rw [show limbs[1]!.val / 2^r + (limbs[2]!.val * 2^(64-r) + limbs[3]!.val * 2^(128-r)) =
        (limbs[1]!.val / 2^r + limbs[2]!.val * 2^(64-r)) + limbs[3]!.val * 2^(128-r) from by ring]
    rw [add_mul_pow_mod_pow' _ _ (128-r) w (by omega)]
  · simp only [show (64:ℕ)*2=128 from rfl]
    rw [show limbs[0]!.val + 2^64*limbs[1]!.val + 2^128*limbs[2]!.val + 2^192*limbs[3]!.val =
        (limbs[0]!.val + 2^64*limbs[1]!.val) +
        (limbs[2]!.val + limbs[3]!.val * 2^64) * 2^128 from by ring]
    rw [div_add_mul_pow_of_lt _ _ r 128
        (by nlinarith [hL 0, hL 1]) (Nat.two_pow_pos r)]
    rw [div_add_mul_pow64 _ _ r (by omega)]

private lemma bit_extraction_correct
    (scalar64x4 : Array Std.U64 4#usize)
    (w : Std.Usize) (window_mask : Std.U64) (i : Std.Usize)
    (hw_lo : 5 ≤ w.val) (hw_hi : w.val ≤ 8)
    (h_mask : window_mask.val = 2 ^ w.val - 1)
    (hi_lt : i.val < (255 + w.val) / w.val)
    (bit_buf : Std.U64)
    (h_buf : (bit_buf.val = scalar64x4[(w.val * i.val) / 64]!.val / 2 ^ ((w.val * i.val) % 64) ∧
              ((w.val * i.val) % 64 + w.val ≤ 64 ∨ (w.val * i.val) / 64 = 3)) ∨
             ((w.val * i.val) / 64 < 3 ∧
              (w.val * i.val) % 64 + w.val > 64 ∧
              bit_buf.val = scalar64x4[(w.val * i.val) / 64]!.val / 2 ^ ((w.val * i.val) % 64) |||
                            scalar64x4[(w.val * i.val) / 64 + 1]!.val *
                              2 ^ (64 - (w.val * i.val) % 64))) :
    (bit_buf &&& window_mask).val =
    X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val) % 2 ^ w.val := by
  rw [U64_and_mask_eq_mod _ _ w.val h_mask]
  have hbo_lt : w.val * i.val < 256 := by
    have hw_pos : 0 < w.val := by omega
    nlinarith [Nat.mul_div_le i.val w.val, Nat.div_mul_le_self (255 + w.val) w.val]
  set bo := w.val * i.val
  rcases h_buf with ⟨h_single, h_fit_or_k3⟩ | ⟨hk_lt3, hcross_cond, h_cross⟩
  · rw [h_single]
    rcases h_fit_or_k3 with hfit | hk3
    · exact (X64_window_single_limb scalar64x4 bo w.val hbo_lt hfit).symm
    · have hk3' : bo / 64 = 3 := hk3
      rw [hk3']
      exact (X64_window_k3 scalar64x4 bo w.val hk3).symm
  · set k := bo / 64; set r := bo % 64
    have hcross_bo : bo < 192 := by
      have hd : bo / 64 < 3 := hk_lt3
      have h1 := Nat.div_add_mod bo 64
      have h2 := Nat.mod_lt bo (show 0 < 64 by norm_num)
      nlinarith [Nat.div_mul_le_self bo 64]
    have hlo_lt : scalar64x4[k]!.val / 2 ^ r < 2 ^ (64 - r) := by
      apply Nat.div_lt_of_lt_mul
      have hv := U64_val_lt scalar64x4[k]!
      calc scalar64x4[k]!.val < 2 ^ 64 := hv
        _ = 2 ^ r * 2 ^ (64 - r) := by rw [← pow_add]; congr 1; omega
    rw [h_cross, or_mul_pow_two_eq_add _ _ (64 - r) hlo_lt]
    exact (X64_window_cross_limb scalar64x4 bo w.val hcross_bo hcross_cond (by omega)).symm

private lemma lt_digits_count_of_bo_le (i w : ℕ) (hw_pos : 0 < w) (h : i * w ≤ 255) :
    i < (255 + w) / w := by
  have h1 : i ≤ 255 / w := by
    rw [Nat.le_div_iff_mul_le hw_pos, Nat.mul_comm]
    grind
  have h2 : (255 + w) / w = 255 / w + 1 := Nat.add_div_right 255 hw_pos
  omega

private lemma mod_add_le_of_mod_lt_sub (a b n : ℕ) (h : a * b % n < n - b) :
    b * a % n + b ≤ n := by
  rw [mul_comm b a]; omega

private lemma bit_offset_le_255 (i K w : ℕ)
    (hi_lt : i < K) (hK_le : K * w ≤ 255 + w) : i * w ≤ 255 := by
  have h1 : (i + 1) * w ≤ K * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hi_lt)
  nlinarith

private lemma pow_succ_half (w : ℕ) : 2 ^ (w + 1) / 2 = 2 ^ w := by
  rw [pow_succ]
  grind

private lemma inv_step_2w
    (N w i : ℕ)
    (carry_old carry_new window_i : ℕ) (S : ℤ) (digit_i : ℤ)
    (h_window : window_i = N / 2 ^ (w * i) % 2 ^ w)
    (h_inv : S + (carry_old : ℤ) * (2 ^ w) ^ i = ↑(N % 2 ^ (w * i)))
    (h_digit : digit_i = (carry_old : ℤ) + window_i - carry_new * 2 ^ w) :
    S + (2 ^ w : ℤ) ^ i * digit_i + (carry_new : ℤ) * (2 ^ w) ^ (i + 1) =
    ↑(N % 2 ^ (w * (i + 1))) := by
  have hstep_nat := window_sum_step N i w
  have hstep : (↑(N % 2 ^ (w * (i + 1))) : ℤ) =
               ↑(N % 2 ^ (w * i)) + ↑window_i * (2 ^ w) ^ i := by
    have key : N % 2 ^ (w * (i + 1)) = N % 2 ^ (w * i) + window_i * 2 ^ (w * i) := by
      rw [hstep_nat, h_window]
    have h := congr_arg (Int.ofNat) key
    push_cast [← pow_mul] at h ⊢
    linarith
  set P := (2 ^ w : ℤ) ^ i with hP
  have h_pow_succ : (2 ^ w : ℤ) ^ (i + 1) = P * 2 ^ w := pow_succ _ _
  have h_ring : S + digit_i * P + carry_new * (P * 2 ^ w) =
                S + carry_old * P + ↑window_i * P := by
    rw [h_digit]; ring
  rw [hstep, h_pow_succ]
  linarith [h_inv, h_ring]

@[step]
private lemma I8x64_update_get (arr : Array Std.I8 64#usize) (j : Usize)
    (v : Std.I8) (hj : j.val < 64) :
    Array.update arr j v ⦃ (arr' : Array Std.I8 64#usize) =>
      (∀ (k : ℕ), k ≠ j.val → (arr')[k]! = arr[k]!) ∧
      (arr')[j.val]! = v ⦄ := by
  have hbound : j.val < arr.length := by scalar_tac
  apply spec_mono (Array.update_spec arr j v hbound)
  intro arr' harr'
  subst harr'
  constructor
  · intro k hk
    simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
    exact List.getElem!_set_ne arr.val j.val k v (Or.inl (Ne.symm hk))
  · simp only [Array.getElem!_Nat_eq, Array.set_val_eq]
    exact List.getElem!_set arr.val j.val v (by scalar_tac)

private lemma bounds_step_2w
    (digits a : Array Std.I8 64#usize) (i w : ℕ)
    (v : Std.I8)
    (hv_lo : -(2 ^ (w - 1) : ℤ) ≤ v.val) (hv_hi : v.val < 2 ^ (w - 1))
    (ha_i : a[i]! = v)
    (ha_pref : ∀ j < i, (a[j]! : Std.I8).val = (digits[j]!).val)
    (h_bounds : ∀ j < i,
        -(2 ^ (w - 1) : ℤ) ≤ (digits[j]!).val ∧ (digits[j]!).val < 2 ^ (w - 1)) :
    ∀ j < i + 1,
        -(2 ^ (w - 1) : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val < 2 ^ (w - 1) := by
  intro j hj
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
  · rw [ha_pref j hjlt]; exact h_bounds j hjlt
  · rw [ha_i]; exact ⟨hv_lo, hv_hi⟩

private lemma tail_step_2w
    (digits a : Array Std.I8 64#usize) (i : ℕ)
    (ha_later : ∀ j, i + 1 ≤ j → j < 64 → (a[j]! : Std.I8).val = (digits[j]!).val)
    (h_tail : ∀ j, i ≤ j → j < 64 → (digits[j]! : Std.I8).val = 0) :
    ∀ j, i + 1 ≤ j → j < 64 → (a[j]! : Std.I8).val = 0 := by
  intro j hj1 hj2
  rw [ha_later j hj1 hj2]
  exact h_tail j (by omega) hj2


set_option maxHeartbeats 4000000 in
-- The proof performs a full induction over the loop iterations, with three
-- large case splits per step; the budget reflects the accumulated cost.
private theorem as_radix_2w_loop_spec_strong
    (iter : core.ops.range.Range Std.Usize)
    (w : Std.Usize)
    (scalar64x4 : Array Std.U64 4#usize)
    (radix window_mask : Std.U64)
    (carry : Std.U64)
    (digits : Array Std.I8 64#usize)
    (K : ℕ)
    (N : ℕ)
    (hw_lo : 5 ≤ w.val) (hw_hi : w.val ≤ 8)
    (h_radix : radix.val = 2 ^ w.val)
    (h_mask : window_mask.val = 2 ^ w.val - 1)
    (h_N : N = X64_as_Nat scalar64x4)
    (h_N_lt : N < 2 ^ (w.val * K))
    (hK_le64 : K ≤ 64)
    (hK_le_digits : K * w.val ≤ 255 + w.val)
    (h_end : iter.end.val = K)
    (h_start : iter.start.val ≤ K)
    (h_inv : ∑ j ∈ Finset.range iter.start.val, (2 ^ w.val : ℤ) ^ j * (digits[j]!).val
                + (carry.val : ℤ) * (2 ^ w.val) ^ iter.start.val
                = ↑(N % 2 ^ (w.val * iter.start.val)))
    (h_carry : carry.val ≤ 1)
    (h_bounds : ∀ j < iter.start.val,
        -(2 ^ (w.val - 1) : ℤ) ≤ (digits[j]!).val ∧ (digits[j]!).val < 2 ^ (w.val - 1))
    (h_tail : ∀ j, iter.start.val ≤ j → j < 64 → (digits[j]! : Std.I8).val = 0) :
    as_radix_2w_loop iter w scalar64x4 radix window_mask carry digits ⦃ result =>
      ∑ j ∈ Finset.range K, (2 ^ w.val : ℤ) ^ j * (result.2[j]!).val
      + (result.1.val : ℤ) * (2 ^ w.val) ^ K = ↑N ∧
      result.1.val ≤ 1 ∧
      (∀ j < K,
        -(2 ^ (w.val - 1) : ℤ) ≤ (result.2[j]!).val ∧
        (result.2[j]!).val < 2 ^ (w.val - 1)) ∧
      (∀ j, K ≤ j → j < 64 → (result.2[j]! : Std.I8).val = 0) ⦄ := by
  unfold as_radix_2w_loop
  obtain ⟨o, iter1, h_next, h_none_branch, h_some_branch⟩ :=
  Insts.SubtleConditionallySelectable.next_spec iter
  rw [h_next, bind_tc_ok]
  match o with
  | none =>
    have hge : ¬ iter.start.val < iter.end.val := by
      intro hlt
      exact absurd (h_some_branch hlt).1 (by simp only [reduceCtorEq, not_false_eq_true])
    have hi_eq : iter.start.val = K := by rw [h_end] at hge; omega
    rw [spec_ok]
    refine ⟨?_, h_carry, ?_, ?_⟩
    · have hmod : N % 2 ^ (w.val * K) = N := Nat.mod_eq_of_lt h_N_lt
      have h := h_inv
      rw [hi_eq, hmod] at h
      exact_mod_cast h
    · intro j hj
      exact h_bounds j (by rwa [hi_eq])
    · intro j hj1 hj2
      exact h_tail j (hi_eq ▸ hj1) hj2
  | some i =>
    have hlt : iter.start.val < iter.end.val := by
      by_contra hge
      exact absurd (h_none_branch hge).1 (by simp only [reduceCtorEq, not_false_eq_true])
    obtain ⟨hi_eq_some, hiter1_start, hiter1_end⟩ := h_some_branch hlt
    have hi_val : i.val = iter.start.val := by
      have h : some i = some iter.start := hi_eq_some
      exact congrArg UScalar.val (Option.some.inj h)
    have hi_lt_K : i.val < K := by
      rw [hi_val, ← h_end]
      exact hlt
    have hi_lt_64 : i.val < 64 := by agrind
    have hw_pos : 0 < w.val := by agrind
    step as ⟨bit_offset, hbit_offset⟩
    step as ⟨u64_idx, hu64_idx⟩
    step as ⟨bit_idx, hbit_idx⟩
    step with @UScalar.sub_spec .Usize 64#usize w (by agrind) as ⟨i1, hi1⟩
    have hbit_offset_val : bit_offset.val = i.val * w.val := by agrind
    have hu64_val : u64_idx.val = i.val * w.val / 64 := by agrind
    have hbit_val : bit_idx.val = i.val * w.val % 64 := by agrind
    have hi1_val : i1.val = 64 - w.val := by agrind
    have hbo_le : i.val * w.val ≤ 255 :=
      bit_offset_le_255 i.val K w.val hi_lt_K hK_le_digits
    have hu64_lt : u64_idx.val < 4 := by
      rw [hu64_val]
      clear *- hbo_le
      agrind
    have hi_lt_digits : i.val < (255 + w.val) / w.val :=
      lt_digits_count_of_bo_le i.val w.val hw_pos hbo_le
    have h2w : 2 ^ w.val ≤ 256 := Nat.pow_le_pow_right (by norm_num) hw_hi
    have h_bound : (2 : ℤ) ^ (w.val - 1) ≤ 128 := by
      have hnat : (2:ℕ) ^ (w.val - 1) ≤ 128 :=
        calc (2:ℕ) ^ (w.val - 1) ≤ 2^7 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 128 := by norm_num
      exact_mod_cast hnat
    by_cases h_fit : bit_idx.val < i1.val
    · have h_cmp : bit_idx < i1 := h_fit
      simp only [h_cmp, ↓reduceIte, Array.getElem!_Nat_eq]
      step as ⟨limb, hlimb⟩
      step as ⟨bit_buf1, hbit_buf1⟩
      have hbuf1_val : bit_buf1.val = scalar64x4[u64_idx.val]!.val / 2 ^ bit_idx.val := by
        simp only [hbit_buf1, hlimb]
        clear *-
        scalar_tac
      have h_buf_cond :
              (bit_buf1.val = scalar64x4[(w.val * i.val) / 64]!.val / 2 ^ ((w.val * i.val) % 64) ∧
              ((w.val * i.val) % 64 + w.val ≤ 64 ∨ (w.val * i.val) / 64 = 3)) ∨
              ((w.val * i.val) / 64 < 3 ∧
              (w.val * i.val) % 64 + w.val > 64 ∧
              bit_buf1.val = scalar64x4[(w.val * i.val) / 64]!.val / 2 ^ ((w.val * i.val) % 64) |||
                              scalar64x4[(w.val * i.val) / 64 + 1]!.val *
                                2 ^ (64 - (w.val * i.val) % 64)) := by
        left
        refine ⟨?_, Or.inl ?_⟩
        · rw [hbuf1_val, hu64_val, hbit_val]
          conv_rhs => rw [mul_comm]
        · exact mod_add_le_of_mod_lt_sub i.val w.val 64
            (by rw [hbit_val, hi1_val] at h_fit; exact h_fit)
      have h_window : bit_buf1.val % 2 ^ w.val =
              X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val) % 2 ^ w.val := by
        have := bit_extraction_correct scalar64x4 w window_mask i hw_lo hw_hi h_mask
              hi_lt_digits bit_buf1 h_buf_cond
        clear *- this h_mask
        rw [U64_and_mask_eq_mod _ _ w.val h_mask] at this
        exact this
      step as ⟨i2, hi2, hi2_bv⟩
      have h_window2 : i2.val = X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val) % 2 ^ w.val := by
        rw [hi2, UScalar.val_and, h_mask, land_pow_two_sub_one_eq_mod, h_window]
      step as ⟨coef, hcoef⟩
      · grind
      have hcoef_val : coef.val = carry.val + i2.val := by scalar_tac
      have hcoef_le : coef.val ≤ 2 ^ w.val := by
        rw [hcoef_val, h_window2]
        have := Nat.mod_lt (X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val)) (Nat.two_pow_pos w.val)
        clear *- h_carry this
        grind
      step as ⟨i3, hi3⟩
      have hi3_val : i3.val = 2 ^ (w.val - 1) := by
        have h1 : i3.val = radix.val / 2 := by scalar_tac
        rw [h1, h_radix]
        cases hw : w.val with
        | zero => omega
        | succ w' =>
            rw [pow_succ_half w']
            simp only [add_tsub_cancel_right]
      step as ⟨i4, hi4⟩
      have hi4_val : i4.val = coef.val + 2 ^ (w.val - 1) := by
        have h1 : i4.val = coef.val + i3.val := by scalar_tac
        rw [h1, hi3_val]
      step as ⟨carry1, hcarry1⟩
      have hcarry1_val : carry1.val = (coef.val + 2 ^ (w.val - 1)) / 2 ^ w.val := by
        have h1 : carry1.val = i4.val / 2 ^ w.val := by
          simp only [hcarry1, Nat.shiftRight_eq_div_pow]
        rw [h1, hi4_val]
      have hcarry1_le : carry1.val ≤ 1 := by
        have := carry_zero_or_one_2w coef.val w.val hcoef_le hw_pos
        omega
      step as ⟨i5, hi5⟩
      have hi5_val : i5.val = (coef.val : ℤ) := by
        rw [hi5]
        apply UScalar.hcast_inBounds_spec .I64
        simp only [IScalar.max]
        grind
      step as ⟨i6, hi6⟩
      have hi6_val : i6.val = carry1.val * 2 ^ w.val := by
        have hbound : carry1.val * 2 ^ w.val < U64.size := by
          simp only [U64.size]; scalar_tac
        have heq : carry1.val <<< w.val % U64.size = carry1.val * 2 ^ w.val := by
          rw [Nat.shiftLeft_eq]
          apply Nat.mod_eq_of_lt hbound
        linarith [show i6.val = carry1.val <<< w.val % U64.size from by scalar_tac, heq]
      step as ⟨i7, hi7⟩
      have hi7_val : i7.val = (carry1.val : ℤ) * 2 ^ w.val := by
        rw [hi7]
        have hi6_bound : i6.val ≤ 2 ^ w.val := by
              rw [hi6_val]; grind only [usr Nat.pow_pos, usr ScalarTac.le_mul_lt_le]
        have hcast : (UScalar.hcast .I64 i6).val = (i6.val : ℤ) := by
          apply UScalar.hcast_inBounds_spec .I64
          simp only [IScalar.max]
          grind only [usr ScalarTac.IScalar.bounds, = Nat.shiftLeft_eq, = IScalarTy.I64_numBits_eq]
        rw [hcast, hi6_val]
        push_cast
        ring
      step as ⟨i8, hi8⟩
      have hi8_val : i8.val = (coef.val : ℤ) - (carry1.val : ℤ) * 2 ^ w.val := by
        simp only [hi8, hi5_val, hi7_val]
      have h_digit_rng := recenter_in_range_2w coef.val w.val hcoef_le hw_pos
      have h_digit_lo : -(2 ^ (w.val - 1) : ℤ) ≤ i8.val := by
        rw [hi8_val, hcarry1_val, hcoef_val, h_window2]
        have := h_digit_rng.1
        simp_all only [Array.getElem!_Nat_eq, Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat,
        not_lt, reduceCtorEq, false_and, imp_false, not_le,  and_self,
        imp_self, Option.some.injEq, Nat.add_div_right, Order.lt_add_one_iff, UScalar.lt_equiv,
        UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, gt_iff_lt, UScalar.val_and,
        Nat.and_two_pow_sub_one_eq_mod, Nat.cast_add, Int.natCast_ediv, Int.natCast_shiftRight,
        neg_le_sub_iff_le_add]
      have h_digit_hi : i8.val < 2 ^ (w.val - 1) := by
        rw [hi8_val, hcarry1_val, hcoef_val, h_window2]
        have := h_digit_rng.2
        simp_all only [Array.getElem!_Nat_eq, Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat,
        not_lt, reduceCtorEq, false_and, imp_false, not_le,  and_self,
        imp_self, Option.some.injEq, Nat.add_div_right, Order.lt_add_one_iff, UScalar.lt_equiv,
        UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, gt_iff_lt, UScalar.val_and,
        Nat.and_two_pow_sub_one_eq_mod, Nat.cast_add, Int.natCast_ediv, Int.natCast_shiftRight,
         neg_le_sub_iff_le_add]
      step as ⟨i9, hi9⟩
      have hi9_val : i9.val = i8.val := by
        have hspec := IScalar.cast_inBounds_spec .I8 i8 (by
          simp only [IScalar.min, IScalar.max]
          norm_num
          grind)
        simp only [lift, spec_ok] at hspec
        clear *- hi9 hspec
        rw [hi9]
        exact hspec
      step with I8x64_update_get as ⟨a, ha_other, ha_i⟩
      have hiter2_start : iter1.start.val = i.val + 1 := by omega
      have hiter2_end : iter1.end = iter.end := hiter1_end
      have ha_pref : ∀ j < i.val, (a[j]! : Std.I8).val = (digits[j]!).val := by
        intro j hj
        simp only [Array.getElem!_Nat_eq, ha_other j (by omega)]
      have ha_later : ∀ j, i.val + 1 ≤ j → j < 64 →
          (a[j]! : Std.I8).val = (digits[j]!).val := by
        intro j hj1 _
        simp only [Array.getElem!_Nat_eq, ha_other j (by omega)]
      have h_inv' :
              ∑ j ∈ Finset.range iter1.start.val, (2 ^ w.val : ℤ) ^ j * (a[j]!).val
              + (carry1.val : ℤ) * (2 ^ w.val) ^ iter1.start.val
              = ↑(N % 2 ^ (w.val * iter1.start.val)) := by
            rw [hiter2_start]
            have h_pref_sum :
                ∑ j ∈ Finset.range i.val, (2 ^ w.val : ℤ) ^ j * (a[j]!).val =
                ∑ j ∈ Finset.range i.val, (2 ^ w.val : ℤ) ^ j * (digits[j]!).val := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [ha_pref j (Finset.mem_range.mp hj)]
            rw [Finset.sum_range_succ, ha_i, hi9_val, h_pref_sum]
            apply inv_step_2w N w.val i.val carry.val carry1.val
             (N / 2 ^ (w.val * i.val) % 2 ^ w.val)
              (∑ j ∈ Finset.range i.val, (2 ^ w.val) ^ j * (digits[j]!).val) i8.val
            · rfl
            · grind
            · grind
      have h_bounds' :
              ∀ j < iter1.start.val,
                -(2 ^ (w.val - 1) : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val < 2 ^ (w.val - 1) := by
        rw [hiter2_start]
        exact bounds_step_2w digits a i.val w.val i9
          (by rw [hi9_val]; exact h_digit_lo) (by rw [hi9_val]; exact h_digit_hi)
          ha_i ha_pref (fun j hj => h_bounds j (hi_val ▸ hj))
      have h_tail' :
              ∀ j, iter1.start.val ≤ j → j < 64 → (a[j]! : Std.I8).val = 0 := by
        rw [hiter2_start]
        exact tail_step_2w digits a i.val ha_later (fun j hj => h_tail j (hi_val ▸ hj))
      apply spec_mono
        (as_radix_2w_loop_spec_strong iter1 w scalar64x4 radix window_mask carry1 a
          K N hw_lo hw_hi h_radix h_mask h_N h_N_lt hK_le64 hK_le_digits
          (by rw [hiter2_end]; exact h_end)
          (by rw [hiter2_start, hi_val]; omega)
          h_inv' hcarry1_le h_bounds' h_tail')
      clear *-
      intro result hresult
      simp at hresult
      simp only [hresult, true_and]
      have := hresult.right.right
      apply this
    · -- Case 2 & 3: bit_idx ≥ i1 (= 64 - w)
      have h_ncmp : ¬ bit_idx < i1 := by
        intro h; exact h_fit h
      simp only [h_ncmp]
      by_cases h_last : u64_idx = 3#usize
      · simp only [h_last, ↓reduceIte, Array.getElem!_Nat_eq]
        step as ⟨limb, hlimb⟩
        step as ⟨bit_buf2, hbit_buf2⟩
        have hbuf2_val : bit_buf2.val = scalar64x4[u64_idx.val]!.val / 2 ^ bit_idx.val := by
          simp only [hbit_buf2, hlimb]
          scalar_tac
        have h_buf_cond :
                  (bit_buf2.val =
                  scalar64x4[(w.val * i.val) / 64]!.val / 2 ^ ((w.val * i.val) % 64) ∧
                  ((w.val * i.val) % 64 + w.val ≤ 64 ∨ (w.val * i.val) / 64 = 3)) ∨
                  ((w.val * i.val) / 64 < 3 ∧
                  (w.val * i.val) % 64 + w.val > 64 ∧
                  bit_buf2.val = scalar64x4[(w.val * i.val) / 64]!.val / 2 ^ ((w.val * i.val) % 64)
                    ||| scalar64x4[(w.val * i.val) / 64 + 1]!.val *
                                    2 ^ (64 - (w.val * i.val) % 64)) := by
          left
          refine ⟨?_, Or.inr ?_⟩
          · rw [hbuf2_val, hu64_val, hbit_val, mul_comm]
          · rw [mul_comm, ←  hu64_val]
            grind only [= UScalar.ofNatCore_val_eq]
        have h_window : bit_buf2.val % 2 ^ w.val =
                  X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val) % 2 ^ w.val := by
          have := bit_extraction_correct scalar64x4 w window_mask i hw_lo hw_hi h_mask
                  hi_lt_digits bit_buf2 h_buf_cond
          rw [U64_and_mask_eq_mod _ _ w.val h_mask] at this
          exact this
        step as ⟨i2, hi2⟩
        have h_window2 : i2.val = X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val) % 2 ^ w.val := by
          rw [hi2, UScalar.val_and, h_mask, land_pow_two_sub_one_eq_mod]
          exact h_window
        step as ⟨coef, hcoef⟩
        · grind
        have hcoef_val : coef.val = carry.val + i2.val := by scalar_tac
        have hcoef_le : coef.val ≤ 2 ^ w.val := by
          rw [hcoef_val, h_window2]
          have := Nat.mod_lt (X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val)) (Nat.two_pow_pos w.val)
          omega
        step as ⟨i3, hi3⟩
        have hi3_val : i3.val = 2 ^ (w.val - 1) := by
          have h1 : i3.val = radix.val / 2 := by scalar_tac
          rw [h1, h_radix]
          cases hw : w.val with
          | zero => omega
          | succ w' =>
            rw [pow_succ_half w']
            simp only [add_tsub_cancel_right]
        step as ⟨i4, hi4⟩
        have hi4_val : i4.val = coef.val + 2 ^ (w.val - 1) := by
          have h1 : i4.val = coef.val + i3.val := by scalar_tac
          rw [h1, hi3_val]
        step as ⟨carry1, hcarry1⟩
        have hcarry1_val : carry1.val = (coef.val + 2 ^ (w.val - 1)) / 2 ^ w.val := by
          have h1 : carry1.val = i4.val / 2 ^ w.val := by
            simp only [hcarry1, Nat.shiftRight_eq_div_pow]
          rw [h1, hi4_val]
        have hcarry1_le : carry1.val ≤ 1 := by
          have := carry_zero_or_one_2w coef.val w.val hcoef_le hw_pos
          omega
        step as ⟨i5, hi5⟩
        have hi5_val : i5.val = (coef.val : ℤ) := by
          rw [hi5]
          apply UScalar.hcast_inBounds_spec .I64
          simp only [IScalar.max]
          grind
        step as ⟨i6, hi6⟩
        have hi6_val : i6.val = carry1.val * 2 ^ w.val := by
          have hbound : carry1.val * 2 ^ w.val < U64.size := by
            simp only [U64.size]; scalar_tac
          have heq : carry1.val <<< w.val % U64.size = carry1.val * 2 ^ w.val := by
            rw [Nat.shiftLeft_eq]
            apply Nat.mod_eq_of_lt hbound
          linarith [show i6.val = carry1.val <<< w.val % U64.size from by scalar_tac, heq]
        step as ⟨i7, hi7⟩
        have hi7_val : i7.val = (carry1.val : ℤ) * 2 ^ w.val := by
          rw [hi7]
          have hi6_bound : i6.val ≤ 2 ^ w.val := by
            rw [hi6_val]; grind only [usr Nat.pow_pos, usr ScalarTac.le_mul_lt_le]
          have hi6_lt63 : i6.val < 2 ^ 63 := by omega
          have hcast : (UScalar.hcast .I64 i6).val = (i6.val : ℤ) := by
            apply UScalar.hcast_inBounds_spec .I64
            simp only [IScalar.max]
            grind
          rw [hcast, hi6_val]; push_cast; ring
        step as ⟨i8, hi8⟩
        have hi8_val : i8.val = (coef.val : ℤ) - (carry1.val : ℤ) * 2 ^ w.val := by
          simp only [hi8, hi5_val, hi7_val]
        have h_digit_rng := recenter_in_range_2w coef.val w.val hcoef_le hw_pos
        have h_digit_lo : -(2 ^ (w.val - 1) : ℤ) ≤ i8.val := by
          rw [hi8_val, hcarry1_val, hcoef_val, h_window2]; simp_all
        have h_digit_hi : i8.val < 2 ^ (w.val - 1) := by
          rw [hi8_val, hcarry1_val, hcoef_val, h_window2]
          grind
        step as ⟨i9, hi9⟩
        have hi9_val : i9.val = i8.val := by
          have hspec := IScalar.cast_inBounds_spec .I8 i8 (by
            simp only [IScalar.min, IScalar.max]
            norm_num
            grind)
          simp only [lift, spec_ok] at hspec
          rw [← hi9] at hspec
          exact hspec
        step with I8x64_update_get as ⟨a, ha_other, ha_i⟩
        have hiter2_start : iter1.start.val = i.val + 1 := by
          rw [← hi_val] at hiter1_start; exact hiter1_start
        have hiter2_end : iter1.end = iter.end := hiter1_end
        have ha_pref : ∀ j < i.val, (a[j]! : Std.I8).val = (digits[j]!).val := by
          intro j hj; simp only [Array.getElem!_Nat_eq, ha_other j (by omega)]
        have ha_later : ∀ j, i.val + 1 ≤ j → j < 64 →
            (a[j]! : Std.I8).val = (digits[j]!).val := by
          intro j hj1 _; simp only [Array.getElem!_Nat_eq, ha_other j (by omega)]
        have h_inv' :
          ∑ j ∈ Finset.range iter1.start.val, (2 ^ w.val : ℤ) ^ j * (a[j]!).val
          + (carry1.val : ℤ) * (2 ^ w.val) ^ iter1.start.val
          = ↑(N % 2 ^ (w.val * iter1.start.val)) := by
          rw [hiter2_start]
          have h_pref_sum :
            ∑ j ∈ Finset.range i.val, (2 ^ w.val : ℤ) ^ j * (a[j]!).val =
            ∑ j ∈ Finset.range i.val, (2 ^ w.val : ℤ) ^ j * (digits[j]!).val :=
            Finset.sum_congr rfl (fun j hj => by rw [ha_pref j (Finset.mem_range.mp hj)])
          rw [Finset.sum_range_succ, ha_i, hi9_val, h_pref_sum]
          apply inv_step_2w N w.val i.val carry.val carry1.val
                (N / 2 ^ (w.val * i.val) % 2 ^ w.val)
                (∑ j ∈ Finset.range i.val, (2 ^ w.val) ^ j * (digits[j]!).val) i8.val
          · rfl
          · grind
          · grind
        have h_bounds' : ∀ j < iter1.start.val,
                  -(2 ^ (w.val - 1) : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val < 2 ^ (w.val - 1) := by
          rw [hiter2_start]
          exact bounds_step_2w digits a i.val w.val i9
            (by rw [hi9_val]; exact h_digit_lo) (by rw [hi9_val]; exact h_digit_hi)
            ha_i ha_pref (fun j hj => h_bounds j (hi_val ▸ hj))
        have h_tail' : ∀ j, iter1.start.val ≤ j → j < 64 → (a[j]! : Std.I8).val = 0 := by
          rw [hiter2_start]
          exact tail_step_2w digits a i.val ha_later (fun j hj => h_tail j (hi_val ▸ hj))
        apply spec_mono
          (as_radix_2w_loop_spec_strong iter1 w scalar64x4 radix window_mask carry1 a
            K N hw_lo hw_hi h_radix h_mask h_N h_N_lt hK_le64 hK_le_digits
            (by rw [hiter2_end]; exact h_end)
            (by rw [hiter2_start, hi_val]; omega)
            h_inv' hcarry1_le h_bounds' h_tail')
        clear *-
        intro result hresult
        simp at hresult
        simp only [hresult, true_and]
        have := hresult.right.right
        apply this
      · -- Case 3: Cross-limb (bit_idx ≥ 64 - w, u64_idx ≠ 3)
        have hu64_ne3 : u64_idx.val ≠ 3 := by
          intro heq
          apply h_last
          exact UScalar.eq_of_val_eq (by simp only [UScalar.ofNatCore_val_eq]; exact heq)
        have hu64_lt3 : u64_idx.val < 3 := by rw [hu64_val]; omega
        simp only [h_last, ↓reduceIte, Array.getElem!_Nat_eq]
        step as ⟨limb1, hlimb1⟩
        step as ⟨s1, hs1⟩
        step as ⟨idx, hidx⟩
        step as ⟨limb2, hlimb2⟩
        step as ⟨shift_amt, hshift_amt⟩
        step as ⟨s2, hs2⟩
        step as ⟨bit_buf3, hbit_buf3⟩
        have hidx_val : idx.val = u64_idx.val + 1 := by scalar_tac
        have hshift_val : shift_amt.val = 64 - bit_idx.val := by scalar_tac
        have hs1_val : s1.val = scalar64x4[u64_idx.val]!.val / 2 ^ bit_idx.val := by
          simp only [hs1, hlimb1]; scalar_tac
        have hs2_val : s2.val =
          (scalar64x4[u64_idx.val + 1]!.val * 2 ^ (64 - bit_idx.val)) % 2 ^ 64 := by
          simp only [hs2, hlimb2, hidx_val, Nat.shiftLeft_eq, hshift_val]
          simp only [Array.getElem!_Nat_eq]
          scalar_tac
        have h_window2 : bit_buf3.val =
          X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val) % 2 ^ w.val := by
          have hlt : bit_buf3.val < 2 ^ w.val := by
            rw [hbit_buf3, UScalar.val_and, h_mask, land_pow_two_sub_one_eq_mod]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          suffices h : bit_buf3.val % 2 ^ w.val =
            X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val) % 2 ^ w.val by
            rwa [Nat.mod_eq_of_lt hlt] at h
          have hcross : i.val * w.val % 64 + w.val ≥  64 := by
            rw [hbit_val, hi1_val] at h_fit; push_neg at h_fit; clear *- h_fit; grind
          have hbo192 : i.val * w.val < 192 := by
            rw [hu64_val] at hu64_lt
            grind
          have hlo_lt : scalar64x4[u64_idx.val]!.val / 2^bit_idx.val < 2^(64-bit_idx.val) := by
            apply Nat.div_lt_of_lt_mul
            calc scalar64x4[u64_idx.val]!.val < 2^64 := by apply U64_val_lt _
                  _ = 2^bit_idx.val * 2^(64-bit_idx.val) := by rw [← pow_add]; congr 1; omega
          rw [hbit_buf3, UScalar.val_and, h_mask, land_pow_two_sub_one_eq_mod,
            UScalar.val_or, hs1_val, hs2_val]
          have h_hi_eq : scalar64x4[u64_idx.val+1]!.val * 2^(64-bit_idx.val) % 2^64 =
                  (scalar64x4[u64_idx.val+1]!.val % 2^bit_idx.val) * 2^(64-bit_idx.val) := by
              conv_lhs => rw [show scalar64x4[u64_idx.val+1]!.val * 2^(64-bit_idx.val) =
                    (scalar64x4[u64_idx.val+1]!.val % 2^bit_idx.val) * 2^(64-bit_idx.val) +
                    (scalar64x4[u64_idx.val+1]!.val / 2^bit_idx.val) * 2^64 from by
                      have := Nat.div_add_mod (scalar64x4[u64_idx.val+1]!.val) (2^bit_idx.val)
                      grind [Nat.two_pow_pos bit_idx.val,
                        show 2^bit_idx.val * 2^(64-bit_idx.val) = 2^64
                        from by rw [← pow_add]; congr 1; omega]]
              rw [add_mul_pow_mod_pow' _ _ 64 64 (le_refl _)]
              apply Nat.mod_eq_of_lt
              have : 2^bit_idx.val * 2^(64-bit_idx.val) = 2^64 :=by
                rw [← pow_add]
                grind
              rw [← this]
              simp only [Array.getElem!_Nat_eq, Nat.ofNat_pos, pow_pos,
              mul_lt_mul_iff_left₀, gt_iff_lt]
              apply Nat.mod_lt
              grind
          rw [h_hi_eq, or_mul_pow_two_eq_add _ _ (64-bit_idx.val) hlo_lt]
          have h_same_mod : (scalar64x4[u64_idx.val]!.val / 2^bit_idx.val +
                  (scalar64x4[u64_idx.val+1]!.val % 2^bit_idx.val) * 2^(64-bit_idx.val)) % 2^w.val =
                  (scalar64x4[u64_idx.val]!.val / 2^bit_idx.val +
                  scalar64x4[u64_idx.val+1]!.val * 2^(64-bit_idx.val)) % 2^w.val := by
            have hwle : w.val ≥ 64 - bit_idx.val := by
                  rw [ hi1_val] at h_fit; push_neg at h_fit; omega
            rw [show scalar64x4[u64_idx.val+1]!.val * 2^(64-bit_idx.val) =
                    (scalar64x4[u64_idx.val+1]!.val % 2^bit_idx.val) * 2^(64-bit_idx.val) +
                    scalar64x4[u64_idx.val+1]!.val / 2^bit_idx.val * 2^64 from by
                      have := Nat.div_add_mod (scalar64x4[u64_idx.val+1]!.val) (2^bit_idx.val)
                      grind [Nat.two_pow_pos bit_idx.val,
                        show 2^bit_idx.val * 2^(64-bit_idx.val) = 2^64
                        from by rw [← pow_add]; congr 1; omega]]
            rw [show scalar64x4[u64_idx.val]!.val / 2^bit_idx.val +
                    ((scalar64x4[u64_idx.val+1]!.val % 2^bit_idx.val) * 2^(64-bit_idx.val) +
                    scalar64x4[u64_idx.val+1]!.val / 2^bit_idx.val * 2^64) =
                    scalar64x4[u64_idx.val]!.val / 2^bit_idx.val +
                    (scalar64x4[u64_idx.val+1]!.val % 2^bit_idx.val) * 2^(64-bit_idx.val) +
                    scalar64x4[u64_idx.val+1]!.val / 2^bit_idx.val * 2^64 from by ring]
            symm
            apply add_mul_pow_mod_pow'
            grind
          rw [h_same_mod, hbit_val, hu64_val,
              show w.val * i.val = i.val * w.val from mul_comm _ _]
          by_cases heq64 : i.val * w.val % 64 + w.val = 64
          · rw [show 64 - i.val * w.val % 64 = w.val from by omega,
                    add_mul_pow_mod_pow' _ _ w.val w.val (le_refl _)]
            have := (X64_window_single_limb scalar64x4 (i.val * w.val) w.val
                    (by omega) (by omega)).symm
            rw [this]
            apply Nat.mod_eq_of_lt
            apply Nat.mod_lt
            grind
          · have:= (X64_window_cross_limb scalar64x4 (i.val * w.val) w.val
                    hbo192 (by omega) (by omega)).symm
            rw [this]
            apply Nat.mod_eq_of_lt
            apply Nat.mod_lt
            grind
        step as ⟨coef, hcoef⟩
        · grind
        have hcoef_val : coef.val = carry.val + bit_buf3.val := by scalar_tac
        have hcoef_le : coef.val ≤ 2 ^ w.val := by
          rw [hcoef_val, h_window2]
          have := Nat.mod_lt (X64_as_Nat scalar64x4 / 2 ^ (w.val * i.val)) (Nat.two_pow_pos w.val)
          omega
        step as ⟨i3, hi3⟩
        have hi3_val : i3.val = 2 ^ (w.val - 1) := by
          have h1 : i3.val = radix.val / 2 := by scalar_tac
          rw [h1, h_radix]
          cases hw : w.val with
          | zero => omega
          | succ w' => rw [pow_succ_half w']; simp
        step as ⟨i4, hi4⟩
        have hi4_val : i4.val = coef.val + 2 ^ (w.val - 1) := by
          have h1 : i4.val = coef.val + i3.val := by scalar_tac
          rw [h1, hi3_val]
        step as ⟨carry1, hcarry1⟩
        have hcarry1_val : carry1.val = (coef.val + 2 ^ (w.val - 1)) / 2 ^ w.val := by
          have h1 : carry1.val = i4.val / 2 ^ w.val := by
            simp only [hcarry1, Nat.shiftRight_eq_div_pow]
          rw [h1, hi4_val]
        have hcarry1_le : carry1.val ≤ 1 := by
          have := carry_zero_or_one_2w coef.val w.val hcoef_le hw_pos
          omega
        step as ⟨i5, hi5⟩
        have hi5_val : i5.val = (coef.val : ℤ) := by
          rw [hi5]
          apply UScalar.hcast_inBounds_spec .I64
          simp only [IScalar.max]
          norm_num
          omega
        step as ⟨i6, hi6⟩
        have hi6_val : i6.val = carry1.val * 2 ^ w.val := by
          have hbound : carry1.val * 2 ^ w.val < U64.size := by
            simp only [U64.size]; scalar_tac
          have heq : carry1.val <<< w.val % U64.size = carry1.val * 2 ^ w.val := by
            rw [Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt hbound
          linarith [show i6.val = carry1.val <<< w.val % U64.size from by scalar_tac, heq]
        step as ⟨i7, hi7⟩
        have hi7_val : i7.val = (carry1.val : ℤ) * 2 ^ w.val := by
          rw [hi7]
          have hi6_bound : i6.val ≤ 2 ^ w.val := by rw [hi6_val]; nlinarith [hcarry1_le]
          have hi6_lt63 : i6.val < 2 ^ 63 := by omega
          have hcast : (UScalar.hcast .I64 i6).val = (i6.val : ℤ) := by
            apply UScalar.hcast_inBounds_spec .I64
            simp only [IScalar.max]
            scalar_tac
          rw [hcast, hi6_val]
          push_cast
          ring
        step as ⟨i8, hi8⟩
        have hi8_val : i8.val = (coef.val : ℤ) - (carry1.val : ℤ) * 2 ^ w.val := by
              simp only [hi8, hi5_val, hi7_val]
        have h_digit_rng := recenter_in_range_2w coef.val w.val hcoef_le hw_pos
        have h_digit_lo : -(2 ^ (w.val - 1) : ℤ) ≤ i8.val := by
              rw [hi8_val, hcarry1_val, hcoef_val, h_window2]; simp_all
        have h_digit_hi : i8.val < 2 ^ (w.val - 1) := by
          rw [hi8_val, hcarry1_val, hcoef_val, h_window2]
          simp_all
        step as ⟨i9, hi9⟩
        have hi9_val : i9.val = i8.val := by
          have hspec := IScalar.cast_inBounds_spec .I8 i8 (by
            simp only [IScalar.min, IScalar.max]
            norm_num
            grind)
          simp only [lift, spec_ok] at hspec
          rw [hi9]
          exact hspec
        step with I8x64_update_get as ⟨a, ha_other, ha_i⟩
        have hiter2_start : iter1.start.val = i.val + 1 := by
          rw [← hi_val] at hiter1_start; exact hiter1_start
        have hiter2_end : iter1.end = iter.end := hiter1_end
        have ha_pref : ∀ j < i.val, (a[j]! : Std.I8).val = (digits[j]!).val := by
          intro j hj; simp only [Array.getElem!_Nat_eq, ha_other j (by omega)]
        have ha_later : ∀ j, i.val + 1 ≤ j → j < 64 →
            (a[j]! : Std.I8).val = (digits[j]!).val := by
          intro j hj1 _; simp only [Array.getElem!_Nat_eq, ha_other j (by omega)]
        have h_inv' :
                ∑ j ∈ Finset.range iter1.start.val, (2 ^ w.val : ℤ) ^ j * (a[j]!).val
                + (carry1.val : ℤ) * (2 ^ w.val) ^ iter1.start.val
                = ↑(N % 2 ^ (w.val * iter1.start.val)) := by
          rw [hiter2_start]
          have h_pref_sum :
                  ∑ j ∈ Finset.range i.val, (2 ^ w.val : ℤ) ^ j * (a[j]!).val =
                  ∑ j ∈ Finset.range i.val, (2 ^ w.val : ℤ) ^ j * (digits[j]!).val :=
                Finset.sum_congr rfl (fun j hj => by rw [ha_pref j (Finset.mem_range.mp hj)])
          rw [Finset.sum_range_succ, ha_i, hi9_val, h_pref_sum]
          apply inv_step_2w N w.val i.val carry.val carry1.val
                (N / 2 ^ (w.val * i.val) % 2 ^ w.val)
                  (∑ j ∈ Finset.range i.val, (2 ^ w.val) ^ j * (digits[j]!).val) i8.val
          · rfl
          · grind
          · grind
        have h_bounds' : ∀ j < iter1.start.val,
                -(2 ^ (w.val - 1) : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val < 2 ^ (w.val - 1) := by
          rw [hiter2_start]
          exact bounds_step_2w digits a i.val w.val i9
                (by rw [hi9_val]; exact h_digit_lo) (by rw [hi9_val]; exact h_digit_hi)
                ha_i ha_pref (fun j hj => h_bounds j (hi_val ▸ hj))
        have h_tail' : ∀ j, iter1.start.val ≤ j → j < 64 → (a[j]! : Std.I8).val = 0 := by
          rw [hiter2_start]
          exact tail_step_2w digits a i.val ha_later (fun j hj => h_tail j (hi_val ▸ hj))
        apply spec_mono
          (as_radix_2w_loop_spec_strong iter1 w scalar64x4 radix window_mask carry1 a
            K N hw_lo hw_hi h_radix h_mask h_N h_N_lt hK_le64 hK_le_digits
            (by rw [hiter2_end]; exact h_end)
            (by rw [hiter2_start, hi_val]; omega)
            h_inv' hcarry1_le h_bounds' h_tail')
        clear *-
        intro result hresult
        simp at hresult
        simp only [hresult, true_and]
        have := hresult.right.right
        apply this
  termination_by K - iter.start.val
  decreasing_by
    all_goals (first
      | (rw [hiter2_start, hi_val]; omega))

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_2w_loop`**
• No panic: the loop always terminates successfully
• The radix-2^w signed-digit sum with carry reconstructs N:
  `∑ j < K, (2^w)^j · digits[j] + carry · (2^w)^K = N`
• The final carry satisfies `carry ≤ 1`
• All produced digits j < K satisfy `−2^(w−1) ≤ digits[j] < 2^(w−1)`
• All array entries at indices j ≥ K remain zero
-/
@[step]
theorem as_radix_2w_loop_spec
    (iter : core.ops.range.Range Std.Usize)
    (w : Std.Usize)
    (scalar64x4 : Array Std.U64 4#usize)
    (radix window_mask : Std.U64)
    (carry : Std.U64)
    (digits : Array Std.I8 64#usize)
    (K : ℕ) (N : ℕ)
    (hw_lo : 5 ≤ w.val) (hw_hi : w.val ≤ 8)
    (h_radix : radix.val = 2 ^ w.val)
    (h_mask : window_mask.val = 2 ^ w.val - 1)
    (h_N : N = X64_as_Nat scalar64x4)
    (h_N_lt : N < 2 ^ (w.val * K))
    (hK_le64 : K ≤ 64)
    (hK_le_digits : K * w.val ≤ 255 + w.val)
    (h_end : iter.end.val = K)
    (h_start : iter.start.val ≤ K)
    (h_inv : ∑ j ∈ Finset.range iter.start.val, (2 ^ w.val : ℤ) ^ j * (digits[j]!).val
                + (carry.val : ℤ) * (2 ^ w.val) ^ iter.start.val
                = ↑(N % 2 ^ (w.val * iter.start.val)))
    (h_carry : carry.val ≤ 1)
    (h_bounds : ∀ j < iter.start.val,
        -(2 ^ (w.val - 1) : ℤ) ≤ (digits[j]!).val ∧ (digits[j]!).val < 2 ^ (w.val - 1))
    (h_tail : ∀ j, iter.start.val ≤ j → j < 64 → (digits[j]! : Std.I8).val = 0) :
    as_radix_2w_loop iter w scalar64x4 radix window_mask carry digits
    ⦃ (result : Std.U64 × Array Std.I8 64#usize) =>
      ∑ j ∈ Finset.range K, (2 ^ w.val : ℤ) ^ j * (result.2[j]!).val
      + (result.1.val : ℤ) * (2 ^ w.val) ^ K = ↑N ∧
      result.1.val ≤ 1 ∧
      (∀ j < K,
        -(2 ^ (w.val - 1) : ℤ) ≤ (result.2[j]!).val ∧
        (result.2[j]!).val < 2 ^ (w.val - 1)) ∧
      (∀ j, K ≤ j → j < 64 → (result.2[j]! : Std.I8).val = 0) ⦄ :=
  as_radix_2w_loop_spec_strong iter w scalar64x4 radix window_mask carry digits
    K N hw_lo hw_hi h_radix h_mask h_N h_N_lt hK_le64 hK_le_digits
    h_end h_start h_inv h_carry h_bounds h_tail

@[step]
private theorem Array_index_mut_SliceIndexRangeUsizeSlice {T : Type} {N : Usize}
    (a : Aeneas.Std.Array T N) (r : core.ops.range.Range Std.Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r ⦃ (s, back) =>
      s.val = a.val.slice r.start r.end ∧
      s.length = r.end.val - r.start.val ∧
      ∀ s', (back s').val = a.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.to_slice.length = N := by simp
  have h_slice :=
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec r a.to_slice h0
      (show r.end ≤ a.to_slice.length from by scalar_tac)
  apply spec_bind h_slice
  intro ⟨s1, back1⟩ ⟨hs1_val, hs1_len, hback1⟩
  simp only [spec_ok]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Array.val_to_slice] at hs1_val; exact hs1_val
  · exact hs1_len
  · intro s'
    simp only [hback1]
    simp_all [Array.from_slice, Slice.setSlice!, Array.to_slice]

private lemma I8x64_as_Radix2w_4_eq_Radix16 (digits : Array Std.I8 64#usize) :
    I8x64_as_Radix2w 4 digits = I8x64_as_Radix16 digits := by
  simp only [I8x64_as_Radix2w, I8x64_as_Radix16, show (2 : ℤ) ^ 4 = 16 from by norm_num]

private lemma N_lt_pow_w_digits_count (N w : ℕ) (hw_lo : 5 ≤ w) (hw_hi : w ≤ 8)
    (hN : N < 2 ^ 256) :
    N < 2 ^ (w * ((255 + w) / w)) := by
  have h : w * ((255 + w) / w) ≥ 256 := by interval_cases w <;> simp_all
  calc N < 2 ^ 256 := hN
    _ ≤ 2 ^ (w * ((255 + w) / w)) := Nat.pow_le_pow_right (by norm_num) h

private lemma X64_as_Nat_lt_pow_w_digits_count
    (limbs : Array Std.U64 4#usize) (w : ℕ) (hw_lo : 5 ≤ w) (hw_hi : w ≤ 8) :
    X64_as_Nat limbs < 2 ^ (w * ((255 + w) / w)) :=
  N_lt_pow_w_digits_count _ w hw_lo hw_hi (X64_as_Nat_lt_pow256 limbs)

/-! ## Geometric series and carry-zero lemma -/

private lemma geom_sum_int (b : ℤ) (K : ℕ) :
    (b - 1) * ∑ j ∈ Finset.range K, b ^ j = b ^ K - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

set_option maxHeartbeats 1600000 in
-- The proof branches over all valid values of w via interval_cases, generating
-- multiple arithmetic subgoals that exhaust the default heartbeat budget.
private lemma final_carry_is_zero (w K N : ℕ)
    (digits : Array Std.I8 64#usize)
    (hw_lo : 5 ≤ w) (hw_hi : w ≤ 7)
    (hK : K = (255 + w) / w)
    (hN_lt : N < 2 ^ 256)
    (carry : ℕ) (h_carry : carry ≤ 1)
    (h_sum : ∑ j ∈ Finset.range K, (2 ^ w : ℤ) ^ j * (digits[j]!).val
             + (carry : ℤ) * (2 ^ w : ℤ) ^ K = ↑N)
    (h_bounds : ∀ j < K, -(2 ^ (w - 1) : ℤ) ≤ (digits[j]!).val) :
    carry = 0 := by
  by_contra hne
  have hc1 : carry = 1 := by omega
  subst hc1
  set S := ∑ j ∈ Finset.range K, (2 ^ w : ℤ) ^ j * (digits[j]!).val with hS_def
  have hSN : S + (2 ^ w : ℤ) ^ K = ↑N := by simpa using h_sum
  have hN_z : (↑N : ℤ) < (2 : ℤ) ^ 256 := Int.ofNat_lt.mpr hN_lt
  have h2w_ge2 : (2 : ℤ) ≤ (2 : ℤ) ^ w := by interval_cases w <;> norm_num
  have h2w_eq : (2 : ℤ) ^ w = 2 * (2 : ℤ) ^ (w - 1) := by
    interval_cases w <;> norm_num
  set G := ∑ j ∈ Finset.range K, (2 ^ w : ℤ) ^ j with hG_def
  have hS_ge : -(2 ^ (w - 1) : ℤ) * G ≤ S := by
    rw [hS_def, hG_def, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    nlinarith [h_bounds j (Finset.mem_range.mp hj),
               show (0 : ℤ) < (2 ^ w : ℤ) ^ j from by positivity]
  have hgeom : ((2 ^ w : ℤ) - 1) * G = (2 ^ w : ℤ) ^ K - 1 := geom_sum_int _ K
  have hbm1 : (0 : ℤ) < (2 ^ w : ℤ) - 1 := by linarith
  have hpowK : (2 ^ w : ℤ) ^ K ≥ (2 : ℤ) ^ 256 := by
    have hwK : w * K ≥ 256 := by
      subst hK; interval_cases w <;> simp_all
    have : (2 : ℤ) ^ (w * K) ≥ (2 : ℤ) ^ 256 := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hwK
    rwa [pow_mul] at this
  have hcoeff : (2 : ℤ) ^ w - 1 - (2 : ℤ) ^ (w - 1) = (2 : ℤ) ^ (w - 1) - 1 := by
    linarith [h2w_eq]
  have hS_scaled : ((2 ^ w : ℤ) - 1) * S ≥ -(2 ^ (w - 1) : ℤ) * ((2 ^ w : ℤ) ^ K - 1) := by
    calc ((2 ^ w : ℤ) - 1) * S
        ≥ ((2 ^ w : ℤ) - 1) * (-(2 ^ (w - 1) : ℤ) * G) := by nlinarith
      _ = -(2 ^ (w - 1) : ℤ) * (((2 ^ w : ℤ) - 1) * G) := by ring
      _ = -(2 ^ (w - 1) : ℤ) * ((2 ^ w : ℤ) ^ K - 1) := by rw [hgeom]
  have key2 : ((2 ^ w : ℤ) - 1) * ↑N ≥
      ((2 : ℤ) ^ (w - 1) - 1) * (2 ^ w : ℤ) ^ K + (2 : ℤ) ^ (w - 1) := by
    have h_eq : ((2 ^ w : ℤ) - 1) * ↑N =
                ((2 ^ w : ℤ) - 1) * S + ((2 ^ w : ℤ) - 1) * (2 ^ w : ℤ) ^ K := by
      nlinarith [hSN]
    have h_expand : -(2 ^ (w - 1) : ℤ) * ((2 ^ w : ℤ) ^ K - 1) =
                    -(2 ^ (w - 1) : ℤ) * (2 ^ w : ℤ) ^ K + (2 : ℤ) ^ (w - 1) := by ring
    have h_mul : ((2 : ℤ) ^ w - 1 - (2 : ℤ) ^ (w - 1)) * (2 ^ w : ℤ) ^ K =
                 ((2 : ℤ) ^ (w - 1) - 1) * (2 ^ w : ℤ) ^ K := by
      rw [hcoeff]
    nlinarith [h_expand, h_mul]
  have hpowK4 : (2 ^ w : ℤ) ^ K ≥ 4 * (2 : ℤ) ^ 256 := by
    have hwK : w * K ≥ 258 := by
      subst hK; interval_cases w <;> simp_all
    have h1 : (2 : ℤ) ^ (w * K) ≥ (2 : ℤ) ^ 258 := by
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hwK
      grind
    rw [pow_mul] at h1
    have h2 : (2 : ℤ) ^ 258 = 4 * (2 : ℤ) ^ 256 := by grind
    grind
  have h4coeff : 4 * ((2 : ℤ) ^ (w - 1) - 1) ≥ (2 : ℤ) ^ w - 1 := by
    interval_cases w <;> norm_num
  have h_upper : ((2 ^ w : ℤ) - 1) * ↑N < ((2 ^ w : ℤ) - 1) * (2 : ℤ) ^ 256 := by
    nlinarith [hbm1, hN_z]
  have hpwm1_pos : (0 : ℤ) < (2 : ℤ) ^ (w - 1) := by positivity
  nlinarith [key2, h_upper, hpowK4, h4coeff, hpwm1_pos]

private lemma I8x64_as_Radix2w_eq_prefix_sum (w K : ℕ) (digits : Array Std.I8 64#usize)
    (hK : K ≤ 64)
    (h_tail : ∀ j, K ≤ j → j < 64 → (digits[j]! : Std.I8).val = 0) :
    I8x64_as_Radix2w w digits =
      ∑ j ∈ Finset.range K, (2 ^ w : ℤ) ^ j * (digits[j]!).val := by
  simp only [I8x64_as_Radix2w]
  symm
  apply Finset.sum_subset
  · intro x hx; exact Finset.mem_range.mpr (by rw [Finset.mem_range] at hx; omega)
  · intro j hj64 hjK
    rw [Finset.mem_range] at hj64
    simp only [Finset.mem_range] at hjK; push_neg at hjK
    rw [h_tail j hjK hj64, mul_zero]

private lemma I8x64_as_Radix2w_trim (w K : ℕ) (digits : Array Std.I8 64#usize)
    (hK : K ≤ 64)
    (h_tail : ∀ j, K ≤ j → j < 64 → (digits[j]! : Std.I8).val = 0) :
    I8x64_as_Radix2w w digits =
    ∑ j ∈ Finset.range K, (2 ^ w : ℤ) ^ j * (digits[j]!).val := by
  unfold I8x64_as_Radix2w
  symm
  apply Finset.sum_subset (Finset.range_mono hK)
  intro i hi hni
  have hi_range : i < 64 := Finset.mem_range.mp hi
  have hi_ge : K ≤ i := by
    by_contra h
    exact hni (Finset.mem_range.mpr (by omega))
  rw [h_tail i hi_ge hi_range]
  simp

private lemma digits_count_le_64 (w : ℕ) (hw_lo : 5 ≤ w) (hw_hi : w ≤ 8) :
    (255 + w) / w ≤ 64 := by
  interval_cases w <;> norm_num

private lemma digits_count_mul_le (w : ℕ) :
    (255 + w) / w * w ≤ 255 + w :=
  Nat.div_mul_le_self (255 + w) w

private lemma digits_count_pos (w : ℕ) (hw_lo : 5 ≤ w) (hw_hi : w ≤ 8) :
    1 ≤ (255 + w) / w := by
  interval_cases w <;> norm_num

private lemma U8x32_as_Nat_lt_pow256 (self : Scalar) :
    U8x32_as_Nat self.bytes < 2 ^ 256 := by
  simp only [U8x32_as_Nat]
  have key : ∀ k, k ≤ 32 →
      ∑ i ∈ Finset.range k, 2 ^ (8 * i) * (self.bytes[i]!).val < 2 ^ (8 * k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hbnd : (self.bytes[k]!).val < 256 := by
        have := (self.bytes[k]!).hBounds; scalar_tac
      have ih' := ih (by omega)
      have h8k : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
        rw [show 8 * (k + 1) = 8 * k + 8 from by ring, pow_add]; norm_num
      nlinarith [Nat.two_pow_pos (8 * k)]
  calc ∑ i ∈ Finset.range 32, 2 ^ (8 * i) * (self.bytes[i]!).val
      < 2 ^ (8 * 32) := key 32 le_rfl
    _ = 2 ^ 256 := by norm_num

lemma U8x32_as_Nat_lt_pow255 (self : Scalar)
    (h_top : (self.bytes[31]!).val ≤ 127) :
    U8x32_as_Nat self.bytes < 2 ^ 255 := by
  simp only [U8x32_as_Nat]
  have key : ∀ k, k ≤ 32 →
      ∑ i ∈ Finset.range k, 2 ^ (8 * i) * (self.bytes[i]!).val < 2 ^ (8 * k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hbnd : (self.bytes[k]!).val < 256 := by
        have := (self.bytes[k]!).hBounds; scalar_tac
      have ih' := ih (by omega)
      have h8k : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
        rw [show 8 * (k + 1) = 8 * k + 8 from by ring, pow_add]; norm_num
      nlinarith [Nat.two_pow_pos (8 * k)]
  have h31 : ∑ i ∈ Finset.range 31, 2 ^ (8 * i) * (self.bytes[i]!).val < 2 ^ (8 * 31) :=
    key 31 (by omega)
  have hsplit : ∑ i ∈ Finset.range 32, 2 ^ (8 * i) * (self.bytes[i]!).val =
      ∑ i ∈ Finset.range 31, 2 ^ (8 * i) * (self.bytes[i]!).val +
      2 ^ (8 * 31) * (self.bytes[31]!).val :=
    Finset.sum_range_succ (fun i => 2 ^ (8 * i) * (self.bytes[i]!).val) 31
  rw [hsplit]
  nlinarith [show (2 : ℕ) ^ (8 * 31) * 128 = 2 ^ 255 from by norm_num,
             Nat.mul_le_mul_left (2 ^ (8 * 31)) h_top]

private lemma carry_fold_value_w_ne8
    (w K N : ℕ) (digits : Array Std.I8 64#usize)
    (hK : K ≤ 64)
    (h_tail : ∀ j, K ≤ j → j < 64 → (digits[j]! : Std.I8).val = 0)
    (h_sum : ∑ j ∈ Finset.range K, (2 ^ w : ℤ) ^ j * (digits[j]!).val
             + (0 : ℤ) * (2 ^ w) ^ K = ↑N) :
    I8x64_as_Radix2w w digits = ↑N := by
  simp only [zero_mul, add_zero] at h_sum
  rw [I8x64_as_Radix2w_trim w K digits hK h_tail, h_sum]

private lemma carry_fold_value_w8
    (K N : ℕ) (digits result : Array Std.I8 64#usize)
    (carry : Std.U64)
    (hK_lt : K < 64)
    (h_tail : ∀ j, K ≤ j → j < 64 → (digits[j]! : Std.I8).val = 0)
    (h_sum : ∑ j ∈ Finset.range K, (2 ^ 8 : ℤ) ^ j * (digits[j]!).val
             + (carry.val : ℤ) * (2 ^ 8) ^ K = ↑N)
    (h_result_at : (result[K]!).val = (digits[K]!).val + (carry.val : ℤ))
    (h_result_other : ∀ j, j ≠ K → (result[j]!).val = (digits[j]!).val) :
    I8x64_as_Radix2w 8 result = ↑N := by
  have hdigitsK : (digits[K]!).val = 0 := h_tail K le_rfl hK_lt
  have hresultK : (result[K]!).val = (carry.val : ℤ) := by
    rw [h_result_at, hdigitsK, zero_add]
  have h_result_tail : ∀ j, K + 1 ≤ j → j < 64 → (result[j]!).val = 0 :=
    fun j hj hj64 => by
      rw [h_result_other j (by omega)]
      exact h_tail j (by omega) hj64
  rw [I8x64_as_Radix2w_trim 8 (K + 1) result (by omega) h_result_tail]
  rw [Finset.sum_range_succ]
  have heq_prefix : ∑ j ∈ Finset.range K, (2 ^ 8 : ℤ) ^ j * (result[j]!).val =
                    ∑ j ∈ Finset.range K, (2 ^ 8 : ℤ) ^ j * (digits[j]!).val :=
    Finset.sum_congr rfl fun j hj =>
      by rw [h_result_other j (Nat.ne_of_lt (Finset.mem_range.mp hj))]
  rw [heq_prefix, hresultK]
  linear_combination h_sum

/-- The natural number interpretation of the 4-limb U64 array obtained from
    reading 32 bytes of `self.bytes` into four 64-bit limbs equals
    `U8x32_as_Nat self.bytes`.

    More precisely, given:
    * `s` — the byte slice equal to `self.bytes.to_slice`,
    * `res1` — the mutable-borrow pair from indexing a 4-element U64 array
      (its second component `res1.2` reassembles the array from a new slice), and
    * `s2` — the U64 slice produced by `read_le_u64_into`,

    the recombined array `res1.2 s2` represents the same 256-bit integer as the
    original 32 bytes of the scalar. -/
private lemma X64_as_Nat_eq_U8x32_as_Nat
    (self : Scalar)
    (s2 : Slice U64)
    (res1 : Slice U64 × (Slice U64 → Std.Array U64 4#usize))
    (hres1 : res1.1.val = List.slice 0 4 ↑(Array.repeat 4#usize 0#u64) ∧
             res1.1.length = 4 - 0 ∧
        ∀ (s' : Slice U64),
            (res1.2 s').val = ((Array.repeat 4#usize 0#u64).val).setSlice! 0 ↑s')
    (s2_post2 : U64Slice_as_Nat s2 ↑res1.1.len =
          ∑ j ∈ Finset.range (8 * res1.1.len), ((self.bytes.to_slice)[j]!).val * 2 ^ (8 * j)) :
    X64_as_Nat (res1.2 s2) = U8x32_as_Nat self.bytes := by
  have helem : ∀ i : ℕ, i < 4 →
      ((res1.2 s2).val[i]!).val = (s2.val[i]!).val := fun i hi4 => by
    rw [hres1.2.2 s2, Array.repeat_val]
    unfold List.setSlice!
    simp only [List.take_zero, List.nil_append]
    by_cases hi : i < s2.val.length
    · have h_take_i : i < (List.take (min s2.val.length 4) s2.val).length := by
        simp only [List.length_take]; omega
      grind
    · push_neg at hi
      have hmin : min s2.val.length 4 = s2.val.length := by omega
      grind
  have hx64 : X64_as_Nat (res1.2 s2) = U64Slice_as_Nat s2 4 := by
    simp only [X64_as_Nat, U64Slice_as_Nat, Array.getElem!_Nat_eq]
    apply Finset.sum_congr rfl
    intro i hi_range
    rw [helem i (Finset.mem_range.mp hi_range)]
    ring
  have hn4 : res1.1.len.val = 4 := by
    have := hres1.2.1
    simp only [Slice.length] at this
    grind
  have hpost2 : U64Slice_as_Nat s2 4 =
      ∑ j ∈ Finset.range 32, (self.bytes.to_slice.val[j]!).val * 2 ^ (8 * j) := by
    have h := s2_post2
    simp only [hn4, Nat.reduceMul, Slice.getElem!_Nat_eq, Array.val_to_slice] at h
    exact h
  rw [hx64, hpost2, U8x32_as_Nat]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Array.getElem!_Nat_eq, Array.val_to_slice]
  grind

/-! ## The Main Spec Theorem -/

set_option maxHeartbeats 4000000 in
-- The proof dispatches to as_radix_2w_loop_spec_strong across three branches
-- (w = 4, w = 8, w ∈ {5,6,7}), each with substantial step-tactic overhead.
/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_2w`**
• No panic: the function always returns successfully for any valid scalar input
• The signed-digit base-2^w representation of the result equals the scalar's integer value:
  `I8x64_as_Radix2w w result = U8x32_as_Nat self.bytes`
-/
@[step]
theorem as_radix_2w_spec (self : Scalar) (w : Std.Usize)
    (h_lo : 4 ≤ w.val) (h_hi : w.val ≤ 8)
    (h_top : (self.bytes[31]!).val ≤ 127) :
    as_radix_2w self w ⦃ (result : Array Std.I8 64#usize) =>
      I8x64_as_Radix2w w.val result = ↑(U8x32_as_Nat self.bytes) ⦄ := by
  simp only [as_radix_2w]
  step (config := { maxSteps := 1 }) as ⟨w_ge4⟩
  step (config := { maxSteps := 1 }) as ⟨w_le8⟩
  -- Branch on w = 4
  split_ifs with hw4
  · -- Case w = 4: delegate to as_radix_16
    have hw4_val : w.val = 4 := by scalar_tac
    apply spec_mono (as_radix_16_spec self h_top)
    intro result ⟨h_val, _⟩
    rw [hw4_val, I8x64_as_Radix2w_4_eq_Radix16]
    exact h_val
  · -- Case w = 8: carry is folded into digits[digits_count]
    have hw_ge5 : 5 ≤ w.val := by scalar_tac
    have hw_ne4 : w.val ≠ 4 := by scalar_tac
    step
    step as ⟨res1, hres1⟩
    step with read_le_u64_into_spec s res1.1 res1.1.len (by simp) (by grind)
    step
    step
    step
    step
    step
    step with as_radix_2w_loop_spec { start := 0#usize, «end» := digits_count }
      w (res1.2 s2) radix window_mask 0#u64 (Array.repeat 64#usize 0#i8) _
        (X64_as_Nat (res1.2 s2))
    · simp_all only [UScalar.ofNatCore_val_eq, Nat.reduceLeDiff, le_refl,
      Array.getElem!_Nat_eq, ge_iff_le,
      UScalar.le_equiv, Nat.not_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      Nat.reduceLT, or_true, or_self,
      UScalar.val_not_eq_imp_not_eq, Array.repeat_val, List.slice_zero_j, List.take_replicate,
      min_self, Slice.length, tsub_zero, Usize.ofNatCore_val_eq, List.length_replicate,
      Nat.reduceMul, Array.val_to_slice,
      UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, U64.ofNat_bv, BitVec.reduceHShiftLeft,
      Nat.reduceShiftLeft, Nat.reduceAdd, Nat.add_one_sub_one, Nat.one_le_ofNat, Nat.reduceDiv]
      scalar_tac
    · have hi1 : i1.val = 255 + w.val := by scalar_tac
      rw [hi1]
      exact X64_as_Nat_lt_pow_w_digits_count _ w.val hw_ge5 h_hi
    · simp only [UScalar.ofNatCore_val_eq, Finset.range_zero, Array.getElem!_Nat_eq,
      Array.repeat_val, Finset.sum_empty, CharP.cast_eq_zero,
      pow_zero, mul_one, add_zero, mul_zero, Int.natCast_emod,
      Nat.cast_one, EuclideanDomain.mod_one]
    · simp only [UScalar.ofNatCore_val_eq, zero_le, Array.getElem!_Nat_eq,
       Array.repeat_val, forall_const]
      grind
    step
    step
    step
    step as ⟨res, hres, hres32⟩
    have hw8 : w.val = 8 := by grind
    have hK_lt : digits_count.val < 64 := by
      have hi1 : i1.val = 255 + w.val := by scalar_tac
      simp_all only [UScalar.ofNatCore_val_eq, Nat.reduceLeDiff, le_refl, Array.getElem!_Nat_eq,
      ge_iff_le, UScalar.le_equiv, Nat.not_eq, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      Nat.reduceLT, or_true, or_self, UScalar.val_not_eq_imp_not_eq, Array.repeat_val,
      List.slice_zero_j, List.take_replicate, min_self, Slice.length,
      tsub_zero, Usize.ofNatCore_val_eq, List.length_replicate, Nat.reduceMul, Array.val_to_slice,
      UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, U64.ofNat_bv, BitVec.reduceHShiftLeft,
      Nat.reduceShiftLeft, Nat.reduceAdd, Nat.add_one_sub_one, Nat.one_le_ofNat,
      Nat.reduceDiv, zero_add]
    have h_nat_eq : X64_as_Nat (res1.2 s2) = U8x32_as_Nat self.bytes := by
      apply X64_as_Nat_eq_U8x32_as_Nat
      all_goals simp_all
    rw [show w.val = 8 from hw8]
    apply carry_fold_value_w8 digits_count.val (U8x32_as_Nat self.bytes) result.2 res result.1
    · exact hK_lt
    · rw [digits_count_post]
      exact result_post4
    · rw [← h_nat_eq, digits_count_post, ← hw8]
      exact result_post1
    · rw [congrArg IScalar.val hres32]
      rw [i2_post, i3_post] at i4_post
      rw [i4_post]
      simp only [Array.getElem!_Nat_eq, add_right_inj]
      exact UScalar.hcast_inBounds_spec IScalarTy.I8 result.1
        (by simp only [IScalar.max]; scalar_tac)
    · intro j hj
      rw [congrArg IScalar.val (hres j hj)]
  · -- Case w ∈ {5, 6, 7}: general radix-2^w algorithm
    have hw_ge5 : 5 ≤ w.val := by scalar_tac
    have hw_ne4 : w.val ≠ 4 := by scalar_tac
    step
    step as ⟨res1, hres1⟩
    step with read_le_u64_into_spec s res1.1 res1.1.len (by simp) (by grind)
    step
    step
    · simp only [UScalar.ofNatCore_val_eq, radix_post1, Nat.shiftLeft_eq, one_mul]
      simp_all only [Array.getElem!_Nat_eq, ge_iff_le, UScalar.le_equiv, UScalar.ofNatCore_val_eq,
      Nat.not_eq, ne_eq, not_false_eq_true, ReduceNat.reduceNatEq, lt_or_lt_iff_ne,
      or_self, UScalar.val_not_eq_imp_not_eq, UScalar.neq_to_neq_val, Array.repeat_val,
      List.slice_zero_j, List.take_replicate, min_self, Slice.length, tsub_zero,
      Usize.ofNatCore_val_eq, List.length_replicate, Nat.reduceMul, Array.val_to_slice,
      UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, U64.ofNat_bv]
      have : 2 ^ w.val % U64.size = 2 ^ w.val := by
        apply Nat.mod_eq_of_lt
        simp only [U64.size]
        apply Nat.pow_lt_pow_of_lt (by simp)
        scalar_tac
      rw [this]
      exact Nat.one_le_two_pow
    step
    step
    step
    step with as_radix_2w_loop_spec { start := 0#usize, «end» := digits_count }
      w (res1.2 s2) radix window_mask 0#u64 (Array.repeat 64#usize 0#i8) _
        (X64_as_Nat (res1.2 s2))
    · simp_all only [Nat.shiftLeft_eq, one_mul]
      apply Nat.mod_eq_of_lt
      simp only [U64.size]
      apply Nat.pow_lt_pow_of_lt (by simp)
      scalar_tac
    · simp_all only [Nat.shiftLeft_eq, one_mul]
      have h2w_lt : 2 ^ w.val < U64.size := by
        simp only [U64.size]
        exact Nat.pow_lt_pow_right (by norm_num) (by scalar_tac)
      have : 2 ^ w.val % U64.size = 2 ^ w.val := by
        apply Nat.mod_eq_of_lt
        simp only [U64.size]
        apply Nat.pow_lt_pow_of_lt (by simp)
        scalar_tac
      rw [this]
    · have hi1 : i1.val = 255 + w.val := by scalar_tac
      rw [hi1]
      exact X64_as_Nat_lt_pow_w_digits_count _ w.val hw_ge5 h_hi
    · have hi1 : i1.val = 255 + w.val := by scalar_tac
      simp_all only [Array.getElem!_Nat_eq, ge_iff_le, UScalar.le_equiv, UScalar.ofNatCore_val_eq,
      Nat.not_eq, ne_eq, not_false_eq_true, ReduceNat.reduceNatEq, lt_or_lt_iff_ne, or_self,
      UScalar.val_not_eq_imp_not_eq, UScalar.neq_to_neq_val, Array.repeat_val, List.slice_zero_j,
      List.take_replicate, min_self, Slice.length, tsub_zero, Usize.ofNatCore_val_eq,
      List.length_replicate, Nat.reduceMul, Array.val_to_slice, UScalarTy.U64_numBits_eq,
      Bvify.U64.UScalar_bv, U64.ofNat_bv, Nat.succ_add_sub_one]
      exact digits_count_le_64 w.val hw_ge5 h_hi
    · have hi1 : i1.val = 255 + w.val := by scalar_tac
      simp_all only [Array.getElem!_Nat_eq, ge_iff_le, UScalar.le_equiv, UScalar.ofNatCore_val_eq,
      Nat.not_eq, ne_eq, not_false_eq_true, ReduceNat.reduceNatEq, lt_or_lt_iff_ne, or_self,
      UScalar.val_not_eq_imp_not_eq, UScalar.neq_to_neq_val, Array.repeat_val, List.slice_zero_j,
      List.take_replicate, min_self, Slice.length, tsub_zero, Usize.ofNatCore_val_eq,
      List.length_replicate, Nat.reduceMul, Array.val_to_slice, UScalarTy.U64_numBits_eq,
      Bvify.U64.UScalar_bv, U64.ofNat_bv, Nat.succ_add_sub_one]
      exact digits_count_mul_le w.val
    · simp only [UScalar.ofNatCore_val_eq, Finset.range_zero, Array.getElem!_Nat_eq,
      Array.repeat_val, Finset.sum_empty, CharP.cast_eq_zero, pow_zero, mul_one, add_zero,
      mul_zero, Int.natCast_emod, Nat.cast_one, EuclideanDomain.mod_one]
    · simp only [UScalar.ofNatCore_val_eq, zero_le, Array.getElem!_Nat_eq,
      Array.repeat_val, forall_const]
      grind
    have hw_le7 : w.val ≤ 7 := by grind
    have hi1_eq : i1.val = 255 + w.val := by scalar_tac
    have carry_is_zero : result.1.val = 0 :=
      final_carry_is_zero w.val (i1.val / w.val) (X64_as_Nat (res1.2 s2)) result.2
        hw_ge5 hw_le7
        (by rw [hi1_eq])
        (X64_as_Nat_lt_pow256 (res1.2 s2))
        result.1.val result_post2 result_post1
        (fun j hj => (result_post3 j hj).1)
    step
    step
    step
    · -- 1 ≤ digits_count (needed for i4 = digits_count - 1)
      have hi1 : i1.val = 255 + w.val := by scalar_tac
      have hpos := digits_count_pos w.val hw_ge5 (by grind)
      simp_all only [Array.getElem!_Nat_eq, ge_iff_le, UScalar.le_equiv, UScalar.ofNatCore_val_eq,
      Nat.not_eq, ne_eq, not_false_eq_true, ReduceNat.reduceNatEq, lt_or_lt_iff_ne, or_self,
      UScalar.val_not_eq_imp_not_eq, UScalar.neq_to_neq_val, Array.repeat_val, List.slice_zero_j,
      List.take_replicate, min_self, Slice.length, tsub_zero, Usize.ofNatCore_val_eq,
      List.length_replicate, Nat.reduceMul, Array.val_to_slice, UScalarTy.U64_numBits_eq,
      Bvify.U64.UScalar_bv, U64.ofNat_bv, Nat.succ_add_sub_one,
      CharP.cast_eq_zero, zero_mul, add_zero, zero_le, Nat.zero_shiftLeft, Nat.zero_mod]
    step
    · -- i4 < result.2.length (needed to index into result.2)
      have hi1 : i1.val = 255 + w.val := by scalar_tac
      have h64 := digits_count_le_64 w.val hw_ge5 (by grind)
      have hlen : result.2.length = 64 := by simp
      simp_all only [Array.getElem!_Nat_eq, ge_iff_le, UScalar.le_equiv, UScalar.ofNatCore_val_eq,
      Nat.not_eq, ne_eq, not_false_eq_true, ReduceNat.reduceNatEq, lt_or_lt_iff_ne,
      or_self, UScalar.val_not_eq_imp_not_eq, UScalar.neq_to_neq_val, Array.repeat_val,
      List.slice_zero_j, List.take_replicate, min_self, Slice.length, tsub_zero,
      Usize.ofNatCore_val_eq, List.length_replicate, Nat.reduceMul, Array.val_to_slice,
      UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, U64.ofNat_bv, Nat.succ_add_sub_one,
      CharP.cast_eq_zero, zero_mul,
      add_zero, zero_le, Nat.zero_shiftLeft, Nat.zero_mod, Array.length,
      List.Vector.length_val, gt_iff_lt]
      omega
    step
    · have hi3_zero : i3.val = 0 := by
        simp_all only [Array.getElem!_Nat_eq, ge_iff_le, UScalar.le_equiv,
        UScalar.ofNatCore_val_eq,
        Nat.not_eq, ne_eq, not_false_eq_true, ReduceNat.reduceNatEq, lt_or_lt_iff_ne, or_self,
        UScalar.val_not_eq_imp_not_eq, UScalar.neq_to_neq_val, Array.repeat_val, List.slice_zero_j,
        List.take_replicate, min_self, Slice.length, tsub_zero,
        Usize.ofNatCore_val_eq, List.length_replicate, Nat.reduceMul, Array.val_to_slice,
        UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, U64.ofNat_bv, Nat.succ_add_sub_one,
        CharP.cast_eq_zero, zero_mul, add_zero, zero_le, Nat.zero_shiftLeft, Nat.zero_mod]
        have : (UScalar.hcast IScalarTy.I8 i2).val = i2.val := by
          exact UScalar.hcast_inBounds_spec IScalarTy.I8 i2
            (by simp only [IScalar.max]; scalar_tac)
        rw [this]
        simp_all
      have hi4_lt : i4.val < i1.val / w.val := by
        simp_all
        omega
      grind [show -(2 ^ (w.val - 1) : ℤ) ≥ -128 from by interval_cases w.val <;> norm_num]
    · have hi3_zero : i3.val = 0 := by
        simp_all only [Array.getElem!_Nat_eq, ge_iff_le, UScalar.le_equiv,
        UScalar.ofNatCore_val_eq, Nat.not_eq, ne_eq,
        not_false_eq_true, ReduceNat.reduceNatEq, lt_or_lt_iff_ne, or_self,
        UScalar.val_not_eq_imp_not_eq, UScalar.neq_to_neq_val, Array.repeat_val, List.slice_zero_j,
        List.take_replicate, min_self, Slice.length, tsub_zero,
        Usize.ofNatCore_val_eq, List.length_replicate, Nat.reduceMul, Array.val_to_slice,
        UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv, U64.ofNat_bv, Nat.succ_add_sub_one,
        CharP.cast_eq_zero, zero_mul, add_zero, zero_le, Nat.zero_shiftLeft, Nat.zero_mod]
        have : (UScalar.hcast IScalarTy.I8 i2).val = i2.val := by
          exact UScalar.hcast_inBounds_spec IScalarTy.I8 i2
            (by simp only [IScalar.max]; scalar_tac)
        rw [this]
        simp_all
      have hi4_lt : i4.val < digits_count.val := by
        simp_all
        omega
      grind [show (2 ^ (w.val - 1) : ℤ) ≤ 64 from by interval_cases w.val <;> norm_num]
    step as ⟨res, hres, hres32⟩
    · simp_all
      have := digits_count_le_64 w.val hw_ge5 h_hi
      grind
    have h_nat_eq : X64_as_Nat (res1.2 s2) = U8x32_as_Nat self.bytes := by
      apply X64_as_Nat_eq_U8x32_as_Nat
      all_goals simp_all
    apply carry_fold_value_w_ne8 w.val digits_count.val (U8x32_as_Nat self.bytes) res
    · have hi1 : i1.val = 255 + w.val := by scalar_tac
      simp only [digits_count_post, i1_post1, i_post, Nat.succ_add_sub_one, ge_iff_le]
      exact digits_count_le_64 w.val hw_ge5 h_hi
    · intro j hj1 hj2
      have hjne : j ≠ i4.val := by
        simp only [i4_post1, digits_count_post, ne_eq]
        omega
      rw [congrArg IScalar.val (hres j hjne)]
      rw [digits_count_post ] at hj1
      exact result_post4 j hj1 hj2
    · rw [← h_nat_eq]
      convert result_post1 using 1
      · rw [digits_count_post, carry_is_zero]
        simp only [Array.getElem!_Nat_eq, zero_mul, add_zero, CharP.cast_eq_zero]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < i1.val / w.val := Finset.mem_range.mp hj
        by_cases hjne : j = i4.val
        · subst hjne
          simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
            ne_eq, false_and, or_false]
          simp only [Array.getElem!_Nat_eq] at hres32
          rw [hres32, i6_post, i5_post]
          have hi3_zero : i3.val = 0 := by
            simp only [i3_post]
            have : (UScalar.hcast IScalarTy.I8 i2).val = i2.val := by
              exact UScalar.hcast_inBounds_spec IScalarTy.I8 i2
                (by simp only [IScalar.max]; scalar_tac)
            rw [this]
            simp only [carry_is_zero, Nat.zero_shiftLeft, Nat.zero_mod] at i2_post1
            simp only [i2_post1, CharP.cast_eq_zero]
          simp only [hi3_zero, add_zero]
        · simp only [mul_eq_mul_left_iff, pow_eq_zero_iff',
          OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
          have := hres j hjne
          simp only [Array.getElem!_Nat_eq] at this
          simp only [this]

end curve25519_dalek.scalar.Scalar
