/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16`: loop 0

Converts the 32-byte little-endian representation of a scalar into a
64-element signed nibble array in radix 16, filling entries in pairs.

The loop runs for `i` from a starting index up to 32. In iteration `i`:
  - `output[2*i]     ← UScalar.hcast .I8 (bot_half(self.bytes[i]))`
    where `bot_half(b) = (b >> 0) & 15 = b.val % 16` ∈ `[0, 15]`
  - `output[2*i + 1] ← UScalar.hcast .I8 (top_half(self.bytes[i]))`
    where `top_half(b) = (b >> 4) & 15 = b.val / 16` ∈ `[0, 15]`

Both casts succeed because nibble values lie in `[0, 15] ⊆ [0, 127]`, which fits
in an `i8`.  The two-nibble identity
  `(b % 16) · 16^(2·i) + (b / 16) · 16^(2·i+1) = b · 256^i`
ensures that each iteration preserves `I8x64_as_Radix16`.  Summing over all
`i < 32` yields
  `I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes)`
after the loop completes.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
set_option linter.hashCommand false -- #setup_aeneas_simps unavoidably triggers this linter
#setup_aeneas_simps
attribute [-simp] Int.reducePow Nat.reducePow
namespace curve25519_dalek.scalar.Scalar.as_radix_16

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16::bot_half`**:
• The function always succeeds (no panic) for any `u8` input.
• The result is the lower nibble (low 4 bits) of `x`:
  `result.val = x.val % 16`
• The result is a valid nibble: `result.val ≤ 15`.
• Together with `top_half`, the byte decomposes as:
  `(bot_half x).val + 16 * (top_half x).val = x.val`
-/
@[step]
theorem bot_half_spec (x : U8) :
    bot_half x ⦃ (result : U8) =>
      result.val = x.val % 16 ∧
      result.val ≤ 15 ⦄ := by
  unfold bot_half
  step as ⟨i, hi_val, _⟩
  have hx_bound : x.val < 256 := x.hBounds
  have hi_eq : i.val = x.val := by
    rw [hi_val, Nat.shiftRight_eq_div_pow]
    norm_num
  have h15 : (15#u8 : U8).val = 15 := by decide
  have hmod_lt : x.val % 16 ≤ 15 := by omega
  have hland : x.val &&& 15 = x.val % 16 := by
    have h := land_pow_two_sub_one_eq_mod x.val 4
    norm_num at h
    exact h
  simp [step_simps, UScalar.val_and, hi_eq, h15, hland]
  omega

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16::top_half`**:
• The function always succeeds (no panic) for any `u8` input.
• The result is the upper nibble (high 4 bits) of `x`:
  `result.val = x.val / 16`
• The result is a valid nibble: `result.val ≤ 15`.
• Together with `bot_half`, the byte decomposes as:
  `(bot_half x).val + 16 * (top_half x).val = x.val`
-/
@[step]
theorem top_half_spec (x : U8) :
    top_half x ⦃ (result : U8) =>
      result.val = x.val / 16 ∧
      result.val ≤ 15 ⦄ := by
  unfold top_half
  step as ⟨i, hi_val, _⟩
  have hx_bound : x.val < 256 := x.hBounds
  have hi_eq : i.val = x.val / 16 := by
    rw [hi_val, Nat.shiftRight_eq_div_pow]
  have h15 : (15#u8 : U8).val = 15 := by decide
  have hdiv_lt : x.val / 16 < 16 := Nat.div_lt_of_lt_mul (by omega)
  have hland : x.val / 16 &&& 15 = x.val / 16 := by
    have h := land_pow_two_sub_one_eq_mod (x.val / 16) 4
    norm_num at h
    rw [h, Nat.mod_eq_of_lt hdiv_lt]
  simp [step_simps, UScalar.val_and, hi_eq, h15, hland]
  omega

end curve25519_dalek.scalar.Scalar.as_radix_16

namespace curve25519_dalek.scalar.Scalar

/-- Interpret a 64-element `i8` array as a signed integer in base 16.
    Each `digits[i]` contributes `digits[i].val * 16^i` to the sum, where
    `.val` is the `ℤ`-valued (signed) lift of the `i8` entry.
    This is the reference value that `as_radix_16` computes. -/
def I8x64_as_Radix16 (digits : Array I8 64#usize) : ℤ :=
  ∑ i ∈ Finset.range 64, (16 : ℤ)^i * (digits[i]!).val

private lemma nibble_identity (b i : ℕ) :
    (↑(b % 16) : ℤ) * (16 : ℤ) ^ (2 * i) + (↑(b / 16) : ℤ) * (16 : ℤ) ^ (2 * i + 1) =
    ↑b * (256 : ℤ) ^ i := by
  have h256 : (16 : ℤ) ^ (2 * i) = (256 : ℤ) ^ i := by
    rw [pow_mul]
    ring_nf
  have h16 : (16 : ℤ) ^ (2 * i + 1) = 16 * (256 : ℤ) ^ i := by
    rw [pow_succ, h256]; ring
  have hb : (↑b : ℤ) = ↑(b % 16) + 16 * ↑(b / 16) := by
    push_cast
    have := Nat.div_add_mod b 16
    omega
  rw [h256, h16, hb]
  ring

@[step]
private lemma I8x64_update_get (arr : Array I8 64#usize) (j : Usize)
    (v : I8) (hj : j.val < 64) :
    Array.update arr j v ⦃ (arr' : Array I8 64#usize) =>
    (∀ (k : ℕ), (hk : k ≠ j.val) → (arr')[k]! = arr[k]!) ∧
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

private lemma inv_step
    (self : Scalar) (output a : Array I8 64#usize) (i : ℕ)
    (i4 : I8) (hi4 : i4.val = ↑((self.bytes[i]!).val % 16))
    (i7 : I8) (hi7 : i7.val = ↑((self.bytes[i]!).val / 16))
    (ha_even : (a)[2 * i]! = i4)
    (ha_odd : (a)[2 * i + 1]! = i7)
    (ha_pref : ∀ j < 2 * i, (a[j]! : I8).val = (output[j]!).val)
    (h_inv : ∑ j ∈ Finset.range (2 * i), (16 : ℤ) ^ j * (output[j]!).val =
             ↑(∑ k ∈ Finset.range i, 2 ^ (8 * k) * (self.bytes[k]!).val)) :
    ∑ j ∈ Finset.range (2 * (i + 1)), (16 : ℤ) ^ j * (a[j]!).val =
    ↑(∑ k ∈ Finset.range (i + 1), 2 ^ (8 * k) * (self.bytes[k]!).val) := by
  have h2i1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
  rw [h2i1, Finset.sum_range_succ, show 2 * i + 1 = 2 * i + 0 + 1 from by ring,
      Finset.sum_range_succ]
  have ha_odd_val : ((a)[2 * i + 1]!).val = ↑((self.bytes[i]!).val / 16) := by
    rw [ha_odd]; exact hi7
  have ha_even_val : ((a)[2 * i]!).val = ↑((self.bytes[i]!).val % 16) := by
     rw [ha_even]; exact hi4
  have h_pref_sum : ∑ j ∈ Finset.range (2 * i), (16 : ℤ) ^ j * (a[j]!).val =
                    ∑ j ∈ Finset.range (2 * i), (16 : ℤ) ^ j * (output[j]!).val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ha_pref j (Finset.mem_range.mp hj)]
  rw [h_pref_sum, h_inv, ha_even_val, ha_odd_val]
  push_cast [Finset.sum_range_succ]
  have h_nibble := nibble_identity (self.bytes[i]!).val i
  simp only [Array.getElem!_Nat_eq, add_zero, add_assoc, add_right_inj]
  simp only [Array.getElem!_Nat_eq, Int.natCast_emod, Nat.cast_ofNat, mul_comm, Int.natCast_ediv]
    at h_nibble
  simp only [mul_comm]
  rw [h_nibble]
  simp only [mul_eq_mul_right_iff, Int.natCast_eq_zero]
  left
  have h256 : (2 : ℤ) ^ (8 * i) = (256 : ℤ) ^ i := by
    rw [show (256 : ℤ) = 2 ^ 8 from by norm_num, ← pow_mul]
  grind

private lemma tail_step
    (output a : Array I8 64#usize) (i : ℕ)
    (ha_later : ∀ j, 2 * (i + 1) ≤ j → j < 64 → (a[j]! : I8).val = (output[j]!).val)
    (h_tail : ∀ j, 2 * i ≤ j → j < 64 → (output[j]! : I8).val = 0) :
    ∀ j, 2 * (i + 1) ≤ j → j < 64 → (a[j]! : I8).val = 0 := by
  intro j hj1 hj2
  rw [ha_later j hj1 hj2]
  exact h_tail j (by omega) hj2

private lemma bounds_step
    (output a : Array I8 64#usize) (i : ℕ)
    (i4 i7 : I8)
    (hi4_pos : (0 : ℤ) ≤ i4.val) (hi4_le : i4.val ≤ 15)
    (hi7_pos : (0 : ℤ) ≤ i7.val) (hi7_le : i7.val ≤ 15)
    (ha_even : (a)[2 * i]! = i4)
    (ha_odd : (a)[2 * i + 1]! = i7)
    (ha_pref : ∀ j < 2 * i, (a[j]! : I8).val = (output[j]!).val)
    (h_bounds : ∀ j < 2 * i, (0 : ℤ) ≤ (output[j]!).val ∧ (output[j]!).val ≤ 15) :
    ∀ j < 2 * (i + 1), (0 : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val ≤ 15 := by
  intro j hj
  rcases lt_or_ge j (2 * i) with hlt | hge
  · have hval : (a[j]!).val = (output[j]!).val := ha_pref j hlt
    rw [hval]; exact h_bounds j hlt
  · rcases Nat.eq_or_lt_of_le hge with rfl | hlt
    · rw [ha_even]; exact ⟨hi4_pos, hi4_le⟩
    · have hj_eq : j = 2 * i + 1 := by omega
      subst hj_eq; rw [ha_odd]; exact ⟨hi7_pos, hi7_le⟩

private theorem as_radix_16_loop0_spec_strong
    (self : Scalar)
    (output : Array I8 64#usize)
    (i : Usize)
    (hi : i.val ≤ 32)
    (h_inv : ∑ j ∈ Finset.range (2 * i.val), (16 : ℤ) ^ j * (output[j]!).val =
             ↑(∑ k ∈ Finset.range i.val, 2 ^ (8 * k) * (self.bytes[k]!).val))
    (h_tail : ∀ j, 2 * i.val ≤ j → j < 64 → (output[j]! : I8).val = 0)
    (h_bounds : ∀ j < 2 * i.val,
        (0 : ℤ) ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    as_radix_16_loop0 self output i ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes) ∧
      ∀ k < 64, (0 : ℤ) ≤ (result[k]!).val ∧ (result[k]!).val ≤ 15 ⦄ := by
  unfold as_radix_16_loop0
  split
  case isTrue hlt =>
    have hi' : i.val < 32 := by scalar_tac
    unfold Scalar.Insts.CoreOpsIndexIndexUsizeU8.index
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2_val, hi2_le⟩
    step as ⟨i3, hi3⟩
    have h_cast2 : i2.val < 128 := by omega
    step as ⟨i4, hi4⟩
    have h_i3_lt : i3.val < 64 := by omega
    step as ⟨output1, h_upd1⟩
    step as ⟨i5, hi5_val, hi5_le⟩
    step as ⟨i6, hi6⟩
    have hi6_val : i6.val = 2 * i.val + 1 := by scalar_tac
    have h_cast5 : i5.val < 128 := by omega
    step as ⟨i7, hi7⟩
    have h_i6_lt : i6.val < 64 := by omega
    step as ⟨a, h_upd2⟩
    step as ⟨i8, hi8⟩
    have hi8_val : i8.val = i.val + 1 := by scalar_tac
    have h_hi4 : i4.val = ↑((self.bytes[i.val]!).val % 16) := by
      have h := hi2_val; rw [hi1] at h
      have hspec := UScalar.hcast_inBounds_spec .I8 i2 (by
      simp only [IScalar.max]; scalar_tac)
      simp only [lift, WP.spec_ok] at hspec
      rw [hi4, hspec]
      simp[h]
    have h_hi7 : i7.val = ↑((self.bytes[i.val]!).val / 16) := by
      have h := hi5_val; rw [hi1] at h
      have hspec := UScalar.hcast_inBounds_spec .I8 i5 (by
      simp only [IScalar.max]; scalar_tac)
      simp only [lift, WP.spec_ok] at hspec
      rw [hi7, hspec]
      simp[h]
    have ha_even : a[2 * i.val]! = i4 := by
      have h6_ne_3 : i3.val ≠ i6.val := by omega
      simp_all
    have ha_odd : a[2 * i.val + 1]! = i7 := by
      simp_all
    have ha_pref : ∀ j < 2 * i.val, (a[j]! : I8).val = (output[j]!).val := by
      intro j hj
      have eq:= h_upd1 j
      simp only [hi3, ne_eq, Array.getElem!_Nat_eq] at eq
      have : ¬j = 2 * ↑i := by grind
      simp only [this, not_false_eq_true, forall_const] at eq
      have eq1:= h_upd2 j
      simp only [hi6_val, ne_eq, Array.getElem!_Nat_eq] at eq1
      have : ¬j = 2 * ↑i +1 := by grind
      simp only [this, not_false_eq_true, forall_const] at eq1
      simp only [Array.getElem!_Nat_eq, eq1, eq]
    have ha_later : ∀ j, 2 * (i.val + 1) ≤ j → j < 64 →
      (a[j]! : I8).val = (output[j]!).val := by
      intro j hj1 hj2
      have eq := h_upd1 j
      simp only [hi3, ne_eq, Array.getElem!_Nat_eq] at eq
      have hne1 : ¬j = 2 * ↑i := by grind
      simp only [hne1, not_false_eq_true, forall_const] at eq
      have eq1 := h_upd2 j
      simp only [hi6_val, ne_eq, Array.getElem!_Nat_eq] at eq1
      have hne2 : ¬j = 2 * ↑i + 1 := by grind
      simp only [hne2, not_false_eq_true, forall_const] at eq1
      simp only [Array.getElem!_Nat_eq, eq1, eq]
    have h_inv' : ∑ j ∈ Finset.range (2 * i8.val), (16 : ℤ) ^ j * (a[j]!).val =
                  ↑(∑ k ∈ Finset.range i8.val, 2 ^ (8 * k) * (self.bytes[k]!).val) := by
      rw [hi8_val]
      exact inv_step self output a i.val i4 h_hi4 i7 h_hi7
              ha_even ha_odd ha_pref h_inv
    have h_tail' : ∀ j, 2 * i8.val ≤ j → j < 64 → (a[j]! : I8).val = 0 := by
      rw [hi8_val]
      exact tail_step output a i.val ha_later h_tail
    have h_bounds' : ∀ j < 2 * i8.val, (0 : ℤ) ≤ (a[j]!).val ∧ (a[j]!).val ≤ 15 := by
      rw [hi8_val]
      apply bounds_step output a i.val i4 i7
      · have hbot := hi2_le  -- i2.val ≤ 15
        push_cast [h_hi4]
        grind
      · have hbot := hi2_le
        push_cast [h_hi4]
        grind
      · have htop := hi5_le  -- i5.val ≤ 15
        push_cast [h_hi7]
        grind
      · have htop := hi5_le
        push_cast [h_hi7]
        grind
      · exact ha_even
      · exact ha_odd
      · exact ha_pref
      · exact h_bounds
    exact as_radix_16_loop0_spec_strong self a i8 (by omega) h_inv' h_tail' h_bounds'
  case isFalse hge =>
    have hi_eq : i.val = 32 := by grind
    refine ⟨?_, ?_⟩
    · unfold I8x64_as_Radix16 U8x32_as_Nat
      rw [hi_eq] at h_inv
      rw [← h_inv]
    · intro k hk
      exact h_bounds k (by omega)
  termination_by 32 - i.val
  decreasing_by
    simp only [hi8_val]
    omega

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16_loop0`**:
• The function always succeeds (no panic) for valid inputs.
• The result satisfies `I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes)`.
• Every nibble of the result lies in `[0, 15]`:
  `∀ k < 64, 0 ≤ (result[k]!).val ∧ (result[k]!).val ≤ 15`
-/
@[step]
theorem as_radix_16_loop0_spec
    (self : Scalar)
    (output : Array I8 64#usize)
    (i : Usize)
    (hi : i.val ≤ 32)
    (h_inv : ∑ j ∈ Finset.range (2 * i.val), (16 : ℤ) ^ j * (output[j]!).val =
             ↑(∑ k ∈ Finset.range i.val, 2 ^ (8 * k) * (self.bytes[k]!).val))
    (h_tail : ∀ j, 2 * i.val ≤ j → j < 64 → (output[j]! : I8).val = 0)
    (h_bounds : ∀ j < 2 * i.val,
        (0 : ℤ) ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    as_radix_16_loop0 self output i ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes) ∧
      ∀ k < 64, (0 : ℤ) ≤ (result[k]!).val ∧ (result[k]!).val ≤ 15 ⦄ :=
  as_radix_16_loop0_spec_strong self output i hi h_inv h_tail
    h_bounds

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16`: loop 1

Recenters a 64-element signed nibble array from the unsigned range `[0, 16)`
into the signed range `[−8, 8)` by carry propagation.

The loop runs for `i` from a starting index up to 63. In each iteration `i`:
  - `carry      ← (output[i] + 8) >>> 4`    ∈ {0, 1}
  - `output[i]  ← output[i] − carry <<< 4`  (recenters digit `i` to `[−8, 7]`)
  - `output[i+1] ← output[i+1] + carry`     (propagates carry to the next digit)

The carry step is value-preserving because
  `(d − carry·16)·16^i + (d′ + carry)·16^(i+1) = d·16^i + d′·16^(i+1)`,
which follows immediately by `ring`.

The loop invariant maintains three properties simultaneously:
1. **Value preservation** — `I8x64_as_Radix16 output = V` for a fixed integer `V`
   (the value produced by loop 0).
2. **Recentered prefix** — every digit at a position `j < i` lies in `[−8, 7]`.
3. **Bounded tail** — digit `i` lies in `[0, 16]` (it may have received a carry
   from the previous step), and every digit `j > i` still lies in `[0, 15]`
   (untouched since loop 0).

After the loop completes (all 63 iterations), every digit `j < 63` is recentered
to `[−8, 7]`, and digit 63 is bounded in `[0, 16]`.  The precondition from the
outer `as_radix_16` function (`self[31] ≤ 127`) ensures that after loop 0 digit 63
is at most 7, and after at most one carry from digit 62 it is at most 8.

Source: "curve25519-dalek/src/scalar.rs"
-/

private lemma carry_recenter_identity (d d' c : ℤ) (i : ℕ) :
    (d - c * 16) * (16 : ℤ) ^ i + (d' + c) * (16 : ℤ) ^ (i + 1) =
    d * (16 : ℤ) ^ i + d' * (16 : ℤ) ^ (i + 1) := by
  ring

private lemma carry_zero_or_one (d : ℤ) (hlo : 0 ≤ d) (hhi : d ≤ 16) :
    (d + 8) / 16 = 0 ∨ (d + 8) / 16 = 1 := by
  omega

private lemma recenter_in_range (d : ℤ) :
    -8 ≤ d - (d + 8) / 16 * 16 ∧ d - (d + 8) / 16 * 16 ≤ 7 := by
  omega

private lemma next_digit_bounded (d' carry : ℤ)
    (hd_lo : 0 ≤ d') (hd_hi : d' ≤ 15)
    (hc : carry = 0 ∨ carry = 1) :
    0 ≤ d' + carry ∧ d' + carry ≤ 16 := by
  omega

@[step]
private theorem isize_shiftRight_4_spec (i : I8) (h_lo : 0 ≤ i.val) (h_hi : i.val ≤ 24) :
    i >>> 4#i32 ⦃ (r : I8) =>
      r.val = i.val / 16 ∧
      0 ≤ r.val ∧
      r.val ≤ 1        ⦄ := by
  simp only [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar,
             IScalar.shiftRight, IScalar.toNat, IScalar.val]
  norm_num
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · simp only [IScalar.val]
    rw [BitVec.sshiftRight_eq]
    rw [BitVec.toInt_ofInt]
    rw [I8.bv_toInt_eq]
    change (i.val >>> (4 : Nat)).bmod (2 ^ 8) = i.val / 16
    have hmatch : i.val >>> (4 : Nat) = i.val / 16 := by
      rw [Int.shiftRight_eq_div_pow]; norm_num
    rw [hmatch]
    exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 7 (i.val / 16)
      (by norm_num; omega) (by norm_num; omega)
  · simp only [IScalar.val]
    rw [BitVec.sshiftRight_eq, BitVec.toInt_ofInt, I8.bv_toInt_eq]
    change 0 ≤ (i.val >>> (4 : Nat)).bmod (2 ^ 8)
    have hmatch : i.val >>> (4 : Nat) = i.val / 16 := by
      rw [Int.shiftRight_eq_div_pow]; norm_num
    rw [hmatch]
    have hbnd := Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 7 (i.val / 16)
      (by norm_num; omega) (by norm_num; omega)
    grind
  · simp only [IScalar.val]
    rw [BitVec.sshiftRight_eq, BitVec.toInt_ofInt, I8.bv_toInt_eq]
    change (i.val >>> (4 : Nat)).bmod (2 ^ 8) ≤ 1
    have hmatch : i.val >>> (4 : Nat) = i.val / 16 := by
      rw [Int.shiftRight_eq_div_pow]; norm_num
    rw [hmatch]
    have hbnd := Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 7 (i.val / 16)
      (by norm_num; omega) (by norm_num; omega)
    grind

@[step]
private theorem isize_shiftLeft_4_spec (i : I8)
    (h_lo : -8 ≤ i.val) (h_hi : i.val ≤ 7) :
    i <<< 4#i32 ⦃ (r : I8) =>
      r.val = i.val * 16 ⦄ := by
  simp only [HShiftLeft.hShiftLeft, IScalar.shiftLeft_IScalar, IScalar.shiftLeft,
             IScalar.toNat, IScalar.val]
  norm_num
  simp only [IScalarTy.I32_numBits_eq, BitVec.reduceToInt,
    Nat.ofNat_nonneg, ↓reduceIte, Int.reduceLT,
    IScalarTy.I8_numBits_eq, Int.reduceToNat, spec_ok]
  simp only [HShiftLeft.hShiftLeft]
  have hbv : (i.bv.shiftLeft 4 : BitVec 8) = i.bv * (16 : BitVec 8) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq]
  rw [hbv]
  simp only [IScalar.val]
  rw [BitVec.toInt_mul, show (16 : BitVec 8).toInt = 16 from by decide, I8.bv_toInt_eq]
  exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 7 (i.val * 16)
    (by norm_num; omega) (by norm_num; omega)

private lemma inv_step_loop1
    (output a : Array I8 64#usize) (i : ℕ) (hi : i < 63)
    (V : ℤ)
    (carry : ℤ)
    (ha_curr : (a[i]!).val = (output[i]!).val - carry * 16)
    (ha_next : (a[i + 1]!).val = (output[i + 1]!).val + carry)
    (ha_other : ∀ j, j ≠ i → j ≠ i + 1 → (a[j]! : I8).val = (output[j]!).val)
    (h_val : I8x64_as_Radix16 output = V) :
    I8x64_as_Radix16 a = V := by
  unfold I8x64_as_Radix16 at *
  rw [← h_val]
  have key : ∀ j ∈ Finset.range 64,
      (16 : ℤ)^j * (a[j]!).val =
      (16 : ℤ)^j * (output[j]!).val +
      (if j = i then -(carry * 16) * (16 : ℤ)^j else 0) +
      (if j = i + 1 then carry * (16 : ℤ)^j else 0) := by
    intro j _
    by_cases h1 : j = i
    · subst h1
      simp only [show j ≠ j + 1 from by omega, ite_false, add_zero]
      simp
      grind
    · by_cases h2 : j = i + 1
      · subst h2
        simp only [show i + 1 ≠ i from by omega, ite_false]
        grind
      · simp only [if_neg h1, if_neg h2, add_zero]
        linear_combination (16 : ℤ)^j * ha_other j h1 h2
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hi64  : i ∈ Finset.range 64     := Finset.mem_range.mpr (by omega)
  have hi164 : i + 1 ∈ Finset.range 64 := Finset.mem_range.mpr (by omega)
  rw [if_pos hi64, if_pos hi164]
  linarith [show -(carry * 16) * (16 : ℤ)^i + carry * (16 : ℤ)^(i + 1) = 0 from by ring]

private lemma lo_bounds_step
    (i4 : I8) (d : ℤ)
    (hi4 : i4.val = d - (d + 8) / 16 * 16) :
    -8 ≤ (i4 : I8).val ∧ (i4 : I8).val ≤ 7 := by
  have h := recenter_in_range d
  omega

private lemma tail_step_loop1
    (output a : Array I8 64#usize) (i : ℕ)
    (ha_other : ∀ j, j ≠ i → j ≠ i + 1 → (a[j]! : I8).val = (output[j]!).val)
    (h_tail : ∀ j, i < j → j < 64 →
        0 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    ∀ j, i + 1 < j → j < 64 →
        0 ≤ (a[j]! : I8).val ∧ (a[j]! : I8).val ≤ 15 := by
  intro j hj1 hj2
  rw [ha_other j (by omega) (by omega)]
  exact h_tail j (by omega) hj2

private lemma lo_bounds_prefix_step
    (output a : Array I8 64#usize) (i : ℕ)
    (i4 : I8)
    (hi4_lo : -8 ≤ (i4 : I8).val) (hi4_hi : (i4 : I8).val ≤ 7)
    (ha_curr : a[i]! = i4)
    (ha_other : ∀ j, j ≠ i → j ≠ i + 1 → (a[j]! : I8).val = (output[j]!).val)
    (h_lo : ∀ j < i,
        -8 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val < 8) :
    ∀ j < i + 1, -8 ≤ (a[j]!).val ∧ (a[j]!).val < 8 := by
  intro j hj
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt | rfl
  · rw [ha_other j (by omega) (by omega)]
    exact h_lo j hjlt
  · rw [ha_curr]
    exact ⟨hi4_lo, by omega⟩

/-! ## The Main Inductive Proof (Strong Form) -/


/-- **Stronger loop 1 spec** tracking all invariant components together:

    Invariants maintained at loop-counter `i`:
    1. `I8x64_as_Radix16 output = V` (value preserved throughout).
    2. `∀ j < i, −8 ≤ output[j].val ∧ output[j].val < 8` (recentered prefix).
    3. `0 ≤ output[i].val ∧ output[i].val ≤ 16` (current digit; may have
       received a carry from the previous step).
    4. `∀ j, i < j → j < 64 → 0 ≤ output[j].val ∧ output[j].val ≤ 15`
       (digits beyond `i` are still from loop 0).

    On exit (i ≥ 63, so i = 63): the loop returns `output` with
    - every digit `j < 63` recentered to `[−8, 7]`,
    - digit 63 bounded in `[0, 16]`. -/
private theorem as_radix_16_loop1_spec_strong
    (output : Array I8 64#usize)
    (i : Usize)
    (V : ℤ)
    (hi : i.val ≤ 63)
    (h_val : I8x64_as_Radix16 output = V)
    (h_lo : ∀ j < i.val,
        -8 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val < 8)
    (h_curr : 0 ≤ (output[i.val]! : I8).val ∧
              (output[i.val]! : I8).val ≤ 16)
    (h_tail : ∀ j, i.val < j → j < 64 →
        0 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    as_radix_16_loop1 output i ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = V ∧
      (∀ j < 63, -8 ≤ (result[j]!).val ∧ (result[j]!).val < 8) ∧
      0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 16 ⦄ := by
  unfold as_radix_16_loop1
  split
  case isTrue hlt =>
    have hi' : i.val < 63 := by scalar_tac
    have h_i_lt : i.val < 64 := by omega
    step as ⟨i1, hi1⟩
    have h_i1_val : i1.val = (output[i.val]!).val := by
      simp [hi1]
    have h_i1_lo : 0 ≤ i1.val := by rw [h_i1_val]; exact h_curr.1
    have h_i1_hi : i1.val ≤ 16   := by rw [h_i1_val]; exact h_curr.2
    step as ⟨i2, hi2⟩
    step with isize_shiftRight_4_spec i2
      (by simp_all; omega) (by simp_all; omega) as ⟨carry, hcarry⟩
    have h_carry_val : carry.val = (i1.val + 8) / 16 := by
      simp[hcarry,hi2]
    have h_carry_01 : carry.val = 0 ∨ carry.val = 1 := by
      have h := carry_zero_or_one i1.val h_i1_lo h_i1_hi
      omega
    step with isize_shiftLeft_4_spec carry (by omega) (by omega) as ⟨i3, hi3⟩
    step as ⟨i4, hi4⟩
    step as ⟨output1, h_upd1⟩
    step as ⟨i5, hi5⟩
    have hi5_val : i5.val = i.val + 1 := by scalar_tac
    have h_i5_lt : i5.val < 64 := by omega
    step as ⟨i6, hi6⟩
    step as ⟨i7, hi7⟩
    step as ⟨a, h_upd2⟩
    have h_carry_val : carry.val = (i1.val + 8) / 16 := by
      simp_all
    have h_carry_01 : carry.val = 0 ∨ carry.val = 1 := by
      have h := carry_zero_or_one i1.val h_i1_lo h_i1_hi
      omega
    have h_i4_val : i4.val = i1.val - carry.val * 16 := by
      simp_all
    have h_i7_val : i7.val = (output[i.val + 1]!).val + carry.val := by
      simp_all
    have ha_curr_eq : a[i.val]! = i4 := by
      have hne : i5.val ≠ i.val := by omega
      have h2 := h_upd2 i.val (by rw [hi5_val]; omega)
      simp only [h2]
      simp_all
    have ha_next_eq : a[i.val + 1]! = i7 := by
      rw [← hi5_val]
      simp_all
    have ha_other : ∀ j, j ≠ i.val → j ≠ i.val + 1 →
        (a[j]! : I8).val = (output[j]!).val := by
      intro j hj1 hj2
      have eq2 := h_upd2 j (by rw [hi5_val]; exact hj2)
      simp only [eq2]
      have eq1 := h_upd1 j hj1
      simp only [eq1]
    have h_val' : I8x64_as_Radix16 a = V := by
      apply inv_step_loop1 output a i.val hi' V carry
      · rw [ha_curr_eq, h_i4_val, h_i1_val]
      · rw [ha_next_eq, h_i7_val]
      · intro j hj1 hj2; exact ha_other j hj1 hj2
      · exact h_val
    have h_i4_rng := recenter_in_range i1.val
    have h_i4_lo : -8 ≤ i4.val := by
      rw [h_i4_val, h_carry_val]; linarith [h_i4_rng.1]
    have h_i4_hi : i4.val ≤ 7 := by
      rw [h_i4_val, h_carry_val]; linarith [h_i4_rng.2]
    have h_lo' : ∀ j < i5.val, -8 ≤ (a[j]!).val ∧ (a[j]!).val < 8 := by
      rw [hi5_val]
      apply lo_bounds_prefix_step output a i.val i4 h_i4_lo h_i4_hi ha_curr_eq
      · intro j hj1 hj2
        exact ha_other j hj1 (by rw [← hi5_val]; simp_all)
      · exact h_lo
    have h_curr' : 0 ≤ (a[i5.val]!).val ∧ (a[i5.val]!).val ≤ 16 := by
      rw [hi5_val, ha_next_eq, h_i7_val]
      have h_next := h_tail (i.val + 1) (by omega) (by omega)
      exact next_digit_bounded (output[i.val + 1]!).val carry.val
        h_next.1 h_next.2 h_carry_01
    have h_tail' : ∀ j, i5.val < j → j < 64 →
        0 ≤ (a[j]!).val ∧ (a[j]!).val ≤ 15 := by
      rw [hi5_val]
      apply tail_step_loop1 output a i.val
      · intro j hj1 hj2
        exact ha_other j hj1 (by rw [← hi5_val]; simp_all)
      · exact h_tail
    exact as_radix_16_loop1_spec_strong a i5 V (by omega)
      h_val' h_lo' h_curr' h_tail'
  case isFalse hge =>
    have hi_eq : i.val = 63 := by scalar_tac
    refine ⟨h_val, ?_, ?_⟩
    · intro j hj
      exact h_lo j (by omega)
    · rw [hi_eq] at h_curr
      exact ⟨h_curr.1, h_curr.2⟩
  termination_by 63 - i.val
  decreasing_by
    simp only [hi5_val]
    omega

/-! ## The Published Spec Theorem -/

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16_loop1`**:
• The function always succeeds (no panic).
• Value preservation: `I8x64_as_Radix16 result = V`.
• All interior digits are recentered:
  `∀ j < 63, −8 ≤ (result[j]!).val ∧ (result[j]!).val < 8`
• The last digit is bounded: `0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 16`.
-/
@[step]
theorem as_radix_16_loop1_spec
    (output : Array I8 64#usize)
    (i : Usize)
    (V : ℤ)
    (hi : i.val ≤ 63)
    (h_val : I8x64_as_Radix16 output = V)
    (h_lo : ∀ j < i.val,
        -8 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val < 8)
    (h_curr : 0 ≤ (output[i.val]! : I8).val ∧
              (output[i.val]! : I8).val ≤ 16)
    (h_tail : ∀ j, i.val < j → j < 64 →
        0 ≤ (output[j]! : I8).val ∧ (output[j]! : I8).val ≤ 15) :
    as_radix_16_loop1 output i ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = V ∧
      (∀ j < 63, -8 ≤ (result[j]!).val ∧ (result[j]!).val < 8) ∧
      0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 16 ⦄ :=
  as_radix_16_loop1_spec_strong output i V hi h_val h_lo h_curr h_tail

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16`

Converts a 32-byte little-endian scalar into a 64-element signed radix-16 digit
array with recentered coefficients in `[-8, 8)`.  The algorithm proceeds in three
phases:

1. **Assertion**: checks `self[31] ≤ 127` (top bit is clear, i.e., the scalar
   value is strictly less than `2^255`), preventing `i8` overflow at digit 63
   after carry propagation.
2. **Loop 0** (`as_radix_16_loop0`, 32 iterations): splits each byte into two
   nibbles.  For each `i ∈ [0, 32)`:
   - `output[2*i]     ← bot_half(self.bytes[i]) = (self.bytes[i] >> 0) & 15`
   - `output[2*i + 1] ← top_half(self.bytes[i]) = (self.bytes[i] >> 4) & 15`
   Every nibble value lies in `[0, 15]`, and the loop invariant maintains
   `∑ j < 2*k, (16:ℤ)^j * output[j].val = ↑(∑ j < k, 2^(8*j) * self.bytes[j].val)`.
3. **Loop 1** (`as_radix_16_loop1`, 63 iterations): recenters digits from
   `[0, 16)` to `[-8, 8)` by carry propagation.  For each `i ∈ [0, 63)`:
   - `carry      ← (output[i] + 8) >> 4` ∈ {0, 1}
   - `output[i]  ← output[i] − carry · 16` ∈ [−8, 7]
   - `output[i+1] ← output[i+1] + carry`
   The value is preserved because
     `(output[i] − carry·16)·16^i + (output[i+1] + carry)·16^(i+1)`
     `= output[i]·16^i + output[i+1]·16^(i+1)`.
   Digit 63 is not recentered; the precondition `self[31] ≤ 127` guarantees
   `output[63] ≤ 7` after loop 0, and the final carry from digit 62 is at
   most 1, so `output[63] ≤ 8` after loop 1.

Source: "curve25519-dalek/src/scalar.rs"
-/

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::as_radix_16`**:
• The function succeeds (no panic) if and only if `self.bytes[31].val ≤ 127`.
• The result represents the same integer as `self` in signed base 16:
  `I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes)`
• All interior digits are recentered:
  `∀ i < 63, −8 ≤ (result[i]!).val ∧ (result[i]!).val < 8`
• The last digit is bounded: `0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 16`.
-/
@[step]
theorem as_radix_16_spec (self : Scalar)
    (h_top : (self.bytes[31]!).val ≤ 127) :
    as_radix_16 self ⦃ (result : Array I8 64#usize) =>
      I8x64_as_Radix16 result = ↑(U8x32_as_Nat self.bytes) ∧
      (∀ i < 63, -8 ≤ (result[i]!).val ∧ (result[i]!).val < 8) ∧
      0 ≤ (result[63]!).val ∧ (result[63]!).val ≤ 16 ⦄ := by
  simp only [as_radix_16]
  unfold scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8.index
  step as ⟨i1, hi1⟩
  step*
  · simp
  · simp only [UScalar.ofNatCore_val_eq, mul_zero, zero_le, Array.getElem!_Nat_eq,
      Array.repeat_val, List.replicate, forall_const]
    decide

end curve25519_dalek.scalar.Scalar
