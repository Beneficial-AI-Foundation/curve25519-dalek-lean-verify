/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.Lfactor
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::montgomery_reduce`

This function performs Montgomery reduction.

Source: "curve25519-dalek/src/backend/serial/u64/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 416

-- Bridge lemma: converts the existing LFACTOR_spec (on Nat) to the form needed for Int arithmetic
private lemma LFACTOR_prop :
    (↑constants.LFACTOR.val * ↑constants.L[0]!.val : Int) % (2 ^ 52) = (2 ^ 52) - 1 := by
  have h_nat := constants.LFACTOR_spec
  obtain ⟨h_mod_zero, _, _⟩ := h_nat
  have h_cong : (constants.L[0]!.val : Int) % (2^52) = (_root_.L : Int) % (2^52) := by
    rw [← constants.L_spec]; unfold Scalar52_as_Nat
    rw [Finset.sum_range_succ']; zify at h_mod_zero ⊢; simp only [mul_zero, pow_zero, one_mul]
    rw [Int.add_emod]
    have h_tail_div : (∑ x ∈ Finset.range 4, (2:Int)^(52 * (x + 1)) *
      (constants.L[x.succ]!).val) % 2^52 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      use (∑ x ∈ Finset.range 4, (2:Int)^(52 * x) * (constants.L[x.succ]!).val)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_tail_div, zero_add, Int.emod_emod]
  rw [mul_comm, Int.mul_emod, h_cong, ← Int.mul_emod]
  rw [← Int.add_sub_cancel (_root_.L * ↑constants.LFACTOR.val : Int) 1, Int.sub_emod]; norm_cast
  rw [h_mod_zero]; exact rfl

/-- The "Montgomery Step": Proves that adding the reduction factor clears the lower 52 bits. -/
private lemma mont_step (x : Int) (p : Int) (carry_out : Int)
    (hp : p = (x * ↑constants.LFACTOR.val) % (2 ^ 52))
    (hcarry : carry_out = (x + p * ↑constants.L[0]!.val) / (2 ^ 52)) :
    x + p * ↑constants.L[0]!.val = carry_out * (2 ^ 52) := by
  have h_div : x + p * ↑constants.L[0]!.val =
    carry_out * (2 ^ 52) + (x + p * ↑constants.L[0]!.val) % (2 ^ 52) := by
    rw [hcarry]
    rw [mul_comm ((x + p * ↑constants.L[0]!.val) / 2 ^ 52)]
    rw [Int.mul_ediv_add_emod]
  have h_mod_zero : (x + p * ↑constants.L[0]!.val) % (2 ^ 52) = 0 := by
    rw [hp, Int.add_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, mul_assoc, Int.mul_emod]
    rw [LFACTOR_prop]
    rw [← Int.zero_emod (2 ^ 52)]
    have h_cast : (2 : Int) ^ 52 = ((2 ^ 52 : Nat) : Int) := by norm_cast
    rw [h_cast]
    apply (ZMod.intCast_eq_intCast_iff' _ _ (2^52)).mp
    simp only [Int.cast_add, ZMod.intCast_mod, Int.cast_mul, Int.cast_sub]
    simp only [Nat.reducePow, Nat.cast_ofNat, Int.cast_ofNat, Aeneas.ReduceZMod.reduceZMod,
      Int.cast_one, zero_sub, mul_neg, mul_one, add_neg_cancel, Int.cast_zero]
  rw [h_div, h_mod_zero, add_zero]


private theorem part1_spec_tail (sum i5 : U128) (p : U64)
    (h_p_val : p.val = (sum.val * constants.LFACTOR) % (2 ^ 52))
    (h_p_bound : p.val < 2 ^ 52)
    (h_add : sum.val + i5.val ≤ U128.max)
    (h_i5_eq : i5.val = p.val * (constants.L[0]!).val) :
    (do
      let i6 ← sum + i5
      let i7 ← i6 >>> 52#i32
      ok (i7, p)) ⦃ result =>
      let (carry, p') := result
      p'.val = (sum.val * constants.LFACTOR) % (2 ^ 52) ∧
      carry.val = (sum.val + p'.val * (constants.L[0]!).val) / (2 ^ 52) ∧
      carry.val < 2 ^ 77 ∧
      p'.val < 2 ^ 52 ⦄ := by
  step as ⟨i6, i6_post⟩
  step as ⟨i7, i7_post⟩
  refine ⟨h_p_val, ?_, ?_, h_p_bound⟩
  · rw [i7_post, i6_post, h_i5_eq]; simp only [Nat.shiftRight_eq_div_pow]
  · rw [i7_post, i6_post]; simp only [Nat.shiftRight_eq_div_pow]; scalar_tac

@[step]
private theorem part1_spec (sum : U128)
    (h_bound : sum.val + (2 ^ 52 - 1) * (constants.L[0]!).val ≤ U128.max) :
    montgomery_reduce.part1 sum ⦃ result =>
    let (carry, p) := result
    p.val = (sum.val * constants.LFACTOR) % (2 ^ 52) ∧
    carry.val = (sum.val + p.val * (constants.L[0]!).val) / (2 ^ 52) ∧
    carry.val < 2 ^ 77 ∧
    p.val < 2 ^ 52 ⦄ := by
  unfold montgomery_reduce.part1
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  have h_L_len : constants.L.val.length = 5 := by
    unfold constants.L; rfl
  step as ⟨i, i_post⟩
  step as ⟨i1, i1_post⟩
  step as ⟨i2, i2_post⟩
  step as ⟨i3, i3_post⟩
  step as ⟨p, p_post⟩
  have h_p_val : p.val = (sum.val * constants.LFACTOR) % (2 ^ 52) := by
      rw [p_post]; simp only [UScalar.val_and]
      have h_mask : i3.val = 2^52 - 1 := by
        simp only [i3_post, i2_post]; scalar_tac
      rw [h_mask]; rw [i1_post, i_post]
      rw [land_pow_two_sub_one_eq_mod]
      simp only [UScalar.cast, UScalar.val, core.num.U64.wrapping_mul]
      simp only [UScalarTy.U64_numBits_eq, UScalar.wrapping_mul_bv_eq, UScalar.bv_toNat,
        Aeneas.Bvify.U64.UScalar_bv]
      rw [BitVec.toNat_mul, BitVec.toNat_setWidth, UScalar.bv_toNat, Nat.mod_mul_mod]
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 2^52 ∣ 2^64)]
      rfl
  have h_p_bound : p.val < 2^52 := by
      rw [h_p_val]; apply Nat.mod_lt; norm_num
  have h_add_safe : sum.val + p.val * (constants.L[0]!).val ≤ U128.max := by
      apply Nat.le_trans (m := sum.val + (2^52 - 1) * (constants.L[0]!).val)
      · apply Nat.add_le_add_left; apply Nat.mul_le_mul_right; apply Nat.le_pred_of_lt h_p_bound
      · exact h_bound
  step as ⟨i4, i4_post⟩
  step as ⟨i5, i5_post⟩
  have h_add_safe' : sum.val + i5.val ≤ U128.max := by
    rw [i5_post, i4_post]
    convert h_add_safe using 2
    simp only [Array.getElem!_Nat_eq]
  have h_i5_eq : i5.val = p.val * (constants.L[0]!).val := by
    rw [i5_post, i4_post]
    simp only [Array.getElem!_Nat_eq]
  exact part1_spec_tail sum i5 p h_p_val h_p_bound h_add_safe' h_i5_eq

@[step]
private theorem part2_spec (sum : U128) :
  montgomery_reduce.part2 sum ⦃ result =>
  let (carry, w) := result
  w.val = sum.val % (2 ^ 52) ∧
  carry.val = sum.val / (2 ^ 52) ∧
  carry.val < 2 ^ 76 ∧
  w.val < 2 ^ 52 ⦄ := by -- 2^128 / 2^52 = 2^76
  unfold montgomery_reduce.part2
  -- Rust: let w = (sum as u64) & ((1u64 << 52) - 1);
  step as ⟨w_cast, hw_cast⟩     -- Cast sum to u64
  step as ⟨mask1, hmask1⟩       -- 1 << 52
  step as ⟨mask, hmask⟩         -- (1 << 52) - 1
  step as ⟨w, hw⟩               -- Bitwise AND
  -- Rust: (sum >> 52, w)
  step as ⟨carry, hcarry⟩       -- Shift right
  have h_w_val : w.val = sum.val % 2^52 := by
    rw [hw]; simp only [UScalar.val_and]
    have h_mask_val : mask.val = 2^52 - 1 := by
      simp only [hmask, hmask1]; scalar_tac
    rw [h_mask_val]; rw [land_pow_two_sub_one_eq_mod]; rw [hw_cast]
    simp only [UScalar.cast, UScalarTy.U64_numBits_eq, BitVec.truncate_eq_setWidth]
    change (BitVec.setWidth 64 sum.bv).toNat % 2^52 = _
    rw [BitVec.toNat_setWidth]
    change (sum.val % 2^64) % 2^52 = _
    apply Nat.mod_mod_of_dvd; scalar_tac
  have h_carry_val : carry.val = sum.val / 2^52 := by
    rw [hcarry]
    simp only [Nat.shiftRight_eq_div_pow]
  have h_w_bound : w.val < 2^52 := by
    rw [h_w_val]; apply Nat.mod_lt; norm_num
  have h_carry_bound : carry.val < 2^76 := by
    rw [h_carry_val]; apply Nat.div_lt_of_lt_mul
    calc sum.val < 2^128 := sum.hBounds
         _ = 2^76 * 2^52 := by norm_num
  exact ⟨h_w_val, h_carry_val, h_carry_bound, h_w_bound⟩

/-- From `Scalar52_wide_as_Nat a < R * L`, derive `a[8]!.val < 2^97`.
    Keeps all exponents ≤ 416 (within threshold) by rewriting `2^260 * 2^253 = 2^416 * 2^97`. -/
private lemma a8_bound_of_canonical (a : Aeneas.Std.Array U128 9#usize)
    (h_canonical : Scalar52_wide_as_Nat a < R * L) : a[8]!.val < 2 ^ 97 := by
  have h_limb := Scalar52_wide_limb_le_nat a 8 (by omega)
  simp only [show 52 * 8 = 416 from rfl] at h_limb
  have hL : L < 2 ^ 253 := by unfold L; omega
  -- 2^260 * 2^253 = 2^416 * 2^97 (both = 2^513, but keep symbolic)
  have key : (2 : Nat) ^ 260 * 2 ^ 253 = 2 ^ 416 * 2 ^ 97 := by
    rw [← pow_add, ← pow_add]
  -- Chain: 2^416 * a[8]! ≤ S52waN a < R * L = 2^260 * L < 2^260 * 2^253 = 2^416 * 2^97
  have : 2 ^ 416 * a[8]!.val < 2 ^ 416 * 2 ^ 97 := by
    calc 2 ^ 416 * a[8]!.val
        ≤ Scalar52_wide_as_Nat a := h_limb
      _ < R * L := h_canonical
      _ = 2 ^ 260 * L := by dsimp [R]
      _ < 2 ^ 260 * 2 ^ 253 := by apply Nat.mul_lt_mul_of_pos_left hL; positivity
      _ = 2 ^ 416 * 2 ^ 97 := key
  exact (Nat.mul_lt_mul_left (show 0 < 2 ^ 416 from by positivity)).mp this

/-- REDC bound: from the main equation `T + N*L = inter*R` and canonical bound `T < R*L`,
    with `0 ≤ N < R`, the intermediate satisfies `inter < 2*L`. -/
private lemma redc_bound {inter T : Nat} {C : Int}
    (h_eq : (T : Int) + C * ↑L = ↑inter * ↑R)
    (h_T : T < R * L) (h_C_nn : 0 ≤ C) (h_C_lt : C < ↑R) :
    inter < 2 * L := by
  have hR_pos : 0 < R := by decide
  have hL_pos : 0 < L := by decide
  have h_cn := Int.toNat_of_nonneg h_C_nn
  have h_c_lt : C.toNat < R := by
    have := h_C_lt; rw [← h_cn] at this; exact_mod_cast this
  have h_eq_nat : inter * R = T + C.toNat * L := by
    have : (↑(inter * R) : Int) = ↑(T + C.toNat * L) := by
      push_cast; rw [h_cn]; linarith [h_eq]
    exact_mod_cast this
  have h_bound : inter * R < 2 * L * R := by
    rw [h_eq_nat]; have := (Nat.mul_lt_mul_right hL_pos).mpr h_c_lt; grind => lia
  exact (Nat.mul_lt_mul_right hR_pos).mp h_bound

/-- Core Montgomery identity: from the 9 carry/split equations, derive
    `a + C*L = inter * R` where B = 2^52, R = B^5.
    Proved by telescoping linear combination; lives outside main proof for context hygiene. -/
private lemma montgomery_core_eq
    {B a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℤ}
    {n0 n1 n2 n3 n4 : ℤ}
    {c0 c1 c2 c3 c4 : ℤ}
    {r0 r1 r2 r3 r4 : ℤ}
    {n5 n6 n7 : ℤ}
    {L0 L1 L2 L4 : ℤ}
    (eq0 : a0 + n0 * L0 = c0 * B)
    (eq1 : c0 + a1 + n0 * L1 + n1 * L0 = c1 * B)
    (eq2 : c1 + a2 + n0 * L2 + n1 * L1 + n2 * L0 = c2 * B)
    (eq3 : c2 + a3 + n1 * L2 + n2 * L1 + n3 * L0 = c3 * B)
    (eq4 : c3 + a4 + n0 * L4 + n2 * L2 + n3 * L1 + n4 * L0 = c4 * B)
    (eq5 : c4 + a5 + n1 * L4 + n3 * L2 + n4 * L1 = n5 * B + r0)
    (eq6 : n5 + a6 + n2 * L4 + n4 * L2 = n6 * B + r1)
    (eq7 : n6 + a7 + n3 * L4 = n7 * B + r2)
    (eq8 : n7 + a8 + n4 * L4 = r4 * B + r3) :
    (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3 + a4 * B ^ 4 +
     a5 * B ^ 5 + a6 * B ^ 6 + a7 * B ^ 7 + a8 * B ^ 8) +
    (n0 + n1 * B + n2 * B ^ 2 + n3 * B ^ 3 + n4 * B ^ 4) *
    (L0 + L1 * B + L2 * B ^ 2 + L4 * B ^ 4) =
    (r0 + r1 * B + r2 * B ^ 2 + r3 * B ^ 3 + r4 * B ^ 4) * B ^ 5 := by
  linear_combination eq0 + eq1 * B + eq2 * B ^ 2 + eq3 * B ^ 3 + eq4 * B ^ 4 +
    eq5 * B ^ 5 + eq6 * B ^ 6 + eq7 * B ^ 7 + eq8 * B ^ 8

/-- A base-B number with 5 digits each < B is < B^5. Used for the Montgomery factor bound. -/
private lemma base_digit_bound {B d0 d1 d2 d3 d4 : ℤ}
    (hB : 0 < B)
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h3 : d3 < B) (h4 : d4 < B)
    (_hnn0 : 0 ≤ d0) (_hnn1 : 0 ≤ d1) (_hnn2 : 0 ≤ d2) (_hnn3 : 0 ≤ d3) (_hnn4 : 0 ≤ d4) :
    d0 + d1 * B + d2 * B ^ 2 + d3 * B ^ 3 + d4 * B ^ 4 < B ^ 5 := by
  -- Each d_k ≤ B-1, so sum ≤ (B-1)(1+B+B²+B³+B⁴) = B⁵-1
  have hBnn : (0 : ℤ) ≤ B := le_of_lt hB
  have hB2 : (0 : ℤ) ≤ B ^ 2 := sq_nonneg _
  have hB3 : (0 : ℤ) ≤ B ^ 3 := by positivity
  have hB4 : (0 : ℤ) ≤ B ^ 4 := by positivity
  have hle : d0 + d1 * B + d2 * B ^ 2 + d3 * B ^ 3 + d4 * B ^ 4 ≤
      (B - 1) * (1 + B + B ^ 2 + B ^ 3 + B ^ 4) := by nlinarith
  linarith [show (B - 1) * (1 + B + B ^ 2 + B ^ 3 + B ^ 4) = B ^ 5 - 1 from by ring]

/-- Product of two values below 2^52 is below 2^104. -/
private theorem mul_lt_pow104 {a b : Nat} (ha : a < 2 ^ 52) (hb : b < 2 ^ 52) :
    a * b < 2 ^ 104 := by
  agrind

/-- Non-trivial shared constants for montgomery_reduce.
Proved separately to avoid adding kernel depth to the main proof. -/
private theorem mont_reduce_consts :
    (constants.L[0]!).val < 2 ^ 52 ∧
    (constants.L[1]!).val < 2 ^ 52 ∧
    (constants.L[2]!).val < 2 ^ 52 ∧
    (constants.L[4]!).val = 2 ^ 44 ∧
    U128.max = 2 ^ 128 - 1 ∧
    (2 ^ 52 - 1) * (constants.L[0]!).val < 2 ^ 104 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using constants.L_limbs_spec 0#usize (by decide)
  · simpa using constants.L_limbs_spec 1#usize (by decide)
  · simpa using constants.L_limbs_spec 2#usize (by decide)
  · unfold constants.L; decide
  · scalar_tac
  · calc (2 ^ 52 - 1) * (constants.L[0]!).val
        < (2 ^ 52 - 1) * 2 ^ 52 := by
          apply Nat.mul_lt_mul_of_pos_left
          · simpa using constants.L_limbs_spec 0#usize (by decide)
          · positivity
      _ < 2 ^ 104 := by omega

set_option maxHeartbeats 2600000 in -- New Aeneas version needs more
/-- Spec theorem for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::montgomery_reduce`
• No panic (always returns successfully)
• The result m satisfies the Montgomery reduction property:
  m * R ≡ a (mod L), where R = 2^260 is the Montgomery constant

**Why `h_canonical` (`Scalar52_wide_as_Nat a < R * L`)**:
The Rust code (scalar.rs:303-306) truncates `carry` from u128 to u64 and performs a single
conditional subtraction. This is only correct when the intermediate result `inter < 2*L`:
- From the REDC identity `inter * R = T + N * L` with `T < R*L` and `N < R`, we get
  `inter * R < R*L + R*L = 2*R*L`, hence `inter < 2*L`.
- A single subtraction of L then guarantees `result < L`.
- Without `T < R*L`, `inter` could be much larger, the u128→u64 truncation would lose bits,
  and the single subtraction would not produce a canonical result.
All callers satisfy this: `mul_internal` produces `m*m' < R*L` when inputs are bounded,
`square_internal` likewise, and `from_montgomery` embeds values trivially smaller than `R*L`. -/
@[step]
theorem montgomery_reduce_spec (a : Array U128 9#usize)
    (h_bounds : ∀ i < 9, a[i]!.val < 2 ^ 127)
    (h_canonical : Scalar52_wide_as_Nat a < R * L) :
    montgomery_reduce a ⦃ m =>
    (Scalar52_as_Nat m * R) % L = Scalar52_wide_as_Nat a % L ∧
    (∀ i < 5, m[i]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat m < L) ⦄
    := by
  unfold montgomery_reduce
  unfold Insts.CoreOpsIndexIndexUsizeU64.index
  simp only [step_simps]
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ result0, h_result0 ⟩ ← part1_spec
  obtain ⟨h_n0_val, h_carry0_val, h_carry0_bound, h_n0_bound⟩ := h_result0
  -- Shared bound library (proved once, reused by all rows)
  -- Import shared constants (proved in separate lemma to avoid kernel depth)
  obtain ⟨h_L0, h_L1, h_L2, h_L4_eq, hmax, h_mask_L0⟩ := mont_reduce_consts
  -- ROW 1 setup: ALL U128.add_spec use spec_bind to avoid deep recursion
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  apply spec_bind; · exact U128.add_spec (by
    have : (↑i1 : Nat) < 2 ^ 127 := by
      rw [show (↑i1 : Nat) = i1.val from rfl, show i1.val = (↑a)[1]!.val from by
        simp [i1_post]]; exact h_bounds 1 (by omega)
    rw [hmax]; omega)
  intro i2 i2_post
  let* ⟨ i3, i3_post ⟩ ← Array.index_usize_spec
  let* ⟨ i4, i4_post ⟩ ← m_spec
  -- ROW 1: i5 = i2 + i4, then part1(i5)
  apply spec_bind; · exact U128.add_spec (by
    have hi1 : (↑i1 : Nat) < 2 ^ 127 := by
      rw [show (↑i1 : Nat) = i1.val from rfl, show i1.val = (↑a)[1]!.val from by
        simp [i1_post]]; exact h_bounds 1 (by omega)
    have hi3 : (↑i3 : Nat) < 2 ^ 52 := by
      rw [show (↑i3 : Nat) = i3.val from rfl, show i3.val = (↑constants.L)[1]!.val from by
        simp [i3_post]]; exact h_L1
    have hi4 : (↑i4 : Nat) < 2 ^ 104 := by rw [i4_post]; nlinarith [h_n0_bound, hi3]
    rw [i2_post, hmax]; omega)
  intro i5 i5_post
  apply spec_bind; · exact part1_spec i5 (by
    have hi1 : (↑i1 : Nat) < 2 ^ 127 := by
      rw [show (↑i1 : Nat) = i1.val from rfl, show i1.val = (↑a)[1]!.val from by
        simp [i1_post]]; exact h_bounds 1 (by omega)
    have hi3 : (↑i3 : Nat) < 2 ^ 52 := by
      rw [show (↑i3 : Nat) = i3.val from rfl, show i3.val = (↑constants.L)[1]!.val from by
        simp [i3_post]]; exact h_L1
    have hi4 : (↑i4 : Nat) < 2 ^ 104 := by rw [i4_post]; nlinarith [h_n0_bound, hi3]
    rw [i5_post, i2_post, hmax]; omega)
  intro result1 ⟨h_n1_val, h_carry1_val, h_carry1_bound, h_n1_bound⟩
  -- ROW 2 setup
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  apply spec_bind; · exact U128.add_spec (by
    have : (↑i6 : Nat) < 2 ^ 127 := by
      rw [show (↑i6 : Nat) = i6.val from rfl, show i6.val = (↑a)[2]!.val from by
        simp [i6_post]]; exact h_bounds 2 (by omega)
    rw [hmax]; omega)
  intro i7 i7_post
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
  let* ⟨ i9, i9_post ⟩ ← m_spec
  have hi8 : (↑i8 : Nat) < 2 ^ 52 := by
    rw [show (↑i8 : Nat) = i8.val from rfl, show i8.val = (↑constants.L)[2]!.val from by
      simp [i8_post]]; exact h_L2
  have hi9 : (↑i9 : Nat) < 2 ^ 104 := by rw [i9_post]; nlinarith [h_n0_bound, hi8]
  have hi6 : (↑i6 : Nat) < 2 ^ 127 := by
    rw [show (↑i6 : Nat) = i6.val from rfl, show i6.val = (↑a)[2]!.val from by
      simp [i6_post]]; exact h_bounds 2 (by omega)
  have hi7 : (↑i7 : Nat) < 2 ^ 77 + 2 ^ 127 := by rw [i7_post]; linarith [h_carry1_bound]
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i10 i10_post
  let* ⟨ i11, i11_post ⟩ ← m_spec
  have hi3 : (↑i3 : Nat) < 2 ^ 52 := by
    rw [show (↑i3 : Nat) = i3.val from rfl, show i3.val = (↑constants.L)[1]!.val from by
      simp [i3_post]]; exact h_L1
  have hi11 : (↑i11 : Nat) < 2 ^ 104 := by rw [i11_post]; nlinarith [h_n1_bound, hi3]
  have hi10 : (↑i10 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 104 := by rw [i10_post]; omega
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i12 i12_post
  -- ROW 2: part1
  have hi12 : (↑i12 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 104 + 2 ^ 104 := by
    rw [i12_post]; omega
  apply spec_bind; · exact part1_spec i12 (by rw [hmax]; omega)
  intro result2 ⟨h_n2_val, h_carry2_val, h_carry2_bound, h_n2_bound⟩
  -- ROW 3 setup
  let* ⟨ i13, i13_post ⟩ ← Array.index_usize_spec
  have hi13 : (↑i13 : Nat) < 2 ^ 127 := by
    rw [show (↑i13 : Nat) = i13.val from rfl, show i13.val = (↑a)[3]!.val from by
      simp [i13_post]]; exact h_bounds 3 (by omega)
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i14 i14_post
  let* ⟨ i15, i15_post ⟩ ← m_spec
  have hi15 : (↑i15 : Nat) < 2 ^ 104 := by rw [i15_post]; nlinarith [h_n1_bound, hi8]
  have hi14 : (↑i14 : Nat) < 2 ^ 77 + 2 ^ 127 := by rw [i14_post]; linarith [h_carry2_bound]
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i16 i16_post
  let* ⟨ i17, i17_post ⟩ ← m_spec
  have hi17 : (↑i17 : Nat) < 2 ^ 104 := by rw [i17_post]; nlinarith [h_n2_bound, hi3]
  have hi16 : (↑i16 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 104 := by rw [i16_post]; omega
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i18 i18_post
  -- ROW 3: part1
  have hi18 : (↑i18 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 104 + 2 ^ 104 := by
    rw [i18_post]; omega
  apply spec_bind; · exact part1_spec i18 (by rw [hmax]; omega)
  intro result3 ⟨h_n3_val, h_carry3_val, h_carry3_bound, h_n3_bound⟩
  -- ROW 4 setup
  let* ⟨ i19, i19_post ⟩ ← Array.index_usize_spec
  have hi19 : (↑i19 : Nat) < 2 ^ 127 := by
    rw [show (↑i19 : Nat) = i19.val from rfl, show i19.val = (↑a)[4]!.val from by
      simp [i19_post]]; exact h_bounds 4 (by omega)
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i20 i20_post
  let* ⟨ i21, i21_post ⟩ ← Array.index_usize_spec
  let* ⟨ i22, i22_post ⟩ ← m_spec
  have hi21 : (↑i21 : Nat) = 2 ^ 44 := by
    rw [show (↑i21 : Nat) = i21.val from rfl, show i21.val = (↑constants.L)[4]!.val from by
      simp [i21_post]]; exact h_L4_eq
  have hi22 : (↑i22 : Nat) < 2 ^ 96 := by rw [i22_post, hi21]; nlinarith [h_n0_bound]
  have hi20 : (↑i20 : Nat) < 2 ^ 77 + 2 ^ 127 := by rw [i20_post]; linarith [h_carry3_bound]
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i23 i23_post
  let* ⟨ i24, i24_post ⟩ ← m_spec
  have hi24 : (i24 : Nat) < 2 ^ 104 := by rw [i24_post]; agrind
  have hi23 : (↑i23 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 96 := by rw [i23_post]; omega
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i25 i25_post
  let* ⟨ i26, i26_post ⟩ ← m_spec
  have hi26 : (↑i26 : Nat) < 2 ^ 104 := by rw [i26_post]; agrind
  have hi25 : (↑i25 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 96 + 2 ^ 104 := by rw [i25_post]; omega
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i27 i27_post
  -- ROW 4: part1
  have hi27 : (↑i27 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 96 + 2 ^ 104 + 2 ^ 104 := by
    rw [i27_post]; omega
  apply spec_bind; · exact part1_spec i27 (by rw [hmax]; omega)
  intro result4 ⟨h_n4_val, h_carry4_val, h_carry4_bound, h_n4_bound⟩
  -- ROW 5 setup (carry4 < 2^77, products < 2^96 or 2^104)
  let* ⟨ i28, i28_post ⟩ ← Array.index_usize_spec
  have hi28 : (↑i28 : Nat) < 2 ^ 127 := by
    rw [show (↑i28 : Nat) = i28.val from rfl, show i28.val = (↑a)[5]!.val from by
      simp [i28_post]]; exact h_bounds 5 (by omega)
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i29 i29_post
  let* ⟨ i30, i30_post ⟩ ← m_spec
  have hi30 : (↑i30 : Nat) < 2 ^ 96 := by
    rw [i30_post, hi21]; exact Nat.mul_lt_mul_of_pos_right h_n1_bound (by positivity)
  have hi29 : (↑i29 : Nat) < 2 ^ 77 + 2 ^ 127 := by rw [i29_post]; linarith [h_carry4_bound]
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i31 i31_post
  let* ⟨ i32, i32_post ⟩ ← m_spec
  have hi32 : (↑i32 : Nat) < 2 ^ 104 := by
    rw [i32_post]; exact mul_lt_pow104 h_n3_bound hi8
  have hi31 : (↑i31 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 96 := by rw [i31_post]; omega
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i33 i33_post
  let* ⟨ i34, i34_post ⟩ ← m_spec
  have hi34 : (↑i34 : Nat) < 2 ^ 104 := by
    rw [i34_post]; exact mul_lt_pow104 h_n4_bound hi3
  have hi33 : (↑i33 : Nat) < 2 ^ 77 + 2 ^ 127 + 2 ^ 96 + 2 ^ 104 := by rw [i33_post]; omega
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i35 i35_post
  -- ROW 5: part2 → r0
  apply spec_bind; · exact part2_spec i35
  intro p2_0 ⟨h_r0_val, h_n5_val, h_n5_bound, h_r0_bound⟩
  -- ROW 6 setup (part2 carry < 2^76)
  let* ⟨ i36, i36_post ⟩ ← Array.index_usize_spec
  have hi36 : (↑i36 : Nat) < 2 ^ 127 := by
    rw [show (↑i36 : Nat) = i36.val from rfl, show i36.val = (↑a)[6]!.val from by
      simp [i36_post]]; exact h_bounds 6 (by omega)
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i37 i37_post
  let* ⟨ i38, i38_post ⟩ ← m_spec
  have hi38 : (↑i38 : Nat) < 2 ^ 96 := by
    rw [i38_post, hi21]; exact Nat.mul_lt_mul_of_pos_right h_n2_bound (by positivity)
  have hi37 : (↑i37 : Nat) < 2 ^ 76 + 2 ^ 127 := by rw [i37_post]; linarith [h_n5_bound]
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i39 i39_post
  let* ⟨ i40, i40_post ⟩ ← m_spec
  have hi40 : (↑i40 : Nat) < 2 ^ 104 := by
    rw [i40_post]; exact mul_lt_pow104 h_n4_bound hi8
  have hi39 : (↑i39 : Nat) < 2 ^ 76 + 2 ^ 127 + 2 ^ 96 := by rw [i39_post]; omega
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i41 i41_post
  -- ROW 6: part2 → r1
  apply spec_bind; · exact part2_spec i41
  intro p2_1 ⟨h_r1_val, h_n6_val, h_n6_bound, h_r1_bound⟩
  -- ROW 7 setup
  let* ⟨ i42, i42_post ⟩ ← Array.index_usize_spec
  have hi42 : (↑i42 : Nat) < 2 ^ 127 := by
    rw [show (↑i42 : Nat) = i42.val from rfl, show i42.val = (↑a)[7]!.val from by
      simp [i42_post]]; exact h_bounds 7 (by omega)
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i43 i43_post
  let* ⟨ i44, i44_post ⟩ ← m_spec
  have hi44 : (↑i44 : Nat) < 2 ^ 96 := by
    rw [i44_post, hi21]; exact Nat.mul_lt_mul_of_pos_right h_n3_bound (by positivity)
  have hi43 : (↑i43 : Nat) < 2 ^ 76 + 2 ^ 127 := by rw [i43_post]; linarith [h_n6_bound]
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i45 i45_post
  -- ROW 7: part2 → r2
  apply spec_bind; · exact part2_spec i45
  intro p2_2 ⟨h_r2_val, h_n7_val, h_n7_bound, h_r2_bound⟩
  -- ROW 8 setup
  let* ⟨ i46, i46_post ⟩ ← Array.index_usize_spec
  have hi46 : (↑i46 : Nat) < 2 ^ 127 := by
    rw [show (↑i46 : Nat) = i46.val from rfl, show i46.val = (↑a)[8]!.val from by
      simp [i46_post]]; exact h_bounds 8 (by omega)
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i47 i47_post
  let* ⟨ i48, i48_post ⟩ ← m_spec
  have hi48 : (↑i48 : Nat) < 2 ^ 96 := by
    rw [i48_post, hi21]; exact Nat.mul_lt_mul_of_pos_right h_n4_bound (by positivity)
  have hi47 : (↑i47 : Nat) < 2 ^ 76 + 2 ^ 127 := by rw [i47_post]; linarith [h_n7_bound]
  apply spec_bind; · exact U128.add_spec (by rw [hmax]; omega)
  intro i49 i49_post
  -- ROW 8: part2 → r3, r4_u128
  apply spec_bind; · exact part2_spec i49
  intro p2_3 ⟨h_r3_val, h_r4u128_val, h_r4u128_bound, h_r3_bound⟩
  -- Cast r4_u128 → r4 (U64)
  let* ⟨ r4, r4_post ⟩ ← UScalar.cast.step_spec
  -- Derive tight r4 bound from h_canonical
  have h_L4 : i21.val = 2 ^ 44 := by
    have := i21_post; rw [this]; unfold constants.L; decide
  have h_a8 : i46.val < 2 ^ 97 := by
    have h1 := a8_bound_of_canonical a h_canonical
    have h2 : i46.val = a[8]!.val := by simp only [i46_post, List.Vector.length_val,
      UScalar.ofNatCore_val_eq, Nat.lt_add_one, getElem!_pos, Array.getElem!_Nat_eq]
    agrind
  have h_i48 : i48.val < 2 ^ 96 := by
    rw [i48_post, h_L4]
    exact Nat.mul_lt_mul_of_pos_right h_n4_bound (by positivity)
  have h_i49_bound : i49.val < 2 ^ 99 := by
    rw [i49_post, i47_post]; linarith [h_n7_bound, h_a8, h_i48]
  have h_r4u128_tight : p2_3.1.val < 2 ^ 47 := by
    rw [h_r4u128_val, Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ 52)]
    calc i49.val < 2 ^ 99 := h_i49_bound
      _ = 2 ^ 47 * 2 ^ 52 := by rw [← pow_add]
  have h_r4_tight : r4.val < 2 ^ 52 := by
    have : r4.val ≤ p2_3.1.val := by
      rw [r4_post]; simp only [U128_cast_U64_val]; exact Nat.mod_le _ _
    linarith
  -- ===== MAIN EQUATION: T + C * L = inter * R (Montgomery identity) =====
  have h_r4_eq : r4.val = p2_3.1.val := by
    rw [r4_post]; simp only [U128_cast_U64_val]
    exact Nat.mod_eq_of_lt (lt_trans h_r4u128_tight (by norm_num))
  zify at h_n0_val h_carry0_val h_n1_val h_carry1_val h_n2_val h_carry2_val
         h_n3_val h_carry3_val h_n4_val h_carry4_val
         h_r0_val h_n5_val h_r1_val h_n6_val h_r2_val h_n7_val h_r3_val h_r4u128_val
  have eq0 := mont_step _ _ _ h_n0_val h_carry0_val
  have eq1 := mont_step _ _ _ h_n1_val h_carry1_val
  have eq2 := mont_step _ _ _ h_n2_val h_carry2_val
  have eq3 := mont_step _ _ _ h_n3_val h_carry3_val
  have eq4 := mont_step _ _ _ h_n4_val h_carry4_val
  have eq5 : (↑i35.val : ℤ) = ↑p2_0.1.val * (2 ^ 52 : ℤ) + ↑p2_0.2.val := by
    rw [h_n5_val, h_r0_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  have eq6 : (↑i41.val : ℤ) = ↑p2_1.1.val * (2 ^ 52 : ℤ) + ↑p2_1.2.val := by
    rw [h_n6_val, h_r1_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  have eq7 : (↑i45.val : ℤ) = ↑p2_2.1.val * (2 ^ 52 : ℤ) + ↑p2_2.2.val := by
    rw [h_n7_val, h_r2_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  have eq8 : (↑i49.val : ℤ) = ↑p2_3.1.val * (2 ^ 52 : ℤ) + ↑p2_3.2.val := by
    rw [h_r4u128_val, h_r3_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  rw [show (↑p2_3.1.val : ℤ) = ↑r4.val from by exact_mod_cast h_r4_eq.symm] at eq8
  simp only [i_post, i1_post, i2_post, i3_post, i4_post, i5_post, i6_post, i7_post, i8_post,
    i9_post, i10_post, i11_post, i12_post, i13_post, i14_post, i15_post, i16_post,
    i17_post, i18_post, i19_post, i20_post, i21_post, i22_post, i23_post, i24_post,
    i25_post, i26_post, i27_post, i28_post, i29_post, i30_post, i31_post, i32_post,
    i33_post, i34_post, i35_post, i36_post, i37_post, i38_post, i39_post, i40_post,
    i41_post, i42_post, i43_post, i44_post, i45_post, i46_post, i47_post, i48_post, i49_post,
    ← Array.getElem!_Nat_eq
  ] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  have h_wide : (↑(Scalar52_wide_as_Nat a) : ℤ) =
      ↑a[0]!.val + ↑a[1]!.val * (2 ^ 52 : ℤ) + ↑a[2]!.val * (2 ^ 52) ^ 2 +
      ↑a[3]!.val * (2 ^ 52) ^ 3 + ↑a[4]!.val * (2 ^ 52) ^ 4 +
      ↑a[5]!.val * (2 ^ 52) ^ 5 + ↑a[6]!.val * (2 ^ 52) ^ 6 +
      ↑a[7]!.val * (2 ^ 52) ^ 7 + ↑a[8]!.val * (2 ^ 52) ^ 8 := by
    unfold Scalar52_wide_as_Nat
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Array.getElem!_Nat_eq]
    simp only [← pow_mul]; agrind
  have h_L3_zero : (constants.L[3]!).val = 0 := by unfold constants.L; decide
  have h_L_expand : (↑L : ℤ) =
      ↑(constants.L[0]!).val + ↑(constants.L[1]!).val * (2 ^ 52 : ℤ) +
      ↑(constants.L[2]!).val * (2 ^ 52) ^ 2 + ↑(constants.L[4]!).val * (2 ^ 52) ^ 4 := by
    rw [show L = Scalar52_as_Nat constants.L from constants.L_spec.symm]
    unfold Scalar52_as_Nat
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Array.getElem!_Nat_eq]
    simp only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      Nat.reduceLT, getElem!_pos] at h_L3_zero
    simp only [mul_comm, zero_mul, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      Nat.ofNat_pos, getElem!_pos, one_mul, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
      h_L3_zero, add_zero, Nat.lt_add_one, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rfl
  let inter_arr := Array.make 5#usize [p2_0.2, p2_1.2, p2_2.2, p2_3.2, r4] (by simp)
  have h_inter : (↑(Scalar52_as_Nat inter_arr) : ℤ) =
      ↑p2_0.2.val + ↑p2_1.2.val * (2 ^ 52 : ℤ) + ↑p2_2.2.val * (2 ^ 52) ^ 2 +
      ↑p2_3.2.val * (2 ^ 52) ^ 3 + ↑r4.val * (2 ^ 52) ^ 4 := by
    unfold Scalar52_as_Nat inter_arr
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Array.make,
      Array.getElem!_Nat_eq, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.ofNat_pos,
      getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
    simp only [← pow_mul]; agrind
  have h_R : (↑R : ℤ) = ((2 : ℤ) ^ 52) ^ 5 := by
    simp only [R, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  let C : ℤ := ↑result0.2.val + ↑result1.2.val * (2 ^ 52 : ℤ) +
    ↑result2.2.val * (2 ^ 52) ^ 2 + ↑result3.2.val * (2 ^ 52) ^ 3 +
    ↑result4.2.val * (2 ^ 52) ^ 4
  have h_core : (↑(Scalar52_wide_as_Nat a) : ℤ) + C * ↑L =
      ↑(Scalar52_as_Nat inter_arr) * ↑R := by
    rw [h_wide, h_L_expand, h_inter, h_R]
    exact montgomery_core_eq eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  have h_C_nn : (0 : ℤ) ≤ C := by
    unfold C; grind => lia
  have h_C_lt : C < ↑R := by
    rw [h_R]; exact base_digit_bound (by positivity)
      (Nat.cast_lt.mpr h_n0_bound) (Nat.cast_lt.mpr h_n1_bound)
      (Nat.cast_lt.mpr h_n2_bound) (Nat.cast_lt.mpr h_n3_bound)
      (Nat.cast_lt.mpr h_n4_bound)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  let* ⟨ m, m_post1, m_post2, m_post3 ⟩ ← sub_spec
  · intro j hj
    interval_cases j <;> simp only [Array.make, Array.getElem!_Nat_eq,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
      getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
    <;> try assumption
  · intro j hj; interval_cases j <;> (simp only [Array.getElem!_Nat_eq, List.Vector.length_val,
      UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem!_pos]; unfold constants.L; decide)
  · rw [constants.L_spec, ← Nat.two_mul]
    exact redc_bound h_core h_canonical h_C_nn h_C_lt
  · rw [constants.L_spec]
  refine ⟨?_, m_post3, m_post2⟩
  have h_m_inter : Scalar52_as_Nat m ≡ Scalar52_as_Nat inter_arr [MOD L] := by
    have h := m_post1; rw [constants.L_spec] at h; rwa [Nat.ModEq, Nat.add_mod_right] at h
  suffices h_int : (↑(Scalar52_as_Nat m * R) : ℤ) % ↑L = (↑(Scalar52_wide_as_Nat a) : ℤ) % ↑L by
    exact_mod_cast h_int
  calc (↑(Scalar52_as_Nat m * R) : ℤ) % ↑L
      = (↑(Scalar52_as_Nat inter_arr) * ↑R) % ↑L := by exact_mod_cast h_m_inter.mul_right R
    _ = (↑(Scalar52_wide_as_Nat a) : ℤ) % ↑L := by
        conv_lhs => rw [show ↑(Scalar52_as_Nat inter_arr) * ↑R =
          ↑(Scalar52_wide_as_Nat a) + C * ↑L from by linarith [h_core]]
        exact Int.add_mul_emod_self_right _ _ _

  -- OLD PROOF (Aeneas rev: `1180be60c7a0e642cb442bfe90fe5cd8c1bb853f`)
  -- simp only [step_simps]
  -- -- ROW 0: part1(a[0])
  -- let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ result0, h_result0 ⟩ ← part1_spec
  -- obtain ⟨h_n0_val, h_carry0_val, h_carry0_bound, h_n0_bound⟩ := h_result0
  -- -- ROW 1: part1(carry0 + a[1] + n0*L[1])
  -- let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i2, i2_post ⟩ ← U128.add_spec
  -- let* ⟨ i3, i3_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i4, i4_post ⟩ ← m_spec
  -- let* ⟨ i5, i5_post ⟩ ← U128.add_spec
  -- -- ROW 1: part1
  -- let* ⟨ result1, h_result1 ⟩ ← part1_spec
  -- obtain ⟨h_n1_val, h_carry1_val, h_carry1_bound, h_n1_bound⟩ := h_result1
  -- let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i7, i7_post ⟩ ← U128.add_spec
  -- let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i9, i9_post ⟩ ← m_spec
  -- let* ⟨ i10, i10_post ⟩ ← U128.add_spec
  -- let* ⟨ i11, i11_post ⟩ ← m_spec
  -- let* ⟨ i12, i12_post ⟩ ← U128.add_spec
  -- -- ROW 2: part1
  -- let* ⟨ result2, h_result2 ⟩ ← part1_spec
  -- obtain ⟨h_n2_val, h_carry2_val, h_carry2_bound, h_n2_bound⟩ := h_result2
  -- let* ⟨ i13, i13_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i14, i14_post ⟩ ← U128.add_spec
  -- let* ⟨ i15, i15_post ⟩ ← m_spec
  -- let* ⟨ i16, i16_post ⟩ ← U128.add_spec
  -- let* ⟨ i17, i17_post ⟩ ← m_spec
  -- let* ⟨ i18, i18_post ⟩ ← U128.add_spec
  -- -- ROW 3: part1
  -- let* ⟨ result3, h_result3 ⟩ ← part1_spec
  -- obtain ⟨h_n3_val, h_carry3_val, h_carry3_bound, h_n3_bound⟩ := h_result3
  -- let* ⟨ i19, i19_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i20, i20_post ⟩ ← U128.add_spec
  -- let* ⟨ i21, i21_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i22, i22_post ⟩ ← m_spec
  -- let* ⟨ i23, i23_post ⟩ ← U128.add_spec
  -- let* ⟨ i24, i24_post ⟩ ← m_spec
  -- let* ⟨ i25, i25_post ⟩ ← U128.add_spec
  -- let* ⟨ i26, i26_post ⟩ ← m_spec
  -- let* ⟨ i27, i27_post ⟩ ← U128.add_spec
  -- -- ROW 4: part1
  -- let* ⟨ result4, h_result4 ⟩ ← part1_spec
  -- obtain ⟨h_n4_val, h_carry4_val, h_carry4_bound, h_n4_bound⟩ := h_result4
  -- let* ⟨ i28, i28_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i29, i29_post ⟩ ← U128.add_spec
  -- let* ⟨ i30, i30_post ⟩ ← m_spec
  -- let* ⟨ i31, i31_post ⟩ ← U128.add_spec
  -- let* ⟨ i32, i32_post ⟩ ← m_spec
  -- let* ⟨ i33, i33_post ⟩ ← U128.add_spec
  -- let* ⟨ i34, i34_post ⟩ ← m_spec
  -- let* ⟨ i35, i35_post ⟩ ← U128.add_spec
  -- -- ROW 5: part2 → r0
  -- let* ⟨ p2_0, h_p2_0 ⟩ ← part2_spec
  -- obtain ⟨h_r0_val, h_n5_val, h_n5_bound, h_r0_bound⟩ := h_p2_0
  -- let* ⟨ i36, i36_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i37, i37_post ⟩ ← U128.add_spec
  -- let* ⟨ i38, i38_post ⟩ ← m_spec
  -- let* ⟨ i39, i39_post ⟩ ← U128.add_spec
  -- let* ⟨ i40, i40_post ⟩ ← m_spec
  -- let* ⟨ i41, i41_post ⟩ ← U128.add_spec
  -- -- ROW 6: part2 → r1
  -- let* ⟨ p2_1, h_p2_1 ⟩ ← part2_spec
  -- obtain ⟨h_r1_val, h_n6_val, h_n6_bound, h_r1_bound⟩ := h_p2_1
  -- let* ⟨ i42, i42_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i43, i43_post ⟩ ← U128.add_spec
  -- let* ⟨ i44, i44_post ⟩ ← m_spec
  -- let* ⟨ i45, i45_post ⟩ ← U128.add_spec
  -- -- ROW 7: part2 → r2
  -- let* ⟨ p2_2, h_p2_2 ⟩ ← part2_spec
  -- obtain ⟨h_r2_val, h_n7_val, h_n7_bound, h_r2_bound⟩ := h_p2_2
  -- let* ⟨ i46, i46_post ⟩ ← Array.index_usize_spec
  -- let* ⟨ i47, i47_post ⟩ ← U128.add_spec
  -- let* ⟨ i48, i48_post ⟩ ← m_spec
  -- let* ⟨ i49, i49_post ⟩ ← U128.add_spec
  -- -- ROW 8: part2 → r3, r4_u128
  -- let* ⟨ p2_3, h_p2_3 ⟩ ← part2_spec
  -- obtain ⟨h_r3_val, h_r4u128_val, h_r4u128_bound, h_r3_bound⟩ := h_p2_3
  -- let* ⟨ r4, r4_post ⟩ ← UScalar.cast.step_spec
  -- -- Derive tight r4 bound from h_canonical
  -- have h_L4 : i21.val = 2 ^ 44 := by
  --   have := i21_post; rw [this]; unfold constants.L; decide
  -- have h_a8 : i46.val < 2 ^ 97 := by
  --   have h1 := a8_bound_of_canonical a h_canonical
  --   have h2 : i46.val = a[8]!.val := by simp only [i46_post, List.Vector.length_val,
  --     UScalar.ofNatCore_val_eq, Nat.lt_add_one, getElem!_pos, Array.getElem!_Nat_eq]
  --   agrind
  -- have h_i48 : i48.val < 2 ^ 96 := by
  --   rw [i48_post, h_L4]
  --   exact Nat.mul_lt_mul_of_pos_right h_n4_bound (by positivity)
  -- have h_i49_bound : i49.val < 2 ^ 99 := by
  --   rw [i49_post, i47_post]; linarith [h_n7_bound, h_a8, h_i48]
  -- have h_r4u128_tight : p2_3.1.val < 2 ^ 47 := by
  --   rw [h_r4u128_val, Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ 52)]
  --   calc i49.val < 2 ^ 99 := h_i49_bound
  --     _ = 2 ^ 47 * 2 ^ 52 := by rw [← pow_add]
  -- have h_r4_tight : r4.val < 2 ^ 52 := by
  --   have : r4.val ≤ p2_3.1.val := by
  --     rw [r4_post]; simp only [U128_cast_U64_val]; exact Nat.mod_le _ _
  --   linarith
  -- -- ===== MAIN EQUATION: T + C * L = inter * R (Montgomery identity) =====
  -- -- r4 cast equality (r4_u128 < 2^47 < 2^64 so cast is identity)
  -- have h_r4_eq : r4.val = p2_3.1.val := by
  --   rw [r4_post]; simp only [U128_cast_U64_val]
  --   exact Nat.mod_eq_of_lt (lt_trans h_r4u128_tight (by norm_num))
  -- -- Lift part1/part2 value equations to ℤ for mont_step / ediv+emod
  -- zify at h_n0_val h_carry0_val h_n1_val h_carry1_val h_n2_val h_carry2_val
  --        h_n3_val h_carry3_val h_n4_val h_carry4_val
  --        h_r0_val h_n5_val h_r1_val h_n6_val h_r2_val h_n7_val h_r3_val h_r4u128_val
  -- -- Part1 carry equations (rows 0–4): input_sum + n_k * L[0] = c_k * 2^52
  -- have eq0 := mont_step _ _ _ h_n0_val h_carry0_val
  -- have eq1 := mont_step _ _ _ h_n1_val h_carry1_val
  -- have eq2 := mont_step _ _ _ h_n2_val h_carry2_val
  -- have eq3 := mont_step _ _ _ h_n3_val h_carry3_val
  -- have eq4 := mont_step _ _ _ h_n4_val h_carry4_val
  -- -- Part2 split equations (rows 5–8): input_sum = carry * 2^52 + limb
  -- have eq5 : (↑i35.val : ℤ) = ↑p2_0.1.val * (2 ^ 52 : ℤ) + ↑p2_0.2.val := by
  --   rw [h_n5_val, h_r0_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  -- have eq6 : (↑i41.val : ℤ) = ↑p2_1.1.val * (2 ^ 52 : ℤ) + ↑p2_1.2.val := by
  --   rw [h_n6_val, h_r1_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  -- have eq7 : (↑i45.val : ℤ) = ↑p2_2.1.val * (2 ^ 52 : ℤ) + ↑p2_2.2.val := by
  --   rw [h_n7_val, h_r2_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  -- have eq8 : (↑i49.val : ℤ) = ↑p2_3.1.val * (2 ^ 52 : ℤ) + ↑p2_3.2.val := by
  --   rw [h_r4u128_val, h_r3_val, mul_comm]; exact (Int.mul_ediv_add_emod _ _).symm
  -- -- Replace p2_3.1 (u128 carry) with r4 (u64 cast) in eq8
  -- rw [show (↑p2_3.1.val : ℤ) = ↑r4.val from by exact_mod_cast h_r4_eq.symm] at eq8
  -- -- Substitute all intermediate computation values into the 9 equations
  -- -- After this, equations use only: a[k]!.val, result_k.{1,2}.val, p2_k.{1,2}.val, r4.val, L[k]!.val
  -- simp only [i_post, i1_post, i2_post, i3_post, i4_post, i5_post, i6_post, i7_post, i8_post,
  --   i9_post, i10_post, i11_post, i12_post, i13_post, i14_post, i15_post, i16_post,
  --   i17_post, i18_post, i19_post, i20_post, i21_post, i22_post, i23_post, i24_post,
  --   i25_post, i26_post, i27_post, i28_post, i29_post, i30_post, i31_post, i32_post,
  --   i33_post, i34_post, i35_post, i36_post, i37_post, i38_post, i39_post, i40_post,
  --   i41_post, i42_post, i43_post, i44_post, i45_post, i46_post, i47_post, i48_post, i49_post,
  --   ← Array.getElem!_Nat_eq
  -- ] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  -- -- Expand Scalar52 definitions to match montgomery_core_eq conclusion
  -- have h_wide : (↑(Scalar52_wide_as_Nat a) : ℤ) =
  --     ↑a[0]!.val + ↑a[1]!.val * (2 ^ 52 : ℤ) + ↑a[2]!.val * (2 ^ 52) ^ 2 +
  --     ↑a[3]!.val * (2 ^ 52) ^ 3 + ↑a[4]!.val * (2 ^ 52) ^ 4 +
  --     ↑a[5]!.val * (2 ^ 52) ^ 5 + ↑a[6]!.val * (2 ^ 52) ^ 6 +
  --     ↑a[7]!.val * (2 ^ 52) ^ 7 + ↑a[8]!.val * (2 ^ 52) ^ 8 := by
  --   unfold Scalar52_wide_as_Nat
  --   simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Array.getElem!_Nat_eq]
  --   simp only [← pow_mul]; agrind
  -- have h_L3_zero : (constants.L[3]!).val = 0 := by unfold constants.L; decide
  -- have h_L_expand : (↑L : ℤ) =
  --     ↑(constants.L[0]!).val + ↑(constants.L[1]!).val * (2 ^ 52 : ℤ) +
  --     ↑(constants.L[2]!).val * (2 ^ 52) ^ 2 + ↑(constants.L[4]!).val * (2 ^ 52) ^ 4 := by
  --   rw [show L = Scalar52_as_Nat constants.L from constants.L_spec.symm]
  --   unfold Scalar52_as_Nat
  --   simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
  --     Array.getElem!_Nat_eq]; agrind
  -- -- Name the intermediate result array for readability
  -- let inter_arr := Array.make 5#usize [p2_0.2, p2_1.2, p2_2.2, p2_3.2, r4] (by simp)
  -- have h_inter : (↑(Scalar52_as_Nat inter_arr) : ℤ) =
  --     ↑p2_0.2.val + ↑p2_1.2.val * (2 ^ 52 : ℤ) + ↑p2_2.2.val * (2 ^ 52) ^ 2 +
  --     ↑p2_3.2.val * (2 ^ 52) ^ 3 + ↑r4.val * (2 ^ 52) ^ 4 := by
  --   unfold Scalar52_as_Nat inter_arr
  --   simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Array.make,
  --     Array.getElem!_Nat_eq, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.ofNat_pos,
  --     getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ,
  --     Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
  --   simp only [← pow_mul]; agrind
  -- have h_R : (↑R : ℤ) = ((2 : ℤ) ^ 52) ^ 5 := by
  --   simp only [R, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  -- -- Montgomery factor C and the core identity
  -- let C : ℤ := ↑result0.2.val + ↑result1.2.val * (2 ^ 52 : ℤ) +
  --   ↑result2.2.val * (2 ^ 52) ^ 2 + ↑result3.2.val * (2 ^ 52) ^ 3 +
  --   ↑result4.2.val * (2 ^ 52) ^ 4
  -- have h_core : (↑(Scalar52_wide_as_Nat a) : ℤ) + C * ↑L =
  --     ↑(Scalar52_as_Nat inter_arr) * ↑R := by
  --   rw [h_wide, h_L_expand, h_inter, h_R]
  --   exact montgomery_core_eq eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  -- -- C bounds for redc_bound (uses base_digit_bound helper)
  -- have h_C_nn : (0 : ℤ) ≤ C := by
  --   unfold C; grind => lia
  -- have h_C_lt : C < ↑R := by
  --   rw [h_R]; exact base_digit_bound (by positivity)
  --     (Nat.cast_lt.mpr h_n0_bound) (Nat.cast_lt.mpr h_n1_bound)
  --     (Nat.cast_lt.mpr h_n2_bound) (Nat.cast_lt.mpr h_n3_bound)
  --     (Nat.cast_lt.mpr h_n4_bound)
  --     (Int.natCast_nonneg _) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  --     (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  -- let* ⟨ m, m_post1, m_post2, m_post3 ⟩ ← sub_spec
  -- · -- case ha: input limbs < 2^52
  --   intro j hj
  --   interval_cases j <;> simp only [Array.make, Array.getElem!_Nat_eq,
  --     List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
  --     getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ,
  --     Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
  --   <;> try assumption
  -- · -- case hb: L limbs < 2^52
  --   intro j hj; interval_cases j <;> (simp only [Array.getElem!_Nat_eq, List.Vector.length_val,
  --     UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem!_pos, Nat.reducePow]; unfold constants.L; decide)
  -- · -- case ha': intermediate < 2*L
  --   rw [constants.L_spec, ← Nat.two_mul]
  --   exact redc_bound h_core h_canonical h_C_nn h_C_lt
  -- · -- case hb': Scalar52_as_Nat constants.L ≤ L
  --   rw [constants.L_spec]
  -- -- Final postcondition: m*R % L = T % L ∧ limbs < 2^52 ∧ m < L
  -- refine ⟨?_, m_post3, m_post2⟩
  -- -- Step 1: m ≡ inter [MOD L] (from sub_spec: m + L ≡ inter)
  -- have h_m_inter : Scalar52_as_Nat m ≡ Scalar52_as_Nat inter_arr [MOD L] := by
  --   have h := m_post1; rw [constants.L_spec] at h; rwa [Nat.ModEq, Nat.add_mod_right] at h
  -- -- Step 2: m * R ≡ inter*R [MOD L]
  -- -- Step 3: inter * R ≡ T [MOD L] (from h_core: T + C * L = inter * R)
  -- -- Step 4: transitivity gives m * R % L = T % L
  -- suffices h_int : (↑(Scalar52_as_Nat m * R) : ℤ) % ↑L = (↑(Scalar52_wide_as_Nat a) : ℤ) % ↑L by
  --   exact_mod_cast h_int
  -- calc (↑(Scalar52_as_Nat m * R) : ℤ) % ↑L
  --     = (↑(Scalar52_as_Nat inter_arr) * ↑R) % ↑L := by exact_mod_cast h_m_inter.mul_right R
  --   _ = (↑(Scalar52_wide_as_Nat a) : ℤ) % ↑L := by
  --       conv_lhs => rw [show ↑(Scalar52_as_Nat inter_arr) * ↑R =
  --         ↑(Scalar52_wide_as_Nat a) + C * ↑L from by linarith [h_core]]
  --       exact Int.add_mul_emod_self_right _ _ _

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
