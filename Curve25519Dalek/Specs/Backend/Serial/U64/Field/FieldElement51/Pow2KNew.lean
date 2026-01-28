/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

#setup_aeneas_simps

/- # Spec Theorem for `FieldElement51::pow2k`

Specification and proof for `FieldElement51::pow2k`.

This function computes the 2^k-th power of the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

-/

set_option maxHeartbeats 10000000
-- progress* and scalar_tac are heavy

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

@[progress]
theorem pow2k.m_spec (x y : U64) :
    ∃ prod : U128, pow2k.m x y = ok prod ∧
    prod.val = x.val * y.val := by
  unfold pow2k.m
  progress*
  suffices x.val * y.val < 2^64 * 2^64 by scalar_tac
  apply Nat.mul_lt_mul''
  · scalar_tac
  · scalar_tac

-- /-- Compute the 5 limbs of a² (before carry propagation) using radix-2^51 squaring.
--     Uses the identity 2^255 ≡ 19 (mod p) to reduce overflow terms. -/
-- def compute_square_limbs (a : Array U64 5#usize) : Result (U128 × U128 × U128 × U128 × U128) := do
--   let a0 := a[0]!
--   let a1 := a[1]!
--   let a2 := a[2]!
--   let a3 := a[3]!
--   let a4 := a[4]!
--   let a3_19 ← 19#u64 * a3
--   let a4_19 ← 19#u64 * a4
--   -- c0 = a0² + 2*(a1*a4_19 + a2*a3_19)
--   let t0 ← pow2k.m a0 a0
--   let t1 ← pow2k.m a1 a4_19
--   let t2 ← pow2k.m a2 a3_19
--   let t3 ← t1 + t2
--   let t4 ← 2#u128 * t3
--   let c0 ← t0 + t4
--   -- c1 = a3*a3_19 + 2*(a0*a1 + a2*a4_19)
--   let t5 ← pow2k.m a3 a3_19
--   let t6 ← pow2k.m a0 a1
--   let t7 ← pow2k.m a2 a4_19
--   let t8 ← t6 + t7
--   let t9 ← 2#u128 * t8
--   let c1 ← t5 + t9
--   -- c2 = a1² + 2*(a0*a2 + a4*a3_19)
--   let t10 ← pow2k.m a1 a1
--   let t11 ← pow2k.m a0 a2
--   let t12 ← pow2k.m a4 a3_19
--   let t13 ← t11 + t12
--   let t14 ← 2#u128 * t13
--   let c2 ← t10 + t14
--   -- c3 = a4*a4_19 + 2*(a0*a3 + a1*a2)
--   let t15 ← pow2k.m a4 a4_19
--   let t16 ← pow2k.m a0 a3
--   let t17 ← pow2k.m a1 a2
--   let t18 ← t16 + t17
--   let t19 ← 2#u128 * t18
--   let c3 ← t15 + t19
--   -- c4 = a2² + 2*(a0*a4 + a1*a3)
--   let t20 ← pow2k.m a2 a2
--   let t21 ← pow2k.m a0 a4
--   let t22 ← pow2k.m a1 a3
--   let t23 ← t21 + t22
--   let t24 ← 2#u128 * t23
--   let c4 ← t20 + t24
--   ok (c0, c1, c2, c3, c4)

/-- Bound for sum of two cross-products with 19x multipliers in squaring. -/
lemma cross_product_bound (a1 a2 a3 a4 : ℕ)
    (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a1 * (19 * a4) + a2 * (19 * a3) ≤ U128.max := by
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (38 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for 2 * (sum of two cross-products) -/
lemma two_cross_product_bound (a1 a2 a3 a4 : ℕ)
    (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    2 * (a1 * (19 * a4) + a2 * (19 * a3)) ≤ U128.max := by
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (76 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c0 = a0² + 2*(cross products) -/
lemma c0_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) ≤ U128.max := by
  have : a0 * a0 < 2 ^ 108 := by nlinarith
  have : a1 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a2 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (77 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for intermediate sum: a*b + c*(19*d) -/
lemma intermediate_sum_bound (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    a * b + c * (19 * d) ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * (19 * d) < 19 * 2 ^ 108 := by nlinarith
  have : (20 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for intermediate sum: a*b + c*d (no 19x factor) -/
lemma intermediate_sum_bound' (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    a * b + c * d ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * d < 2 ^ 108 := by nlinarith
  have : (2 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for 2 * intermediate sum: 2*(a*b + c*(19*d)) -/
lemma two_intermediate_sum_bound (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    2 * (a * b + c * (19 * d)) ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * (19 * d) < 19 * 2 ^ 108 := by nlinarith
  have : (40 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for 2 * intermediate sum: 2*(a*b + c*d) (no 19x factor) -/
lemma two_intermediate_sum_bound' (a b c d : ℕ)
    (ha : a < 2 ^ 54) (hb : b < 2 ^ 54) (hc : c < 2 ^ 54) (hd : d < 2 ^ 54) :
    2 * (a * b + c * d) ≤ U128.max := by
  have : a * b < 2 ^ 108 := by nlinarith
  have : c * d < 2 ^ 108 := by nlinarith
  have : (4 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c1 = a3*(19*a3) + 2*(a0*a1 + a2*(19*a4)) -/
lemma c1_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4)) ≤ U128.max := by
  have : a3 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a1 < 2 ^ 108 := by nlinarith
  have : a2 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : (59 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c2 = a1² + 2*(a0*a2 + a4*(19*a3)) -/
lemma c2_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3)) ≤ U128.max := by
  have : a1 * a1 < 2 ^ 108 := by nlinarith
  have : a0 * a2 < 2 ^ 108 := by nlinarith
  have : a4 * (19 * a3) < 19 * 2 ^ 108 := by nlinarith
  have : (41 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c3 = a4*(19*a4) + 2*(a0*a3 + a1*a2) -/
lemma c3_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2) ≤ U128.max := by
  have : a4 * (19 * a4) < 19 * 2 ^ 108 := by nlinarith
  have : a0 * a3 < 2 ^ 108 := by nlinarith
  have : a1 * a2 < 2 ^ 108 := by nlinarith
  have : (23 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Bound for c4 = a2² + 2*(a0*a4 + a1*a3) -/
lemma c4_bound (a0 a1 a2 a3 a4 : ℕ)
    (h0 : a0 < 2 ^ 54) (h1 : a1 < 2 ^ 54) (h2 : a2 < 2 ^ 54) (h3 : a3 < 2 ^ 54) (h4 : a4 < 2 ^ 54) :
    a2 * a2 + 2 * (a0 * a4 + a1 * a3) ≤ U128.max := by
  have : a2 * a2 < 2 ^ 108 := by nlinarith
  have : a0 * a4 < 2 ^ 108 := by nlinarith
  have : a1 * a3 < 2 ^ 108 := by nlinarith
  have : (5 : ℕ) * 2 ^ 108 ≤ U128.max + 1 := by scalar_tac
  omega

/-- Decomposition lemma: squaring in radix-2^51 representation mod p.
    This is the key algebraic identity underlying field squaring. -/
lemma decompose (a0 a1 a2 a3 a4 : ℕ) :
    (a0 + 2^51 * a1 + 2^102 * a2 + 2^153 * a3 + 2^204 * a4)^2
    ≡ a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) +
      2^51 * (a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4))) +
      2^102 * (a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3))) +
      2^153 * (a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2)) +
      2^204 * (a2 * a2 + 2 * (a0 * a4 + a1 * a3))
    [MOD p] := by
  have expand : (a0 + 2^51 * a1 + 2^102 * a2 + 2^153 * a3 + 2^204 * a4)^2 =
    a0^2 +
    2^51 * (2 * a0 * a1) +
    2^102 * (a1^2 + 2 * a0 * a2) +
    2^153 * (2 * a0 * a3 + 2 * a1 * a2) +
    2^204 * (a2^2 + 2 * a0 * a4 + 2 * a1 * a3) +
    2^255 * ((2 * a1 * a4 + 2 * a2 * a3) +
      2^51 * (a3^2 + 2 * a2 * a4) +
      2^102 * (2 * a3 * a4) +
      2^153 * a4^2) := by ring
  rw [expand]
  have key : (2 : ℕ)^255 ≡ 19 [MOD p] := by unfold p; rw [Nat.ModEq]; norm_num
  have := Nat.ModEq.mul_right ((2 * a1 * a4 + 2 * a2 * a3) +
    2^51 * (a3^2 + 2 * a2 * a4) + 2^102 * (2 * a3 * a4) + 2^153 * a4^2) key
  have := Nat.ModEq.add_left (a0^2 +
    2^51 * (2 * a0 * a1) +
    2^102 * (a1^2 + 2 * a0 * a2) +
    2^153 * (2 * a0 * a3 + 2 * a1 * a2) +
    2^204 * (a2^2 + 2 * a0 * a4 + 2 * a1 * a3)) this
  apply Nat.ModEq.trans this
  have : a0^2 + 2^51 * (2 * a0 * a1) + 2^102 * (a1^2 + 2 * a0 * a2) +
      2^153 * (2 * a0 * a3 + 2 * a1 * a2) + 2^204 * (a2^2 + 2 * a0 * a4 + 2 * a1 * a3) +
      19 * (2 * a1 * a4 + 2 * a2 * a3 + 2^51 * (a3^2 + 2 * a2 * a4) +
        2^102 * (2 * a3 * a4) + 2^153 * a4^2) =
    a0 * a0 + 2 * (a1 * (19 * a4) + a2 * (19 * a3)) +
    2^51 * (a3 * (19 * a3) + 2 * (a0 * a1 + a2 * (19 * a4))) +
    2^102 * (a1 * a1 + 2 * (a0 * a2 + a4 * (19 * a3))) +
    2^153 * (a4 * (19 * a4) + 2 * (a0 * a3 + a1 * a2)) +
    2^204 * (a2 * a2 + 2 * (a0 * a4 + a1 * a3)) := by ring
  rw [this]

@[local simp]
theorem shiftLeft_54 : 1 <<< 54 % U64.size = 2^54 := by scalar_tac

/-- The final carry bound: if carry ≤ (2^64 - 2^51)/19 then 2^51 + 19*carry < 2^64. -/
lemma carry_mul_bound (carry_val : ℕ) (h : carry_val ≤ (2 ^ 64 - 2 ^ 51) / 19) :
    2 ^ 51 + 19 * carry_val < 2 ^ 64 := by
  have hle := Nat.mul_le_mul_right 19 h
  have hdiv : 19 * ((2 ^ 64 - 2 ^ 51) / 19) ≤ 2 ^ 64 - 2 ^ 51 := Nat.mul_div_le _ _
  omega


-- /-- The square limbs represent a² in radix-2^51 form modulo p.
--     c0 + 2^51*c1 + 2^102*c2 + 2^153*c3 + 2^204*c4 ≡ (Field51_as_Nat a)² [MOD p] -/
-- @[progress]
-- theorem compute_square_limbs_spec (a : Array U64 5#usize)
--     (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
--     ∃ c0 c1 c2 c3 c4 : U128, compute_square_limbs a = ok (c0, c1, c2, c3, c4) ∧
--     (c0.val + 2^51 * c1.val + 2^102 * c2.val + 2^153 * c3.val + 2^204 * c4.val)
--       ≡ (Field51_as_Nat a)^2 [MOD p] := by
--   unfold compute_square_limbs
--   have := ha 0 (by simp)
--   have := ha 1 (by simp)
--   have := ha 2 (by simp)
--   have := ha 3 (by simp)
--   have := ha 4 (by simp)
--   progress*
--   have := decompose a[0]!.val a[1]!.val a[2]!.val a[3]!.val a[4]!.val
--   use c0; use c1; use c2; use c3; use c4
--   refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
--   simp_all [-Nat.reducePow, Field51_as_Nat, Finset.sum_range_succ, Nat.ModEq]

@[progress]
theorem pow2k_loop_spec (k : ℕ) (k' : U32) (a : Array U64 5#usize)
    (hk : 0 < k) (eqk : k'.val = k)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k_loop k' a = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  unfold pow2k_loop
  have := ha 0 (by simp)
  have := ha 1 (by simp)
  have := ha 2 (by simp)
  have := ha 3 (by simp)
  have := ha 4 (by simp)
  -- Using `progress*?` in order to run progress until a certain point in the implementation
  simp only [progress_simps]
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
  let* ⟨ a3_19, a3_19_post ⟩ ← U64.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec
  let* ⟨ a4_19, a4_19_post ⟩ ← U64.mul_spec
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
  let* ⟨ i3, i3_post ⟩ ← pow2k.m_spec
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
  let* ⟨ i5, i5_post ⟩ ← pow2k.m_spec
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
  let* ⟨ i7, i7_post ⟩ ← pow2k.m_spec
  let* ⟨ i8, i8_post ⟩ ← U128.add_spec
  · simp_all only
    apply cross_product_bound <;> simp_all
  let* ⟨ i9, i9_post ⟩ ← U128.mul_spec
  · simp_all only
    apply two_cross_product_bound <;> simp_all
  let* ⟨ c0, c0_post ⟩ ← U128.add_spec
  · simp_all only
    apply c0_bound <;> simp_all
  let* ⟨ i10, i10_post ⟩ ← pow2k.m_spec
  let* ⟨ i11, i11_post ⟩ ← pow2k.m_spec
  let* ⟨ i12, i12_post ⟩ ← pow2k.m_spec
  let* ⟨ i13, i13_post ⟩ ← U128.add_spec
  · simp_all only; apply intermediate_sum_bound <;> simp_all
  let* ⟨ i14, i14_post ⟩ ← U128.mul_spec
  · simp_all only; apply two_intermediate_sum_bound <;> simp_all
  let* ⟨ c1, c1_post ⟩ ← U128.add_spec
  · simp_all only; apply c1_bound <;> simp_all
  let* ⟨ i15, i15_post ⟩ ← pow2k.m_spec
  let* ⟨ i16, i16_post ⟩ ← pow2k.m_spec
  let* ⟨ i17, i17_post ⟩ ← pow2k.m_spec
  let* ⟨ i18, i18_post ⟩ ← U128.add_spec
  · simp_all only; apply intermediate_sum_bound <;> simp_all
  let* ⟨ i19, i19_post ⟩ ← U128.mul_spec
  · simp_all only; apply two_intermediate_sum_bound <;> simp_all
  let* ⟨ c2, c2_post ⟩ ← U128.add_spec
  · simp_all only; apply c2_bound <;> simp_all
  let* ⟨ i20, i20_post ⟩ ← pow2k.m_spec
  let* ⟨ i21, i21_post ⟩ ← pow2k.m_spec
  let* ⟨ i22, i22_post ⟩ ← pow2k.m_spec
  let* ⟨ i23, i23_post ⟩ ← U128.add_spec
  · simp_all only; apply intermediate_sum_bound' <;> simp_all
  let* ⟨ i24, i24_post ⟩ ← U128.mul_spec
  · simp_all only; apply two_intermediate_sum_bound' <;> simp_all
  let* ⟨ c3, c3_post ⟩ ← U128.add_spec
  · simp_all only; apply c3_bound <;> simp_all
  let* ⟨ i25, i25_post ⟩ ← pow2k.m_spec
  let* ⟨ i26, i26_post ⟩ ← pow2k.m_spec
  let* ⟨ i27, i27_post ⟩ ← pow2k.m_spec
  let* ⟨ i28, i28_post ⟩ ← U128.add_spec
  · simp_all only; apply intermediate_sum_bound' <;> simp_all
  let* ⟨ i29, i29_post ⟩ ← U128.mul_spec
  · simp_all only; apply two_intermediate_sum_bound' <;> simp_all
  let* ⟨ c4, c4_post ⟩ ← U128.add_spec
  · simp_all only; apply c4_bound <;> simp_all
  -- The 5 intermediate products (c0-c4) have been computed
  have a_pow_two : (c0.val + 2^51 * c1.val + 2^102 * c2.val + 2^153 * c3.val + 2^204 * c4.val)
      ≡ (Field51_as_Nat a)^2 [MOD p] := by
    have := decompose a[0]!.val a[1]!.val a[2]!.val a[3]!.val a[4]!.val
    simp_all [-Nat.reducePow, Field51_as_Nat, Finset.sum_range_succ, Nat.ModEq]
  -- The splits are due to 5 `debug_assert!(a[i] < (1 << 54))`
  let* ⟨ i30, i30_post_1, i30_post_2 ⟩ ← U64.ShiftLeft_IScalar_spec
  split
  . split
    . split
      . split
        . split
          . let* ⟨ i31, i31_post_1, i31_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
            let* ⟨ i32, i32_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i33, i33_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ c11, c11_post ⟩ ← U128.add_spec
            let* ⟨ i34, i34_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i35, i35_post_1, i35_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ a1, a1_post ⟩ ← Array.update_spec
            let* ⟨ i36, i36_post_1, i36_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
            let* ⟨ i37, i37_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i38, i38_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ c21, c21_post ⟩ ← U128.add_spec
            let* ⟨ i39, i39_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i40, i40_post_1, i40_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ a2, a2_post ⟩ ← Array.update_spec
            let* ⟨ i41, i41_post_1, i41_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
            let* ⟨ i42, i42_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i43, i43_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ c31, c31_post ⟩ ← U128.add_spec
            let* ⟨ i44, i44_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i45, i45_post_1, i45_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ a3, a3_post ⟩ ← Array.update_spec
            let* ⟨ i46, i46_post_1, i46_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
            let* ⟨ i47, i47_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i48, i48_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ c41, c41_post ⟩ ← U128.add_spec
            let* ⟨ i49, i49_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i50, i50_post_1, i50_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ a4, a4_post ⟩ ← Array.update_spec
            let* ⟨ i51, i51_post_1, i51_post_2 ⟩ ← U128.ShiftRight_IScalar_spec
            let* ⟨ carry, carry_post ⟩ ← UScalar.cast.progress_spec
            have hcarry : 2^51 + 19 * carry.val < 2^64 := by
              -- carry = (c41 >> 51) % 2^64. With limbs < 2^54:
              -- c4 < 5*2^108, i48 < 2^64, so c41 < 5*2^108 + 2^64 < 2^111
              -- Thus carry = c41/2^51 < 2^60 < (2^64 - 2^51)/19
              -- Full proof tracks bounds through carry chain (see Pow2K.lean)
              apply carry_mul_bound
              simp only [carry_post, UScalar.cast_val_eq, UScalarTy.numBits,
                  i51_post_1, Nat.shiftRight_eq_div_pow]
              sorry -- Requires detailed carry chain bound tracking
            let* ⟨ i52, i52_post ⟩ ← UScalar.cast.progress_spec
            let* ⟨ i53, i53_post_1, i53_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ a5, a5_post ⟩ ← Array.update_spec
            let* ⟨ i54, i54_post ⟩ ← U64.mul_spec
            let* ⟨ i55, i55_post ⟩ ← Array.index_usize_spec
            let* ⟨ i56, i56_post ⟩ ← U64.add_spec
            · -- i55 < 2^51 (masked), i54 = 19*carry. By hcarry: sum < 2^64
              sorry
            let* ⟨ a6, a6_post ⟩ ← Array.update_spec
            let* ⟨ i57, i57_post ⟩ ← Array.index_usize_spec
            let* ⟨ i58, i58_post_1, i58_post_2 ⟩ ← U64.ShiftRight_IScalar_spec
            let* ⟨ i59, i59_post ⟩ ← Array.index_usize_spec
            let* ⟨ i60, i60_post ⟩ ← U64.add_spec
            · -- i59 < 2^51 (masked), i58 = i56 >> 51 < 2^13 (since i56 < 2^64)
              sorry
            let* ⟨ a7, a7_post ⟩ ← Array.update_spec
            let* ⟨ i61, i61_post ⟩ ← Array.index_usize_spec
            let* ⟨ i62, i62_post_1, i62_post_2 ⟩ ← UScalar.and_spec
            let* ⟨ __discr, __discr_post ⟩ ← Array.index_mut_usize_spec
            let* ⟨ k1, k1_post_1, k1_post_2 ⟩ ← U32.sub_spec
            split
            . -- Base case: k1 = 0 means k = 1, single squaring
              simp only [progress_simps]
              -- The result is a7.set 0 i62, representing a^2 mod p
              -- Need: Field51_as_Nat result ≡ (Field51_as_Nat a)^(2^1) [MOD p]
              -- and bounds on result limbs
              constructor
              · -- Main equality for k=1: a^(2^1) = a^2
                sorry
              · -- Bounds: each limb < 2^52
                sorry
            . let* ⟨ res, res_post_1, res_post_2 ⟩ ← pow2k_loop_spec
              · -- Recursive call precondition: k-1 > 0
                -- We're in the branch where k1 ≠ 0, i.e., k' - 1 ≠ 0
                sorry
              · constructor
                · -- Main equality: Field51_as_Nat res ≡ (Field51_as_Nat a)^(2^k) [MOD p]
                  -- res satisfies: Field51_as_Nat res ≡ (Field51_as_Nat a7')^(2^(k-1)) [MOD p]
                  -- where a7' = a7.set 0 i62 is one squaring of a
                  -- Need: (a^2)^(2^(k-1)) = a^(2^k)
                  rw [eqk] at res_post_1
                  -- First show: a7.set 0 i62 ≡ a^2 [MOD p]
                  have hsq : Field51_as_Nat (a7.set 0#usize i62) ≡ (Field51_as_Nat a)^2 [MOD p] := by
                    sorry
                  have hpow := Nat.ModEq.pow (2^(k-1)) hsq
                  apply Nat.ModEq.trans res_post_1 hpow |>.trans
                  rw [← pow_mul]
                  congr 1
                  have : 2 * 2^(k-1) = 2^k := by
                    have : k ≠ 0 := by sorry
                    sorry
                  grind
                · assumption
          . have : 2^54 < a[4]!.val := by scalar_tac
            grind
        . have : 2^54 < a[3]!.val := by scalar_tac
          grind
      . have : 2^54 < a[2]!.val := by scalar_tac
        grind
    . have : 2^54 < a[1]!.val := by scalar_tac
      grind
  . have : 2^54 < a[0]!.val := by scalar_tac
    grind

-- @[progress]
-- theorem pow2k_loop_spec' (k : ℕ) (k' : U32) (a : Array U64 5#usize)
--     (hk : 0 < k) (eqk : k'.val = k)
--     (h_bounds : ∀ i < 5, a[i]!.val < 2 ^ 54) :
--     ∃ r, pow2k_loop k' a = ok r ∧
--     Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k) [MOD p] ∧
--     (∀ i < 5, r[i]!.val < 2 ^ 52) := by
--   unfold pow2k_loop
--   progress*
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry

@[progress]
theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (hk : 0 < k.val)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    ∃ result : FieldElement51, pow2k self k = ok result ∧
    Field51_as_Nat result ≡ (Field51_as_Nat self)^(2^k.val) [MOD p] ∧
    (∀ i < 5, result[i]!.val < 2 ^ 52) := by
  unfold pow2k
  progress*
  grind

end curve25519_dalek.backend.serial.u64.field.FieldElement51
