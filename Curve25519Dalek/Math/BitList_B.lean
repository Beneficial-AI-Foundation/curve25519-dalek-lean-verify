/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Math.BitList

/-! # BitList conversion lemmas (Option B)

Conversion lemmas ("bitlistify") that turn Nat-level postconditions (from standard `@[step]` specs)
into BitList-level equalities. These are used by the ToBytes_B proof.

After `step*` produces Nat-level hypotheses like `r.val = x.val / 2^k % 2^8`, we convert them to
BitList form like `ofU8 r = (ofU64 x).extract k (k+8)`.
-/

open Aeneas Aeneas.Std

namespace BitList
open List

/-! ## Simple byte: right-shift then cast to U8

For the 30 "simple" bytes, the pattern is `(limb >>> shift) as u8`, giving
`byte.val = limb.val / 2^shift % 2^8`. -/

/-- If `r.val = x.val / 2^k % 2^8`, then `ofU8 r = (ofU64 x).extract k (k+8)`. -/
theorem bitlistify_simple {r : U8} {x : U64} {k : Nat} (hk : k + 8 ≤ 64)
    (h : r.val = x.val / 2 ^ k % 2 ^ 8) :
    ofU8 r = (ofU64 x).extract k (k + 8) := by
  simp only [ofU8, ofU64, h, ofNat_mod, ofNat_extract 64 k 8 x.val (by omega)]

/-- Core simp lemma: `ofNat 8 (n / 2^k % 2^8) = (ofNat 64 n).extract k (k+8)`.
Used by `simp (discharger := omega)` to automatically convert all simple byte
postconditions to BitList extract form. -/
theorem ofNat8_div_mod_eq_extract (n k : Nat) (hk : k + 8 ≤ 64) :
    ofNat 8 (n / 2 ^ k % 2 ^ 8) = (ofNat 64 n).extract k (k + 8) := by
  rw [ofNat_mod, ofNat_extract 64 k 8 n hk]

/-! ## Shared byte: OR of upper nibble from one limb and lower nibble of the next

For the 2 "shared" bytes (s[6] and s[19]), the pattern is
`((limbA >>> 48) | (limbB <<< 4)) as u8`.

We prove this equals `extract limbA 48 52 ++ extract limbB 0 4`. -/

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

/-- Non-overlapping OR equals addition when bottom `k` bits of `a` are zero
    and `b` fits in `k` bits. -/
private theorem nat_or_eq_add (a b k : Nat) (ha : a % 2 ^ k = 0) (hb : b < 2 ^ k) :
    a ||| b = a + b := by
  have ha_low : ∀ j, j < k → a.testBit j = false := by
    intro j hj
    have h1 := Nat.testBit_mod_two_pow a k j
    rw [ha] at h1; simp_all
  have hb_high : ∀ j, j ≥ k → b.testBit j = false :=
    fun j hj => Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hj))
  have ha_eq : a = 2 ^ k * (a / 2 ^ k) := by have := Nat.div_add_mod a (2 ^ k); omega
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  by_cases hi : i < k
  · rw [ha_low i hi, Bool.false_or, ha_eq, Nat.add_comm]
    exact (testBit_add_mul_pow_low b (a / 2 ^ k) k i hb hi).symm
  · rw [hb_high i (by omega), Bool.or_false, ha_eq, Nat.add_comm]
    exact (testBit_add_mul_pow_high b (a / 2 ^ k) k i hb (by omega)).symm

/-- For the shared byte: given the Nat-level postconditions from step*, prove the BitList equality.

  `limbA` is the left limb (shifted right by 48).
  `limbB` is the right limb (shifted left by 4).
  The result byte = extract(limbA, 48, 52) ++ extract(limbB, 0, 4). -/
theorem bitlistify_shared {result : U8} {limbA limbB shr shl orv : U64}
    (hA : limbA.val < 2 ^ 52)
    (hB : limbB.val < 2 ^ 52)
    (hshr : shr.val = limbA.val / 2 ^ 48)
    (hshl : shl.val = limbB.val * 2 ^ 4 % U64.size)
    (hor_bv : orv.bv = shr.bv ||| shl.bv)
    (hcast : result = UScalar.cast .U8 orv) :
    ofU8 result = (ofU64 limbA).extract 48 52 ++ (ofU64 limbB).extract 0 4 := by
  -- Derive key bounds
  have hshr_bound : shr.val < 2 ^ 4 := by
    rw [hshr]; exact Nat.div_lt_of_lt_mul (by rwa [← Nat.pow_add])
  have hU64size : U64.size = 2 ^ 64 := by scalar_tac
  have hshl_no_overflow : limbB.val * 2 ^ 4 < 2 ^ 64 := by
    calc limbB.val * 2 ^ 4 < 2 ^ 52 * 2 ^ 4 := by omega
      _ = 2 ^ 56 := by ring
      _ ≤ 2 ^ 64 := by norm_num
  have hshl_eq : shl.val = limbB.val * 2 ^ 4 := by
    rw [hshl, hU64size, Nat.mod_eq_of_lt hshl_no_overflow]
  have hshl_mod : shl.val % 2 ^ 4 = 0 := by
    rw [hshl_eq]; rw [Nat.mul_comm]; exact Nat.mul_mod_right _ _
  -- orv.val = shl.val + shr.val (by non-overlapping OR)
  have hor_eq : orv.val = shl.val + shr.val := by
    have hbv : orv.bv = (shr ||| shl).bv := by rw [hor_bv, UScalar.bv_or]
    have := congrArg BitVec.toNat hbv
    simp only [UScalar.bv_toNat] at this
    rw [this, UScalar.val_or]
    rw [show shr.val ||| shl.val = shl.val ||| shr.val from Nat.or_comm _ _]
    exact nat_or_eq_add shl.val shr.val 4 hshl_mod hshr_bound
  -- result.val
  have hresult_val : result.val = orv.val % 2 ^ 8 := by
    rw [hcast, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq]
  -- Key computation: result.val = shr.val + limbB.val % 2^4 * 2^4
  have hmod_sum : orv.val % 2 ^ 8 = shr.val + limbB.val % 2 ^ 4 * 2 ^ 4 := by
    rw [hor_eq, hshl_eq]
    have h1 : limbB.val % 2 ^ 4 < 2 ^ 4 := Nat.mod_lt _ (by positivity)
    have h2 : shr.val + limbB.val % 2 ^ 4 * 2 ^ 4 < 2 ^ 8 := by omega
    have h3 : limbB.val * 2 ^ 4 = limbB.val % 2 ^ 4 * 2 ^ 4 +
        limbB.val / 2 ^ 4 * (2 ^ 8) := by
      have := Nat.div_add_mod limbB.val (2 ^ 4)
      nlinarith
    rw [h3, show limbB.val % 2 ^ 4 * 2 ^ 4 + limbB.val / 2 ^ 4 * 2 ^ 8 + shr.val =
        (shr.val + limbB.val % 2 ^ 4 * 2 ^ 4) + limbB.val / 2 ^ 4 * 2 ^ 8 from by ring]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  -- Combine into a direct expression for result.val
  have hresult_val2 : result.val = shr.val + limbB.val % 2 ^ 4 * 2 ^ 4 := by
    rw [hresult_val, hmod_sum]
  -- Convert to BitList
  simp only [ofU8, ofU64, hresult_val2]
  rw [show (8 : Nat) = 4 + 4 from by norm_num]
  rw [ofNat_split 4 4 (shr.val + limbB.val % 2 ^ 4 * 2 ^ 4)]
  congr 1
  · -- Bottom 4 bits = shr = limbA / 2^48
    rw [← ofNat_mod, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hshr_bound, hshr]
    exact (ofNat_extract 64 48 4 limbA.val (by omega)).symm
  · -- Top 4 bits = limbB % 2^4
    rw [show shr.val + limbB.val % 2 ^ 4 * 2 ^ 4 = shr.val + 2 ^ 4 * (limbB.val % 2 ^ 4)
        from by ring]
    rw [Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ 4),
        Nat.div_eq_of_lt hshr_bound, Nat.zero_add]
    -- Goal: ofNat 4 (limbB.val % 2^4) = (ofNat 64 limbB.val).extract 0 4
    conv_rhs => rw [ofNat_extract 64 0 4 limbB.val (by omega)]
    simp only [Nat.reducePow, pow_zero, Nat.div_one]
    exact ofNat_mod 4 limbB.val

/-! ## Auxiliary lemma for bridge: concatenating adjacent extracts -/

/-- Concatenating adjacent extracts yields the combined extract. -/
theorem List.extract_append_extract {α : Type*} (l : List α) (a b c : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) :
    l.extract a b ++ l.extract b c = l.extract a c := by
  simp only [List.extract_eq_drop_take]
  conv_rhs => rw [show c - a = (b - a) + (c - b) from by omega]
  rw [List.take_add]
  congr 1
  rw [List.drop_drop, show a + (b - a) = b from by omega]

end BitList
