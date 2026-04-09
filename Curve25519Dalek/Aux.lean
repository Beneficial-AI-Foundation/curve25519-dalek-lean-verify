/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Zhang-Liao, Markus Ferdinand Dablander, Hoang Le Truong,
  Alessandro D'Angelo
-/
import Aeneas
import Curve25519Dalek.Math.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Auxiliary theorems

Theorems which are useful for proving spec theorems in this project
but aren't available upstream.
This file is for theorems which depend only on Defs.lean,
not on Funs.lean or Types.lean. -/

-- Linter doesn't recognize this Aeneas macro
set_option linter.hashCommand false
#setup_aeneas_simps

open Aeneas.Std Result

attribute [-simp] Int.reducePow Nat.reducePow

/-- Right-shifting a 64-bit value by 51 bits leaves at most 13 bits so bounded by 2^13 - 1. -/
theorem U64_shiftRight_le (a : U64) : a.val >>> 51 ≤ 2 ^ 13 - 1 := by
  bvify 64 at *; bv_decide

-- /-- Bitwise AND with 2^51 - 1 (which is a mask with all 1s in the lower 51 bits) extracts
-- the lower 51 bits of the number, which is equivalent to taking the value modulo 2^51. -/
-- theorem Aeneas.Std.U64.and_LOW_51_BIT_MASK (x : U64) :
--     (x &&& LOW_51_BIT_MASK).val = x.val % 2^51 := by
--   simp [LOW_51_BIT_MASK_val_eq]

/-- Right shift by 51 is equivalent to division by 2^51 -/
theorem Aeneas.Std.U64.shiftRight_51 (x : U64) : x.val >>> 51 = x.val / 2^51 := by
  simp only [Nat.shiftRight_eq_div_pow]

-- /-- Fundamental property of bit operations: a number can be split into lower and upper bits -/
-- theorem Aeneas.Std.U64.split_51 (x : U64) :
--     x.val = (x &&& LOW_51_BIT_MASK).val + (x.val >>> 51) * 2^51 := by
--   rw [x.and_LOW_51_BIT_MASK, x.shiftRight_51]
--   omega

theorem Array.val_getElem!_eq' (bs : Array U64 5#usize) (i : Nat) (h : i < bs.length) :
    (bs.val)[i]! = bs[i] := by
  simpa [Subtype.val] using getElem!_pos bs.val i _

/-- Setting the j part of an array doesn't change the i part if i ≠ j -/
@[simp]
theorem Array.set_of_ne (bs : Array U64 5#usize) (a : U64) (i j : Nat) (hi : i < bs.length)
    (hj : j < bs.length) (h : i ≠ j) :
    (bs.set j#usize a)[i]! = bs[i] := by
  rw [Array.getElem!_Nat_eq, Array.set_val_eq, ← Array.val_getElem!_eq' bs i hi]
  exact List.getElem!_set_ne bs j i a (by omega)

/-- Setting the j part of an array doesn't change the i part if i ≠ j -/
theorem Array.set_of_ne' (bs : Array U64 5#usize) (a : U64)
    (i : Nat) (j : Usize) (hi : i < bs.length) (h : i ≠ j) :
    (bs.set j a)[i]! = bs[i] := by
  rw [Array.getElem!_Nat_eq, Array.set_val_eq, ← Array.val_getElem!_eq' bs i hi]
  exact List.getElem!_set_ne bs j i a (by omega)

/-- Convert GetElem (Nat index) to getElem! for Aeneas Array -/
theorem Array.getElem_eq_getElem! (bs : Array U64 5#usize) (i : Nat) (hi : i < bs.length) :
    (bs[i] : U64) = bs[i]! := by
  rw [Array.getElem!_Nat_eq, ← Array.val_getElem!_eq' bs i hi]

/-- Convert GetElem (Usize index) to getElem! for Aeneas Array -/
theorem Array.getElem_usize_eq_getElem! (bs : Array U64 5#usize) (i : Usize)
    (hi : i.val < bs.length) :
    (bs[i] : U64) = bs[i.val]! := by
  simp only [Array.getElem!_Nat_eq]
  change bs.val[i.val] = bs.val[i.val]!
  exact List.Inhabited_getElem_eq_getElem! bs.val i.val hi

/-- Like set_of_ne but returns getElem! on both sides -/
theorem Array.set_of_ne_getElem! (bs : Array U64 5#usize)
    (a : U64) (i j : Nat) (hi : i < bs.length)
    (hj : j < bs.length) (h : i ≠ j) :
    (bs.set j#usize a)[i]! = bs[i]! := by
  rw [Array.set_of_ne bs a i j hi hj h, Array.getElem_eq_getElem! bs i hi]

/-- Setting the j part of an array gives exactly the i part if i = j -/
theorem Array.set_of_eq (bs : Array U64 5#usize) (a : U64) (i : Nat) (hi : i < bs.length) :
    (bs.set i#usize a)[i]! = a := by
  grind only [usr Subtype.property, = getElem?_pos,
    = Array.set_val_eq, = UScalar.ofNatCore_val_eq,
    = List.getElem_set]

/-- If a 32-byte array represents a value less than `2 ^ 252`, then the high bit (bit 7) of byte 31
must be 0. -/
theorem high_bit_zero_of_lt_255 (bytes : Array U8 32#usize) (h : U8x32_as_Nat bytes < 2 ^ 255) :
    bytes.val[31]!.val >>> 7 = 0 := by
  by_contra!
  have : 2 ^ 7 ≤ bytes.val[31]!.val := by omega
  have : 2 ^ 255 ≤ U8x32_as_Nat bytes := by
    unfold U8x32_as_Nat
    have : ∑ i ∈ Finset.range 32,
        2 ^ (8 * i) * bytes.val[i]!.val =
        ∑ i ∈ Finset.range 31,
        2 ^ (8 * i) * bytes.val[i]!.val +
        2 ^ (8 * 31) * bytes.val[31]!.val := by
      rw [Finset.sum_range_succ]
    simp_all only [ne_eq, Nat.reduceMul,
      Array.getElem!_Nat_eq, ge_iff_le]; omega
  omega

/-- If a 32-byte array represents a value less than `L`, then the high bit (bit 7) of byte 31
must be 0. -/
theorem high_bit_zero_of_lt_L (bytes : Array U8 32#usize) (h : U8x32_as_Nat bytes < L) :
    bytes.val[31]!.val >>> 7 = 0 := by
  refine high_bit_zero_of_lt_255 bytes ?_
  have : L ≤ 2 ^ 255 := by decide
  omega

/-- If `Scalar52_as_Nat a < 2^259`, then the top limb `a[4]` is bounded by `2^51`.
This follows because `2^208 * a[4] ≤ Scalar52_as_Nat a < 2^259` implies `a[4] < 2^51`. -/
theorem Scalar52_top_limb_lt_of_as_Nat_lt (a : Array U64 5#usize)
    (h : Scalar52_as_Nat a < 2 ^ 259) : a[4]!.val < 2 ^ 51 := by
  unfold Scalar52_as_Nat at h
  have h4 : 2 ^ 208 * a[4]!.val ≤ ∑ j ∈ Finset.range 5, 2 ^ (52 * j) * a[j]!.val := by
    have hmem : 4 ∈ Finset.range 5 := by decide
    have := Finset.single_le_sum (f := fun j => 2 ^ (52 * j) * a[j]!.val)
      (fun j _ => Nat.zero_le _) hmem
    convert this using 2
  omega

/-- The function U8x32_as_Nat can be represented via Nat.ofDigits applied to an appropriate
list representation of the input array -/
lemma U8x32_as_Nat_is_NatofDigits
    (a : Aeneas.Std.Array U8 32#usize) :
    U8x32_as_Nat a =
    Nat.ofDigits (2 ^ 8)
      (List.ofFn fun i : Fin 32 => a[i]!.val) := by
  unfold U8x32_as_Nat
  rw [Nat.ofDigits_eq_sum_mapIdx (2 ^ 8)
    (List.ofFn fun i : Fin 32 => a[i]!.val),
    Finset.sum_range]
  simp only [pow_mul]
  change (List.ofFn fun i : Fin 32 =>
    (2 ^ 8) ^ (i : ℕ) * a[i]!.val).sum = _
  simp only [Fin.getElem!_fin, Array.getElem!_Nat_eq,
    List.ofFn_succ, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, pow_zero, one_mul, Fin.val_succ,
    zero_add, pow_one, Nat.reduceAdd, Fin.val_eq_zero,
    List.ofFn_zero, List.sum_cons, List.sum_nil, add_zero,
    List.mapIdx_cons, mul_one, Nat.mul_comm,
    List.mapIdx_nil]

/-! ## Bridge between U8x32_as_Nat and U8x32_as_Field

`U8x32_as_Nat` (Finset.sum in ℕ) and `U8x32_as_Field` (Horner foldr in ZMod p) compute the same
little-endian byte interpretation but in different types. The bridge goes through `Nat.ofDigits`:

  U8x32_as_Nat ──(is_NatofDigits)──▶ Nat.ofDigits 256 [b₀.val, ..., b₃₁.val]
                                        │
                                   (ofDigits = foldr)
                                        │
                                        ▼
  U8x32_as_Field ◀──(Nat.cast)──── List.foldr Horner₂₅₆ 0 bytes.val
-/

/-- `Nat.ofDigits b l` equals Horner evaluation via `foldr`. -/
private lemma ofDigits_eq_foldr (b : ℕ) (l : List ℕ) :
    Nat.ofDigits b l = l.foldr (fun d acc => d + b * acc) 0 := by
  induction l with
  | nil => simp only [Nat.ofDigits, List.foldr_nil]
  | cons h t ih =>
    simp only [Nat.ofDigits, Nat.cast_id, ih,
      List.foldr_cons]

/-- `Nat.cast` commutes with Horner evaluation on a byte list. -/
lemma horner_natCast (l : List U8) :
    ((l.foldr (fun (b : U8) (acc : ℕ) => b.val + 256 * acc) 0 : ℕ) : ZMod p) =
    l.foldr (fun (b : U8) (acc : ZMod p) => (b.val : ZMod p) + 256 * acc) 0 := by
  induction l with
  | nil => simp only [List.foldr_nil, Nat.cast_zero]
  | cons h t ih =>
    simp only [List.foldr_cons]
    push_cast [ih]
    ring

/-- The byte-value list produced by `List.ofFn` on Array indices equals `List.map` on the
    underlying list. Bridges the `Fin`-indexed view from `Nat.ofDigits` to the raw list view. -/
private lemma ofFn_val_eq_map_val (a : Aeneas.Std.Array U8 32#usize) :
    (List.ofFn fun i : Fin 32 => (a[i]! : U8).val) = a.val.map (fun b => b.val) := by
  simp only [Fin.getElem!_fin, Array.getElem!_Nat_eq]
  apply List.ext_getElem
  · simp only [List.ofFn_succ, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.val_succ,
      zero_add, Nat.reduceAdd, Fin.val_eq_zero,
      List.ofFn_zero, List.length_cons, List.length_nil,
      List.length_map, a.property,
      UScalar.ofNatCore_val_eq]
  · intro i hi1 hi2
    simp only [List.getElem_ofFn, List.getElem_map]
    congr 1
    rw [getElem!_pos (h := by rw [List.length_map] at hi2; omega)]

/-- `U8x32_as_Nat` equals Horner evaluation at base 256 on the underlying byte list. -/
lemma U8x32_as_Nat_eq_foldr (a : Aeneas.Std.Array U8 32#usize) :
    U8x32_as_Nat a = a.val.foldr (fun b (acc : ℕ) => b.val + 256 * acc) 0 := by
  rw [U8x32_as_Nat_is_NatofDigits, ofDigits_eq_foldr]
  have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [h256]
  -- Rewrite the List.ofFn to List.map, then use List.foldr_map
  have h_list := ofFn_val_eq_map_val a
  rw [h_list, List.foldr_map]

/-- **Bridge lemma**: `U8x32_as_Field` and `U8x32_as_Nat` compute the same value,
    just in different types (ZMod p vs ℕ). -/
lemma U8x32_as_Field_eq_cast (a : Aeneas.Std.Array U8 32#usize) :
    U8x32_as_Field a = ((U8x32_as_Nat a : ℕ) : ZMod p) := by
  unfold U8x32_as_Field
  rw [U8x32_as_Nat_eq_foldr, horner_natCast]
  rfl

/-- The function `U8x32_as_Nat` is injective: if two 32-byte arrays produce the same natural
number representation, then the input arrays must be equal. -/
lemma U8x32_as_Nat_injective : Function.Injective U8x32_as_Nat := by
  intro a a' h_funs_eq
  rw [U8x32_as_Nat_is_NatofDigits a, U8x32_as_Nat_is_NatofDigits a'] at h_funs_eq
  let L := (List.ofFn fun i : Fin 32 => a[i]!.val)
  let L' := (List.ofFn fun i : Fin 32 => a'[i]!.val)
  have h_inj := Nat.ofDigits_inj_of_len_eq
    (b := 2 ^ 8)
    (by omega : 1 < 2 ^ 8)
    (L1 := L)
    (L2 := L')
    (by rw [List.length_ofFn, List.length_ofFn])
    (by intro l hl; rw [List.mem_ofFn] at hl
        obtain ⟨i, rfl⟩ := hl; exact Aeneas.Std.UScalar.hBounds (a[i]!))
    (by intro l hl; rw [List.mem_ofFn] at hl
        obtain ⟨i, rfl⟩ := hl; exact Aeneas.Std.UScalar.hBounds (a'[i]!))
    (h_funs_eq)
  simp only [L, L', List.ofFn_inj] at h_inj
  apply Subtype.ext
  apply List.ext_get
  · simp only [List.Vector.length_val,
      UScalar.ofNatCore_val_eq]
  · intro n h_a h_a'
    have h_len : n < 32 := by
      rw [List.Vector.length_val] at h_a; exact h_a
    have h_congr := congr_fun h_inj ⟨n, h_len⟩
    simp_all only [Fin.getElem!_fin, Array.getElem!_Nat_eq, getElem!_pos, List.get_eq_getElem]
    exact UScalar.eq_of_val_eq h_congr

lemma land_pow_two_sub_one_eq_mod (a n : Nat) :
    a &&& (2^n - 1) = a % 2^n := by
  induction n generalizing a
  · simp only [pow_zero, tsub_self, Nat.and_zero,
      Aeneas.ReduceNat.reduceNatEq]; omega
  · simp only [Nat.and_two_pow_sub_one_eq_mod]

/-! ## UScalar cast lemmas for carry propagation

These lemmas capture the Nat interpretation of casting patterns used in
field element carry propagation:
- `((x >> 51) as u64) as u128` extracts carry: `(x / 2^51) % 2^64`
- `(x as u64) & MASK` extracts remainder: `x % 2^51`
-/

/-- Casting U128 to U64 truncates to lower 64 bits -/
@[simp]
theorem U128_cast_U64_val (x : U128) : (UScalar.cast .U64 x).val = x.val % 2^64 := by
  simp only [UScalar.cast_val_eq, UScalarTy.numBits]

/-- Casting U64 to U128 preserves value (widening) -/
@[simp]
theorem U64_cast_U128_val (x : U64) : (UScalar.cast .U128 x).val = x.val := by
  simp only [UScalar.cast_val_eq, UScalarTy.numBits]
  have hx : x.val < 2^64 := x.hBounds
  have h64_lt_128 : (64 : ℕ) ≤ 128 := by omega
  have : 2^64 ≤ 2^128 := Nat.pow_le_pow_right (by omega) h64_lt_128
  omega

/-- The double-cast pattern `((x : U128).cast U64).cast U128` gives `x % 2^64` -/
@[simp]
theorem U128_cast_U64_cast_U128_val (x : U128) :
    (UScalar.cast .U128 (UScalar.cast .U64 x)).val = x.val % 2^64 := by
  simp only [U64_cast_U128_val, U128_cast_U64_val]

/-- When `x < 2^115`, the carry `x / 2^51` fits in U64 without truncation -/
theorem carry_fits_U64 (x : ℕ) (hx : x < 2 ^ 115) : x / 2 ^ 51 < 2 ^ 64 := by
  have h1 : (2 : ℕ) ^ 115 / 2 ^ 51 = 2 ^ 64 := by decide
  calc x / 2 ^ 51 ≤ (2 ^ 115 - 1) / 2 ^ 51 := Nat.div_le_div_right (by omega)
    _ < 2 ^ 64 := by decide

/-- When the shift result fits in U64, the double-cast preserves it exactly -/
theorem double_cast_of_lt (x : ℕ) (hx : x < 2 ^ 64) :
    x % 2 ^ 64 % 2 ^ 128 = x := by
  have h1 : x % 2 ^ 64 = x := Nat.mod_eq_of_lt hx
  have h2 : x < 2 ^ 128 := by omega
  simp only [h1, Nat.mod_eq_of_lt h2]

/-- Key lemma: when `c < 2^115`, the carry extraction `(c / 2^51) % 2^64` equals `c / 2^51` -/
theorem carry_mod_eq (c : ℕ) (hc : c < 2 ^ 115) : (c / 2 ^ 51) % 2 ^ 64 = c / 2 ^ 51 := by
  exact Nat.mod_eq_of_lt (carry_fits_U64 c hc)

/-! ## Bitwise OR equals addition for disjoint ranges -/

/-- Nat.bit decomposition: every natural number is `bit (testBit 0) (n / 2)`. -/
private lemma bit_decomp (a : Nat) : a = Nat.bit (a.testBit 0) (a / 2) := by
  rw [Nat.testBit_zero]
  unfold Nat.bit
  have := Nat.div_add_mod a 2
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · simp only [h, zero_ne_one, decide_false, cond_false]; omega
  · simp only [h, decide_true, cond_true]; omega

/-- OR of a value below `2^k` with a multiple of `2^k` equals their sum,
    because the bit ranges are disjoint. -/
lemma or_mul_pow_two_eq_add (a b k : Nat) (ha : a < 2 ^ k) :
    a ||| (b * 2 ^ k) = a + b * 2 ^ k := by
  induction k generalizing a b with
  | zero =>
    simp_all only [pow_zero, Nat.lt_one_iff, mul_one,
      Nat.zero_or, zero_add]
  | succ k ih =>
    have ha_div : a / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      linarith [show 2 ^ (k + 1) = 2 ^ k * 2 from by ring]
    conv_lhs =>
      rw [bit_decomp a,
        show b * 2 ^ (k + 1) = Nat.bit false (b * 2 ^ k) from by
          unfold Nat.bit; simp only [cond_false]; ring]
    rw [Nat.lor_bit, Bool.or_false, ih (a / 2) b ha_div]
    unfold Nat.bit
    have h2 : b * 2 ^ (k + 1) = 2 * (b * 2 ^ k) := by ring
    have hmod := Nat.div_add_mod a 2
    rw [h2]
    rcases Nat.mod_two_eq_zero_or_one a with h | h
    · rw [Nat.testBit_zero]
      simp only [h, zero_ne_one, decide_false, cond_false]
      omega
    · rw [Nat.testBit_zero]
      simp only [h, decide_true, cond_true]
      omega

/-! ## Byte-packing helpers for load8 / from_bytes

These lemmas handle the pattern of ORing 8 shifted bytes into a U64 word.
Used by both `FieldElement51::from_bytes` and `Scalar52::from_bytes`. -/

lemma u8_mul_pow_lt_u64_size (x : U8) (k : Nat) (hk : k ≤ 56) :
    x.val * 2 ^ k < U64.size := calc
  _ ≤ 255 * 2 ^ 56 := Nat.mul_le_mul (Nat.lt_succ_iff.mp x.hmax)
        (Nat.pow_le_pow_right (by omega) hk)
  _ < U64.size := by scalar_tac

lemma u8_val_mod_u64_numBits (x : U8) :
    x.val % 2 ^ UScalarTy.U64.numBits = x.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.hmax (by norm_num))

lemma u8_mul_pow_mod_u64 (x : U8) (k : Nat) (hk : k ≤ 56) :
    x.val * 2 ^ k % U64.size = x.val * 2 ^ k :=
  Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size x k hk)

/-- Left-associated OR of 8 byte values shifted by multiples of 8 equals their sum. -/
lemma or_bytes_eq_sum (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (_ : b0 < 256) (_ : b1 < 256)
    (_ : b2 < 256) (_ : b3 < 256) (_ : b4 < 256) (_ : b5 < 256) (_ : b6 < 256) (_ : b7 < 256) :
    ((((((b0 ||| b1 * 2^8) ||| b2 * 2^16) ||| b3 * 2^24) |||
      b4 * 2^32) ||| b5 * 2^40) ||| b6 * 2^48) ||| b7 * 2^56 =
      b0 + b1 * 2^8 + b2 * 2^16 + b3 * 2^24 + b4 * 2^32 + b5 * 2^40 + b6 * 2^48 + b7 * 2^56 := by
  rw [or_mul_pow_two_eq_add _ _ 8 (by omega), or_mul_pow_two_eq_add _ _ 16 (by grind),
    or_mul_pow_two_eq_add _ _ 24 (by grind), or_mul_pow_two_eq_add _ _ 32 (by grind),
    or_mul_pow_two_eq_add _ _ 40 (by grind), or_mul_pow_two_eq_add _ _ 48 (by grind),
    or_mul_pow_two_eq_add _ _ 56 (by grind)]

/-- If `x + n * m = y` then `x ≡ y [MOD m]`. -/
lemma modeq_of_add_mul_eq (x y n m : ℕ) (h : x + n * m = y) :
    Nat.ModEq m x y := by
  have : x % m = (x + n * m) % m := by rw [Nat.add_mul_mod_self_right]
  rw [Nat.ModEq, this, h]

/-- Converts pointwise limb-wise addition to `Field51_as_Nat` addition. -/
lemma pointwise_add_Field51_as_Nat (a b c : Array U64 5#usize)
    (h : ∀ i < 5, c[i]!.val = a[i]!.val + b[i]!.val) :
    Field51_as_Nat c = Field51_as_Nat a + Field51_as_Nat b := by
  simp only [Field51_as_Nat, Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
    List.Vector.length_val, UScalar.ofNatCore_val_eq,
    Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul,
    mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
    Nat.reduceLT, Nat.lt_add_one]
  simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
    UScalar.ofNatCore_val_eq, getElem!_pos, Nat.ofNat_pos,
    Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
  scalar_tac

def U8x32_as_Nat_foldr (bytes : Array U8 32#usize) :=
  bytes.val.foldr (fun b (acc : ℕ) => b.val + 256 * acc) 0

lemma U8x32_as_Nat_eq_foldr' (a : Aeneas.Std.Array U8 32#usize) :
  U8x32_as_Nat a = U8x32_as_Nat_foldr a := by
  unfold U8x32_as_Nat_foldr
  apply U8x32_as_Nat_eq_foldr
