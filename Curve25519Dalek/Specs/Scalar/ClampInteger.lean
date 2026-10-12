/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Dana Mukusheva
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Curve25519Dalek.Auxiliary
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Spec theorem for `curve25519_dalek::scalar::clamp_integer`

Applies bitwise clamping to a 32-byte little-endian scalar representation:
• clears the three lowest bits of byte[0] (ensuring divisibility by the cofactor h = 8),
• clears the highest bit of byte[31] (ensuring the value < 2^255),
• sets bit 6 of byte[31] (ensuring the value ≥ 2^254).

The spec states that the result is exactly `clampBytes bytes`, where `clampBytes` transcribes
the clamping steps of `decodeScalar25519` in RFC 7748 §5. The arithmetic form of the clamped
value and its bounds and divisibility are proved as separate lemmas.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek scalar

attribute [-simp] Int.reducePow Nat.reducePow

/-- Clamping of a 32-byte X25519 scalar, transcribed from `decodeScalar25519` in RFC 7748 §5:
```
k_list[0] &= 248
k_list[31] &= 127
k_list[31] |= 64
```
The RFC then decodes the clamped bytes as a little-endian integer, i.e.
`U8x32_as_Nat (clampBytes k)`. -/
def clampBytes (k : Array U8 32#usize) : Array U8 32#usize :=
  let k := k.set 0#usize (k[0]! &&& 248#u8)
  let k := k.set 31#usize (k[31]! &&& 127#u8)
  k.set 31#usize (k[31]! ||| 64#u8)

/-- A little-endian number with `n` base-`2^8` digits is `< 2^(8 * n)`. -/
private lemma sum_bytes_lt (v : ℕ → ℕ) (hv : ∀ i, v i < 2 ^ 8) (n : ℕ) :
    ∑ i ∈ Finset.range n, 2 ^ (8 * i) * v i < 2 ^ (8 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_succ, pow_add]
    have := hv n
    have : 2 ^ (8 * n) * v n ≤ 2 ^ (8 * n) * (2 ^ 8 - 1) := by
      gcongr; omega
    have : 2 ^ (8 * n) * (2 ^ 8 - 1) + 2 ^ (8 * n) = 2 ^ (8 * n) * 2 ^ 8 := by
      rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by positivity))]
    omega

/-- Splits the little-endian value of 32 bytes into the lowest byte, the middle 30 bytes
and the highest byte. -/
private lemma U8x32_as_Nat_split (bytes : Array U8 32#usize) :
    U8x32_as_Nat bytes = bytes[0]!.val +
      2 ^ 8 * (∑ i ∈ Finset.range 30, 2 ^ (8 * i) * bytes[i + 1]!.val) +
      2 ^ 248 * bytes[31]!.val := by
  unfold U8x32_as_Nat
  rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => (by ring :
    2 ^ (8 * (i + 1)) * (bytes[i + 1]!).val = 2 ^ 8 * (2 ^ (8 * i) * (bytes[i + 1]!).val))]
  simp only [Nat.reduceMul, pow_zero, one_mul]
  ring

/-- The little-endian value of the clamped bytes: bits 3 to 253 of the input are kept,
bit 254 is set, and every other bit is cleared. -/
theorem U8x32_as_Nat_clampBytes (bytes : Array U8 32#usize) :
    U8x32_as_Nat (clampBytes bytes) = 2 ^ 254 + 8 * ((U8x32_as_Nat bytes / 8) % 2 ^ 251) := by
  have hmid : ∀ i ∈ Finset.range 30, 2 ^ (8 * i) * (clampBytes bytes)[i + 1]!.val =
      2 ^ (8 * i) * bytes[i + 1]!.val := by
    intro i hi
    have := Finset.mem_range.mp hi
    simp only [clampBytes, Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      Nat.ofNat_pos, getElem!_pos, ne_eq, Nat.lt_add_one, Array.set_val_eq, List.length_set,
      List.set_set, List.getElem!_eq_getElem?_getD, mul_eq_mul_left_iff, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, mul_eq_zero, false_or, false_and, or_false]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  -- Clearing the three lowest bits of a byte rounds it down to a multiple of 8.
  have hlo : (clampBytes bytes)[0]!.val = 8 * (bytes[0]!.val / 8) := by
    have key : ∀ n < 2 ^ 8, n &&& 248 = 8 * (n / 8) := by decide +kernel
    simp only [clampBytes, Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      Nat.ofNat_pos, getElem!_pos, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.lt_add_one,
      Array.set_val_eq, List.length_set, and_self, List.set_set, Nat.not_eq, OfNat.ofNat_ne_zero,
      not_lt_zero, or_true, or_self, List.set_getElem!_not_eq, List.getElem_set_self,
      UScalar.val_and]
    exact key _ (by scalar_tac)
  -- Clearing bit 7 and setting bit 6 of a byte keeps its six lowest bits and adds 64.
  have hhi : (clampBytes bytes)[31]!.val = 64 + bytes[31]!.val % 64 := by
    have key : ∀ n < 2 ^ 8, n &&& 127 ||| 64 = 64 + n % 64 := by decide +kernel
    simp only [clampBytes, Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      Nat.ofNat_pos, getElem!_pos, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.lt_add_one,
      Array.set_val_eq, List.length_set, List.set_set, List.getElem_set_self, List.getElem_set_ne,
      UScalar.val_or, UScalar.val_and]
    exact key _ (by scalar_tac)
  have hM := sum_bytes_lt (fun i => bytes[i + 1]!.val) (fun i => by scalar_tac) 30
  have h0 : bytes[0]!.val < 2 ^ 8 := by scalar_tac
  rw [U8x32_as_Nat_split, U8x32_as_Nat_split bytes, Finset.sum_congr rfl hmid, hlo, hhi]
  generalize ∑ i ∈ Finset.range 30, 2 ^ (8 * i) * bytes[i + 1]!.val = M at *
  simp only [Nat.reducePow, Nat.reduceMul] at *
  omega

/-- The clamped value is divisible by the cofactor `h = 8`. -/
theorem h_dvd_U8x32_as_Nat_clampBytes (bytes : Array U8 32#usize) :
    h ∣ U8x32_as_Nat (clampBytes bytes) := by
  rw [U8x32_as_Nat_clampBytes, h]
  omega

/-- The clamped value is `< 2^255`. -/
theorem U8x32_as_Nat_clampBytes_lt (bytes : Array U8 32#usize) :
    U8x32_as_Nat (clampBytes bytes) < 2 ^ 255 := by
  rw [U8x32_as_Nat_clampBytes]
  omega

/-- The clamped value is `≥ 2^254`. -/
theorem le_U8x32_as_Nat_clampBytes (bytes : Array U8 32#usize) :
    2 ^ 254 ≤ U8x32_as_Nat (clampBytes bytes) := by
  rw [U8x32_as_Nat_clampBytes]
  omega

namespace curve25519_dalek.scalar

/-- **Spec theorem for `curve25519_dalek::scalar::clamp_integer`**
• The function always succeeds (no panic) for any 32-byte input
• The result is `clampBytes bytes`, the clamping of RFC 7748 §5
• Consequently (see `U8x32_as_Nat_clampBytes`), the result's value is
  `2^254 + 8 * ((U8x32_as_Nat bytes / 8) % 2^251)`: divisible by `h = 8` and in `[2^254, 2^255)`
-/
@[step]
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (result : Array U8 32#usize) =>
      result = clampBytes bytes ⦄ := by
  unfold clamp_integer clampBytes
  step*
  have e1 : i1 = i &&& 248#u8 := UScalar.eq_of_val_eq i1_post1
  have e3 : i3 = i2 &&& 127#u8 := UScalar.eq_of_val_eq i3_post1
  have e5 : i5 = i4 ||| 64#u8 := UScalar.eq_of_val_eq i5_post1
  subst_vars
  simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq, ne_eq, OfNat.zero_ne_ofNat,
    not_false_eq_true, List.getElem_set_ne, List.getElem_set_self, Array.getElem!_Nat_eq,
    List.Vector.length_val, Nat.ofNat_pos, getElem!_pos, Nat.lt_add_one, List.length_set]

end curve25519_dalek.scalar
