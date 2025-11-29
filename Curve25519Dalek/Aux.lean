import Aeneas
import Curve25519Dalek.Defs
import Mathlib

set_option linter.style.longLine false

/-! # Auxiliary theorems

Theorems which are useful for proving spec theorems in this project but aren't available upstream.
This file is for theorems which depend only on Defs.lean, not on Funs.lean or Types.lean. -/

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
  simp [Nat.shiftRight_eq_div_pow]

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
theorem Array.set_of_ne' (bs : Array U64 5#usize) (a : U64) (i : Nat) (j : Usize) (hi : i < bs.length)
    (h : i ≠ j) :
    (bs.set j a)[i]! = bs[i] := by
  rw [Array.getElem!_Nat_eq, Array.set_val_eq, ← Array.val_getElem!_eq' bs i hi]
  exact List.getElem!_set_ne bs j i a (by omega)

/-- If a 32-byte array represents a value less than `2 ^ 252`, then the high bit (bit 7) of byte 31
must be 0. -/
theorem high_bit_zero_of_lt_255 (bytes : Array U8 32#usize) (h : U8x32_as_Nat bytes < 2 ^ 255) :
    bytes.val[31]!.val >>> 7 = 0 := by
  by_contra!
  have : 2 ^ 7 ≤ bytes.val[31]!.val := by omega
  have : 2 ^ 255 ≤ U8x32_as_Nat bytes := by
    unfold U8x32_as_Nat
    have : ∑ i ∈ Finset.range 32, 2^(8*i) * bytes.val[i]!.val =
        ∑ i ∈ Finset.range 31, 2^(8*i) * bytes.val[i]!.val + 2^(8*31) * bytes.val[31]!.val := by
      rw [Finset.sum_range_succ]
    simp_all; grind
  grind

/-- If a 32-byte array represents a value less than `L`, then the high bit (bit 7) of byte 31
must be 0. -/
theorem high_bit_zero_of_lt_L (bytes : Array U8 32#usize) (h : U8x32_as_Nat bytes < L) :
    bytes.val[31]!.val >>> 7 = 0 := by
  refine high_bit_zero_of_lt_255 bytes ?_
  have : L ≤ 2 ^ 255 := by decide
  grind






















def aa : Aeneas.Std.Array U8 32#usize :=
  ⟨[1#u8, 1#u8, 0#u8, 0#u8, 32#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 1#u8, 0#u8, 8#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 1#u8], by decide⟩

#eval U8x32_as_Nat aa = Nat.ofDigits (2 ^ 8) (List.ofFn fun i : Fin 32 => aa[i]!.val)

#check (List.ofFn fun i : Fin 32 => aa[i]!.val)









lemma U8x32_as_Nat_is_NatofDigits (a : Aeneas.Std.Array U8 32#usize) :
    U8x32_as_Nat a = Nat.ofDigits (2 ^ 8) (List.ofFn fun i : Fin 32 => a[i]!.val) := by
    sorry





lemma U8_Array_elements_lt_256 {n : Usize} (a : Aeneas.Std.Array U8 n) :
    ∀ l ∈ (List.ofFn fun i : Fin 32 => a[i]!.val), l < 2 ^ 8 := by
  intro l hl
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact Aeneas.Std.UScalar.hBounds (a[i]!)


lemma U8x32_as_Nat_injective : Function.Injective U8x32_as_Nat := by

  intro a a' h_funs_eq

  rw [U8x32_as_Nat_is_NatofDigits a, U8x32_as_Nat_is_NatofDigits a'] at h_funs_eq

  set L := (List.ofFn fun i : Fin 32 => a[i]!.val)
  set L' := (List.ofFn fun i : Fin 32 => a'[i]!.val)
  set b := (2 ^ 8 : Nat)

  have h_inj := Nat.ofDigits_inj_of_len_eq
    (b := b)
    (by omega : 1 < b)
    (L1 := L)
    (L2 := L')
    (by rw [List.length_ofFn, List.length_ofFn])
    (by exact U8_Array_elements_lt_256 a)
    (by exact U8_Array_elements_lt_256 a')
    (by exact h_funs_eq)

  simp only [L, L'] at h_inj
  rw [List.ofFn_inj] at h_inj
  apply Subtype.eq
  apply List.ext_get

  · simp only [List.Vector.length_val, UScalar.ofNat_val_eq]
  · intro n h_a h_a'
    have h_len : n < 32 := by  simp_all only [Fin.getElem!_fin, Array.getElem!_Nat_eq,
        List.Vector.length_val, UScalar.ofNat_val_eq, Fin.is_lt, getElem!_pos]
    have h_congr := congr_fun h_inj ⟨n, h_len⟩
    have h_a_len : a.val.length = 32 := by simp only [List.Vector.length_val, UScalar.ofNat_val_eq]
    cases a' with | mk val_a' =>
    cases a with | mk val_a =>
    simp_all only [UScalar.ofNat_val_eq, Fin.getElem!_fin, Array.getElem!_Nat_eq, Fin.is_lt,
        getElem!_pos, List.get_eq_getElem]
    exact UScalar.eq_of_val_eq h_congr
