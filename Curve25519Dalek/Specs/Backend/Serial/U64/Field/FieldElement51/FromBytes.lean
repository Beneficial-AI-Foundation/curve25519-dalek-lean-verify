/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.ExternallyVerified

/-! # FromBytes

Specification and proof for `FieldElement51::from_bytes`.
This function constructs a field element from a 32-byte array.
Source: curve25519-dalek/src/backend/serial/u64/field.rs

## Rust source

```rust
    pub const fn from_bytes(bytes: &[u8; 32]) -> FieldElement51 {
        const fn load8_at(input: &[u8], i: usize) -> u64 {
               (input[i] as u64)
            | ((input[i + 1] as u64) << 8)
            | ((input[i + 2] as u64) << 16)
            | ((input[i + 3] as u64) << 24)
            | ((input[i + 4] as u64) << 32)
            | ((input[i + 5] as u64) << 40)
            | ((input[i + 6] as u64) << 48)
            | ((input[i + 7] as u64) << 56)
        }

        let low_51_bit_mask = (1u64 << 51) - 1;
        FieldElement51(
        [  load8_at(bytes,  0)        & low_51_bit_mask
        , (load8_at(bytes,  6) >>  3) & low_51_bit_mask
        , (load8_at(bytes, 12) >>  6) & low_51_bit_mask
        , (load8_at(bytes, 19) >>  1) & low_51_bit_mask
        , (load8_at(bytes, 24) >> 12) & low_51_bit_mask
        ])
    }
```

## Proof structure

1. `load8_at_val_spec`: byte-pack lemma —
   `load8_at(input, i).val = ∑ j ∈ range 8, input[i + j]!.val * 2 ^ (8 j)`.
2. `limb_slicing`: pure-Nat identity equating the five limb formulas to
   `U8x32_as_Nat bytes mod 2 ^ 255`.
3. `load8_at_eq_shift`: byte-sum at offset `i` equals the 64-bit slice
   `(U8x32_as_Nat bytes / 2 ^ (8 i)) % 2 ^ 64`.
4. `limb_eq_aux`: the shift+mask reduction
   `(B / 2 ^ k) % 2 ^ 64 / 2 ^ s % 2 ^ 51 = B / 2 ^ (k + s) % 2 ^ 51`.
5. `from_bytes_spec`: glues the `step*` posts to the limb-level postcondition.
-/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open scoped BigOperators

/-! ## load8_at specification (Nat-level only) -/

/-- The Nat-level spec for `load8_at`: the result is the little-endian combination of 8 bytes. -/
@[step]
theorem load8_at_val_spec (input : Slice U8) (i : Usize) (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ (result : U64) =>
      result.val = ∑ j ∈ Finset.range 8, input[i.val + j]!.val * 2 ^ (8 * j) ⦄ := by
  unfold from_bytes.load8_at
  step*
  simp (discharger := omega) only [*, UScalar.val_or, UScalar.cast_val_eq, u8_val_mod_u64_numBits,
    Nat.shiftLeft_eq, u8_mul_pow_mod_u64]
  rw [or_bytes_eq_sum _ _ _ _ _ _ _ _ (input.val[i.val]!).hmax (input.val[i.val + 1]!).hmax
    (input.val[i.val + 2]!).hmax (input.val[i.val + 3]!).hmax (input.val[i.val + 4]!).hmax
    (input.val[i.val + 5]!).hmax (input.val[i.val + 6]!).hmax (input.val[i.val + 7]!).hmax]
  simp [Finset.sum_range_succ]

/-! ## Bit-slicing identity (pure Nat) -/

/-- The five 51-bit limbs of `B mod 2^255` are `(B / 2^(51 k)) mod 2^51` for `k = 0..4`. -/
private theorem limb_slicing (B : Nat) :
    B % 2 ^ 51
    + 2 ^ 51 * ((B / 2 ^ 51) % 2 ^ 51)
    + 2 ^ 102 * ((B / 2 ^ 102) % 2 ^ 51)
    + 2 ^ 153 * ((B / 2 ^ 153) % 2 ^ 51)
    + 2 ^ 204 * ((B / 2 ^ 204) % 2 ^ 51)
    = B % 2 ^ 255 := by
  have d0 := Nat.div_add_mod B (2 ^ 51)
  have d1 := Nat.div_add_mod (B / 2 ^ 51) (2 ^ 51)
  have d2 := Nat.div_add_mod (B / 2 ^ 102) (2 ^ 51)
  have d3 := Nat.div_add_mod (B / 2 ^ 153) (2 ^ 51)
  have d4 := Nat.div_add_mod (B / 2 ^ 204) (2 ^ 51)
  have dB := Nat.div_add_mod B (2 ^ 255)
  have hpow : (2 : Nat) ^ 255 = 2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * 2 ^ 51))) := by norm_num
  have hdd : ∀ a b, a + 51 = b → B / 2 ^ a / 2 ^ 51 = B / 2 ^ b := fun a b h => by
    rw [Nat.div_div_eq_div_mul, ← pow_add, h]
  have hd1 := hdd 51 102 rfl
  have hd2 := hdd 102 153 rfl
  have hd3 := hdd 153 204 rfl
  have hd4 := hdd 204 255 rfl
  omega

/-! ## Bridge: load8_at as a slice of `U8x32_as_Nat bytes` -/

/-- A sum of bytes (each `< 2^8`) shifted by their offset positions is bounded by `2^(8n)`. -/
private lemma byte_sum_lt (bytes : Array U8 32#usize) (i n : Nat) (hn : i + n ≤ 32) :
    ∑ k ∈ Finset.range n, bytes[i + k]!.val * 2 ^ (8 * k) < 2 ^ (8 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (by omega)
    have hb : (bytes[i + n]! : U8).val < 2 ^ 8 := by
      have := (bytes[i + n]! : U8).hmax; scalar_tac
    have : ((bytes[i + n]! : U8).val + 1) * 2 ^ (8 * n) ≤ 2 ^ 8 * 2 ^ (8 * n) :=
      Nat.mul_le_mul_right _ hb
    rw [Finset.sum_range_succ, show (8 * (n + 1) : Nat) = 8 * n + 8 from by ring, pow_add]
    nlinarith

/-- Sum of `f` over `range 32` decomposes into three blocks around `i..i+8`. -/
private lemma sum_split_three (f : Nat → Nat) (i : Nat) (hi : i + 8 ≤ 32) :
    ∑ k ∈ Finset.range 32, f k =
      (∑ k ∈ Finset.range i, f k)
      + (∑ k ∈ Finset.range 8, f (i + k))
      + (∑ k ∈ Finset.range (32 - (i + 8)), f (i + 8 + k)) := by
  conv_lhs => rw [show (32 : Nat) = (i + 8) + (32 - (i + 8)) from by omega,
    Finset.sum_range_add, Finset.sum_range_add (n := i) (m := 8)]

/-- An 8-byte little-endian load at offset `i` is the corresponding 64-bit slice
of the full 32-byte little-endian value. -/
private theorem load8_at_eq_shift (bytes : Array U8 32#usize) (i : Nat) (hi : i + 8 ≤ 32) :
    ∑ j ∈ Finset.range 8, bytes[i + j]!.val * 2 ^ (8 * j) =
      (U8x32_as_Nat bytes / 2 ^ (8 * i)) % 2 ^ 64 := by
  set lower := ∑ k ∈ Finset.range i, bytes[k]!.val * 2 ^ (8 * k) with hlower_def
  set middle := ∑ j ∈ Finset.range 8, bytes[i + j]!.val * 2 ^ (8 * j) with hmiddle_def
  set upper :=
    ∑ k ∈ Finset.range (32 - (i + 8)), bytes[i + 8 + k]!.val * 2 ^ (8 * k) with hupper_def
  have hlow_lt : lower < 2 ^ (8 * i) := by simpa using byte_sum_lt bytes 0 i (by omega)
  have hmid_lt : middle < 2 ^ 64 := by simpa using byte_sum_lt bytes i 8 hi
  have hsplit :
      U8x32_as_Nat bytes = lower + 2 ^ (8 * i) * middle + 2 ^ (8 * (i + 8)) * upper := by
    have hsum := sum_split_three (fun k => 2 ^ (8 * k) * bytes[k]!.val) i hi
    simp only [U8x32_as_Nat, hsum]
    have hlow_rw : ∑ k ∈ Finset.range i, 2 ^ (8 * k) * bytes[k]!.val = lower := by
      simp only [hlower_def]; exact Finset.sum_congr rfl fun _ _ => by ring
    have hmid_rw : ∑ k ∈ Finset.range 8, 2 ^ (8 * (i + k)) * bytes[i + k]!.val
        = 2 ^ (8 * i) * middle := by
      simp only [hmiddle_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (8 * (i + j) : Nat) = 8 * i + 8 * j from by ring, pow_add]; ring
    have hup_rw : ∑ k ∈ Finset.range (32 - (i + 8)),
        2 ^ (8 * (i + 8 + k)) * bytes[i + 8 + k]!.val = 2 ^ (8 * (i + 8)) * upper := by
      simp only [hupper_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (8 * (i + 8 + j) : Nat) = 8 * (i + 8) + 8 * j from by ring, pow_add]; ring
    rw [hlow_rw, hmid_rw, hup_rw]
  rw [hsplit,
    show (2 : Nat) ^ (8 * (i + 8)) = 2 ^ (8 * i) * 2 ^ 64 from by
      rw [show (8 * (i + 8) : Nat) = 8 * i + 64 from by ring, pow_add],
    show lower + 2 ^ (8 * i) * middle + 2 ^ (8 * i) * 2 ^ 64 * upper
      = lower + (middle + 2 ^ 64 * upper) * 2 ^ (8 * i) from by ring,
    Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero (by positivity)),
    Nat.div_eq_of_lt hlow_lt, Nat.zero_add, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt hmid_lt).symm

/-- The shift+mask formula reducing `(B / 2^k) % 2^64 / 2^s % 2^51` to `B / 2^(k+s) % 2^51`.
Requires `s + 51 ≤ 64` so the inner mod doesn't lose bits. -/
private lemma limb_eq_aux (B k s : Nat) (hs : s + 51 ≤ 64) :
    (B / 2 ^ k) % 2 ^ 64 / 2 ^ s % 2 ^ 51 = B / 2 ^ (k + s) % 2 ^ 51 := by
  rw [show (64 : Nat) = s + (64 - s) from by omega, pow_add, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← pow_add, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-! ## Final spec -/

@[step]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold from_bytes
  let* ⟨ _, shift_post1, _ ⟩ ← U64.ShiftLeft_IScalar_spec
  let* ⟨ mask, mask_post1, _ ⟩ ← U64.sub_spec
  let* ⟨ s0, s0_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ ld0, ld0_post ⟩ ← load8_at_val_spec
  let* ⟨ l0, l0_post1, _ ⟩ ← UScalar.and_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ ld1, ld1_post ⟩ ← load8_at_val_spec
  let* ⟨ sh1, sh1_post1, _ ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ l1, l1_post1, _ ⟩ ← UScalar.and_spec
  let* ⟨ s2, s2_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ ld2, ld2_post ⟩ ← load8_at_val_spec
  let* ⟨ sh2, sh2_post1, _ ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ l2, l2_post1, _ ⟩ ← UScalar.and_spec
  let* ⟨ s3, s3_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ ld3, ld3_post ⟩ ← load8_at_val_spec
  let* ⟨ sh3, sh3_post1, _ ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ l3, l3_post1, _ ⟩ ← UScalar.and_spec
  let* ⟨ s4, s4_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ ld4, ld4_post ⟩ ← load8_at_val_spec
  let* ⟨ sh4, sh4_post1, _ ⟩ ← U64.ShiftRight_IScalar_spec
  let* ⟨ l4, l4_post1, _ ⟩ ← UScalar.and_spec
  have hmask : mask.val = 2 ^ 51 - 1 := by scalar_tac
  -- Each `ldN` is the 64-bit slice of `U8x32_as_Nat bytes` at byte offset `i`.
  have hld : ∀ {ld : U64} {sx : Slice U8} (i : Nat), i + 8 ≤ 32 →
      sx = bytes.to_slice →
      ld.val = ∑ x ∈ Finset.range 8, sx[i + x]!.val * 2 ^ (8 * x) →
      ld.val = U8x32_as_Nat bytes / 2 ^ (8 * i) % 2 ^ 64 := by
    intro ld sx i hi hsx h
    have : sx.val = bytes.val := by simp [hsx, Array.to_slice]
    rw [h]; simp only [Slice.getElem!_Nat_eq, this]
    simpa using load8_at_eq_shift bytes i hi
  -- Each `lN` is the 51-bit slice of `U8x32_as_Nat bytes` at bit offset `8*i + s = 51*k`.
  have hl : ∀ {l ld sh : U64} {sx : Slice U8} (i s k : Nat),
      i + 8 ≤ 32 → s + 51 ≤ 64 → 8 * i + s = 51 * k →
      sx = bytes.to_slice →
      ld.val = ∑ x ∈ Finset.range 8, sx[i + x]!.val * 2 ^ (8 * x) →
      sh.val = ld.val >>> s →
      l.val = (sh &&& mask).val →
      l.val = U8x32_as_Nat bytes / 2 ^ (51 * k) % 2 ^ 51 := by
    intro l ld sh sx i s k hi hs hk hsx hld' hsh hl
    rw [hl, UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod, hsh,
      Nat.shiftRight_eq_div_pow, hld i hi hsx hld', limb_eq_aux _ (8 * i) s hs, hk]
  -- Specialise to each limb. For limb 0 we use `sh := ld0` (no shift).
  have hl0v : l0.val = U8x32_as_Nat bytes % 2 ^ 51 := by
    simpa using hl (l := l0) (sh := ld0) 0 0 0 (by omega) (by omega) rfl
      s0_post ld0_post (by simp) l0_post1
  have hl1v := hl (l := l1) 6 3 1 (by omega) (by omega) (by norm_num)
    s1_post ld1_post sh1_post1 l1_post1
  have hl2v := hl (l := l2) 12 6 2 (by omega) (by omega) (by norm_num)
    s2_post ld2_post sh2_post1 l2_post1
  have hl3v := hl (l := l3) 19 1 3 (by omega) (by omega) (by norm_num)
    s3_post ld3_post sh3_post1 l3_post1
  have hl4v := hl (l := l4) 24 12 4 (by omega) (by omega) (by norm_num)
    s4_post ld4_post sh4_post1 l4_post1
  -- Resolve each `result[k]!` to the corresponding limb.
  have hk0 : ((Array.make 5#usize [l0, l1, l2, l3, l4]).val[0]! : U64) = l0 := by simp [Array.make]
  have hk1 : ((Array.make 5#usize [l0, l1, l2, l3, l4]).val[1]! : U64) = l1 := by simp [Array.make]
  have hk2 : ((Array.make 5#usize [l0, l1, l2, l3, l4]).val[2]! : U64) = l2 := by simp [Array.make]
  have hk3 : ((Array.make 5#usize [l0, l1, l2, l3, l4]).val[3]! : U64) = l3 := by simp [Array.make]
  have hk4 : ((Array.make 5#usize [l0, l1, l2, l3, l4]).val[4]! : U64) = l4 := by simp [Array.make]
  refine ⟨?_, ?_⟩
  · -- Equality (stronger than `≡`).
    show Field51_as_Nat _ ≡ _ [MOD p]
    have : Field51_as_Nat (Array.make 5#usize [l0, l1, l2, l3, l4])
        = U8x32_as_Nat bytes % 2 ^ 255 := by
      simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
        zero_add, Nat.reduceMul, pow_zero, one_mul, Array.getElem!_Nat_eq,
        hk0, hk1, hk2, hk3, hk4, hl0v, hl1v, hl2v, hl3v, hl4v]
      linarith [limb_slicing (U8x32_as_Nat bytes)]
    rw [this]
  · -- Bounds for each limb (each is `_ % 2 ^ 51`).
    intro i hi
    simp only [Array.getElem!_Nat_eq]
    interval_cases i <;>
    · first | rw [hk0, hl0v] | rw [hk1, hl1v] | rw [hk2, hl2v] | rw [hk3, hl3v] | rw [hk4, hl4v]
      exact Nat.mod_lt _ (by positivity)

end curve25519_dalek.backend.serial.u64.field.FieldElement51
