/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Math.BitList
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.ExternallyVerified
/-! # FromBytes
Specification and proof for `FieldElement51::from_bytes`.
This function constructs a field element from a 32-byte array.
Source: curve25519-dalek/src/backend/serial/u64/field.rs

-/

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open scoped BigOperators


/- **Proof strategy: List Bool interpretation**

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

## Approach

We think of the 32 bytes as a single list of 256 booleans (bits), LSB-first:
  `bits[0], bits[1], ..., bits[255]`.
Byte `bytes[i]` contributes `bits[8i .. 8i+7]`.

Every operation in `from_bytes` is a simple list operation:
  - `load8_at(bytes, i)` → extract sublist `bits[8i .. 8i+63]` (64 bits)
  - `>> k` (right shift)  → drop the first `k` elements from the list
  - `& low_51_bit_mask`   → take only the first 51 elements (truncate the tail)

Tracing each limb:

  | Limb | load           | shift  | mask    | Result bits       |
  |------|----------------|--------|---------|-------------------|
  |  0   | bits[0..64)    | none   | take 51 | bits[0..51)       |
  |  1   | bits[48..112)  | drop 3 | take 51 | bits[51..102)     |
  |  2   | bits[96..160)  | drop 6 | take 51 | bits[102..153)    |
  |  3   | bits[152..216) | drop 1 | take 51 | bits[153..204)    |
  |  4   | bits[192..256) | drop 12| take 51 | bits[204..255)    |

The 5 limbs extract exactly the 5 consecutive, non-overlapping 51-bit slices
covering `bits[0..255)`. Bit 255 (the 256th bit) is discarded — this is the `% 2^255`.

## Proof structure

1. `load8_at_bitList_spec`:
   `ofU64 result = (ofByteList input.val).extract (8*i) (8*i + 64)`

2. For each limb, the shift+mask chain gives:
   `ofU64 result[i] ≈ₗ allBits.extract (51*i) (51*i + 51)`
   using: `ofNat_equiv_of_lt`, `ofNat_mod`, `ofNat_extract`, `extract_extract`

3. `from_bytes_bitList_spec` → `from_bytes_spec` via:
   `field51_eq_of_bitList` + `limb_bound_of_equiv`
-/

open BitList

/-! ## load8_at specification

`load8_at` loads 8 consecutive bytes from a slice and packs them into a U64 in little-endian order.
In List Bool terms, the result's bits are exactly the 64 bits starting at position `8*i` in the
slice's bit representation. -/

private lemma u8_mul_pow_lt_u64_size (x : U8) (k : Nat) (hk : k ≤ 56) :
    x.val * 2 ^ k < U64.size := calc
    _ ≤ 255 * 2 ^ 56 := Nat.mul_le_mul (Nat.lt_succ_iff.mp x.hmax)
        (Nat.pow_le_pow_right (by omega) hk)
    _ < U64.size := by scalar_tac

private lemma u8_val_mod_u64_numBits (x : U8) :
    x.val % 2 ^ UScalarTy.U64.numBits = x.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.hmax (by norm_num))

private lemma u8_mul_pow_mod_u64 (x : U8) (k : Nat) (hk : k ≤ 56) :
    x.val * 2 ^ k % U64.size = x.val * 2 ^ k :=
  Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size x k hk)

/-- Left-associated OR of 8 byte values shifted by multiples of 8 equals their sum. -/
private lemma or_bytes_eq_sum (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (_ : b0 < 256) (_ : b1 < 256)
    (_ : b2 < 256) (_ : b3 < 256) (_ : b4 < 256) (_ : b5 < 256) (_ : b6 < 256) (_ : b7 < 256) :
    ((((((b0 ||| b1 * 2^8) ||| b2 * 2^16) ||| b3 * 2^24) |||
      b4 * 2^32) ||| b5 * 2^40) ||| b6 * 2^48) ||| b7 * 2^56 =
      b0 + b1 * 2^8 + b2 * 2^16 + b3 * 2^24 + b4 * 2^32 + b5 * 2^40 + b6 * 2^48 + b7 * 2^56 := by
  rw [or_mul_pow_two_eq_add _ _ 8 (by omega), or_mul_pow_two_eq_add _ _ 16 (by grind),
    or_mul_pow_two_eq_add _ _ 24 (by grind), or_mul_pow_two_eq_add _ _ 32 (by grind),
    or_mul_pow_two_eq_add _ _ 40 (by grind), or_mul_pow_two_eq_add _ _ 48 (by grind),
    or_mul_pow_two_eq_add _ _ 56 (by grind)]

/-- The Nat-level spec for load8_at: the result is the little-endian combination of 8 bytes. -/
@[progress]
theorem load8_at_val_spec (input : Slice U8) (i : Usize) (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ (result : U64) =>
      result.val = ∑ j ∈ Finset.range 8, input[i.val + j]!.val * 2 ^ (8 * j) ⦄ := by
  unfold from_bytes.load8_at
  progress*
  simp (discharger := omega) only [*, UScalar.val_or, UScalar.cast_val_eq, u8_val_mod_u64_numBits,
    Nat.shiftLeft_eq, u8_mul_pow_mod_u64]
  rw [or_bytes_eq_sum _ _ _ _ _ _ _ _ (input.val[i.val]!).hmax (input.val[i.val + 1]!).hmax
    (input.val[i.val + 2]!).hmax (input.val[i.val + 3]!).hmax (input.val[i.val + 4]!).hmax
    (input.val[i.val + 5]!).hmax (input.val[i.val + 6]!).hmax (input.val[i.val + 7]!).hmax]
  simp [Finset.sum_range_succ]

private lemma extract_getElem! (l : List U8) (i j : Nat) (hj : j < 8) :
    (l.extract i (i + 8))[j]! = l[i + j]! := by grind

private lemma sum_extract_eq (l : List U8) (i : Nat) (hi : i + 8 ≤ l.length) :
    ∑ j ∈ Finset.range 8, l[i + j]!.val * 2 ^ (8 * j) =
      Nat.ofDigits 256 ((l.extract i (i + 8)).map (·.val)) := by
  have hlen : (l.extract i (i + 8)).length = 8 := by
    simp [List.extract_eq_drop_take, List.length_take, List.length_drop]; omega
  rw [ofDigits_map_val_eq_sum, hlen]
  apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
  rw [extract_getElem! l i j hj, show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]

/-- The List Bool spec for load8_at: the result bits are the 64 bits starting at byte position i. -/
@[progress]
theorem load8_at_bitList_spec (input : Slice U8) (i : Usize) (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ (result : U64) =>
      ofU64 result = (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64) ⦄ := by
  apply spec_mono (load8_at_val_spec input i h)
  intro result hval
  simp only [Slice.getElem!_Nat_eq] at hval
  set rhs := (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64)
  have hlen : rhs.length = 64 := by
    simp [rhs, List.extract_eq_drop_take, List.length_take, List.length_drop, ofByteList_length]
    omega
  have hval_eq : result.val = toNat rhs := by
    simp only [rhs]
    rw [show 8 * i.val + 64 = 8 * (i.val + 8) from by ring,
      ofByteList_extract input.val i.val (i.val + 8) (by omega),
      toNat_ofByteList, ← sum_extract_eq input.val i.val (by omega)]
    exact hval
  simp only [ofU64, hval_eq]
  rw [← hlen, ofNat_toNat rhs]

/-! ## BitList-native specs for shift and mask

These replace the Nat-level Aeneas specs with List Bool equivalents,
so the proof of `from_bytes_bitList_spec` stays entirely in List Bool land. -/

-- Remove @[progress] from the Nat-level specs so the BitList versions are preferred.
attribute [-progress] load8_at_val_spec load8_at_bitList_spec

/-- Right-shifting a U64 by k drops k bits from its List Bool representation. -/
@[progress]
theorem u64_shr_bitList_spec (x : U64) (k : I32) (hk0 : 0 ≤ k.val) (hk : k.val < 64) :
    (x >>> k) ⦃ z => ofU64 z ≈ₗ (ofU64 x).drop k.toNat ⦄ := by
  have hknat : k.toNat < 64 := by scalar_tac
  progress as ⟨z, hval, _⟩
  simp only [ofU64]
  rw [hval, Nat.shiftRight_eq_div_pow, ofNat_drop k.toNat 64 x.val (by omega)]
  exact ofNat_equiv_of_lt _ 64 _ (by omega) (by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add,
      show 64 - k.toNat + k.toNat = 64 from by omega]
    exact x.hmax)

/-- Masking a U64 with `2^n - 1` takes the first n bits. -/
theorem u64_and_mask_bitList_spec (x mask : U64) (n : Nat)
    (hn : n ≤ 64) (hmask : mask.val = 2 ^ n - 1) :
    lift (x &&& mask) ⦃ (z : UScalar UScalarTy.U64) => ofU64 z ≈ₗ (ofU64 x).take n ⦄ := by
  simp only [lift, spec_ok]
  have hval : (x &&& mask).val = x.val % 2 ^ n := by
    rw [UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod]
  simp only [ofU64, hval]
  rw [ofNat_take n 64 x.val (by omega), ← ofNat_mod n x.val]
  exact ofNat_equiv_of_lt n 64 (x.val % 2 ^ n) (by omega)
    (Nat.mod_lt _ (by positivity))

/-- Specialized mask spec for 51-bit mask with literal precondition for progress*. -/
@[progress]
theorem u64_and_mask51_bitList_spec (x mask : U64)
    (hmask : mask.val = 2251799813685247) :
    lift (x &&& mask) ⦃ (z : U64) => ofU64 z ≈ₗ (ofU64 x).take 51 ⦄ :=
  u64_and_mask_bitList_spec x mask 51 (by omega) (by omega)

/-- load8_at in List Bool terms, as a progress-compatible spec. -/
@[progress]
theorem load8_at_bitList_progress_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      ofU64 result ≈ₗ
        (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64) ⦄ := by
  exact spec_mono (load8_at_bitList_spec input i h) fun result heq => heq ▸ BitList.Equiv.refl _

/-! ## Bridge: List Bool spec implies Nat spec -/

/-- Equiv implies the limb value equals the slice value. -/
theorem field51_eq_of_bitList (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    Field51_as_Nat result = U8x32_as_Nat bytes % 2 ^ 255 := by
  unfold Field51_as_Nat
  have hsum : ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * result[i]!.val =
      ∑ i ∈ Finset.range 5,
        toNat ((ofByteArray bytes).extract (51 * i) (51 * i + 51)) * 2 ^ (51 * i) := by
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    rw [(toNat_ofU64 result[i]!).symm.trans (hequiv ⟨i, hi⟩).toNat_eq]; ring
  rw [hsum, ← toNat_split_chunks (ofByteArray bytes) 51 5 (by rw [ofByteArray_length]; norm_num),
    show 51 * 5 = 255 from by norm_num, toNat_take 255 (ofByteArray bytes), toNat_ofByteArray]

/-- The limb bound follows from Equiv (the extract has length ≤ 51). -/
theorem limb_bound_of_equiv (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    ∀ i : Fin 5, result[i]!.val < 2 ^ 51 := by
  intro i
  rw [← toNat_ofU64 result[i]!, (hequiv i).toNat_eq]
  refine (toNat_lt_pow _).trans_le (Nat.pow_le_pow_right (by omega) ?_)
  simp [List.extract_eq_drop_take, List.length_take, List.length_drop, ofByteArray_length]

/-! ## The pure List Bool specification for from_bytes -/

section
attribute [simp] List.extract_eq_drop_take List.drop_take List.drop_drop List.take_take
  inf_of_le_left

/-- The pure List Bool spec for from_bytes, using `BitList.Equiv` (≈ₗ). -/
@[progress]
theorem from_bytes_bitList_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      let allBits := ofByteArray bytes
      ∀ i : Fin 5, ofU64 result[i]! ≈ₗ allBits.extract (51 * i.val) (51 * i.val + 51) ⦄ := by
  unfold from_bytes
  progress*
  have hs : ∀ sx, sx = bytes.to_slice → ofByteList sx.val = ofByteList bytes.val := by
    intro sx hsx; rw [hsx]; simp [Array.to_slice]
  rw [hs s s_post] at i1_post; rw [hs s1 s1_post] at i3_post
  rw [hs s2 s2_post] at i6_post; rw [hs s3 s3_post] at i9_post
  rw [hs s4 s4_post] at i12_post
  intro i; fin_cases i <;> simp only [Array.make, ofByteArray]
  · exact i2_post.trans (i1_post.take 51 |>.trans (by simp; intro i; rfl))
  · exact i5_post.trans ((i4_post.take 51).trans ((i3_post.drop 3 |>.take 51).trans (by
      simp; intro i; rfl)))
  · exact i8_post.trans ((i7_post.take 51).trans ((i6_post.drop 6 |>.take 51).trans (by
      simp; intro i; rfl)))
  · exact i11_post.trans ((i10_post.take 51).trans ((i9_post.drop 1 |>.take 51).trans (by
      simp; intro i; rfl)))
  · exact i14_post.trans ((i13_post.take 51).trans ((i12_post.drop 12 |>.take 51).trans (by
      simp; intro i; rfl)))

end -- section: local simp attributes for extract/drop/take normalization

/-! ## Final spec -/

@[progress]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  progress*
  constructor
  · rw [field51_eq_of_bitList result bytes _]
    assumption
  · intro i hi
    exact limb_bound_of_equiv result bytes ‹_› ⟨i, hi⟩

attribute [-progress] from_bytes_bitList_spec

end curve25519_dalek.backend.serial.u64.field.FieldElement51
