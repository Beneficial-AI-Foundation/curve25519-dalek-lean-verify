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

Think of the 32 bytes as a single list of 256 booleans (bits), LSB-first:
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

`load8_at` loads 8 consecutive bytes from a slice and packs them into a U64
in little-endian order. In List Bool terms, the result's bits are exactly
the 64 bits starting at position `8*i` in the slice's bit representation. -/

private lemma u8_mul_pow_lt_u64_size (x : U8) (k : Nat) (hk : k ≤ 56) :
    x.val * 2 ^ k < U64.size := by
  have hx : x.val ≤ 255 := Nat.lt_succ_iff.mp x.hmax
  calc x.val * 2 ^ k
      ≤ 255 * 2 ^ k := Nat.mul_le_mul_right _ hx
    _ ≤ 255 * 2 ^ 56 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hk)
    _ < U64.size := by scalar_tac

private lemma u8_val_mod_u64_numBits (x : U8) :
    x.val % 2 ^ UScalarTy.U64.numBits = x.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.hmax (by norm_num))

/-- The Nat-level spec for load8_at: the result is the little-endian
    combination of 8 consecutive bytes. -/
@[progress]
theorem load8_at_val_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      result.val = ∑ j ∈ Finset.range 8,
        input[i.val + j]!.val * 2 ^ (8 * j) ⦄ := by
  unfold from_bytes.load8_at
  progress*
  simp only [i32_post1, i27_post1, i22_post1, i17_post1, i12_post1, i7_post1, UScalar.val_or]
  simp only [i36_post1, i31_post1, i26_post1, i21_post1, i16_post1, i11_post1, i6_post1]
  simp only [i35_post, i30_post, i25_post, i20_post, i15_post, i10_post, i5_post, i2_post,
    UScalar.cast_val_eq]
  simp only [i34_post, i29_post, i24_post, i19_post, i14_post, i9_post, i4_post, i1_post,
    i33_post, i28_post, i23_post, i18_post, i13_post, i8_post, i3_post]
  simp only [u8_val_mod_u64_numBits, Nat.shiftLeft_eq]
  conv_lhs =>
    rw [Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size (input.val[i.val + 1]!) 8 (by omega))]
    rw [Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size (input.val[i.val + 2]!) 16 (by omega))]
    rw [Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size (input.val[i.val + 3]!) 24 (by omega))]
    rw [Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size (input.val[i.val + 4]!) 32 (by omega))]
    rw [Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size (input.val[i.val + 5]!) 40 (by omega))]
    rw [Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size (input.val[i.val + 6]!) 48 (by omega))]
    rw [Nat.mod_eq_of_lt (u8_mul_pow_lt_u64_size (input.val[i.val + 7]!) 56 (by omega))]
  rw [or_mul_pow_two_eq_add _ _ 8 (by exact (input.val[i.val]!).hmax)]
  rw [or_mul_pow_two_eq_add _ _ 16 (by
    have := (input.val[i.val]!).hmax; have := (input.val[i.val + 1]!).hmax
    norm_num at *; omega)]
  rw [or_mul_pow_two_eq_add _ _ 24 (by
    have := (input.val[i.val]!).hmax; have := (input.val[i.val + 1]!).hmax
    have := (input.val[i.val + 2]!).hmax; norm_num at *; omega)]
  rw [or_mul_pow_two_eq_add _ _ 32 (by
    have := (input.val[i.val]!).hmax; have := (input.val[i.val + 1]!).hmax
    have := (input.val[i.val + 2]!).hmax; have := (input.val[i.val + 3]!).hmax
    norm_num at *; omega)]
  rw [or_mul_pow_two_eq_add _ _ 40 (by
    have := (input.val[i.val]!).hmax; have := (input.val[i.val + 1]!).hmax
    have := (input.val[i.val + 2]!).hmax; have := (input.val[i.val + 3]!).hmax
    have := (input.val[i.val + 4]!).hmax; norm_num at *; omega)]
  rw [or_mul_pow_two_eq_add _ _ 48 (by
    have := (input.val[i.val]!).hmax; have := (input.val[i.val + 1]!).hmax
    have := (input.val[i.val + 2]!).hmax; have := (input.val[i.val + 3]!).hmax
    have := (input.val[i.val + 4]!).hmax; have := (input.val[i.val + 5]!).hmax
    norm_num at *; omega)]
  rw [or_mul_pow_two_eq_add _ _ 56 (by
    have := (input.val[i.val]!).hmax; have := (input.val[i.val + 1]!).hmax
    have := (input.val[i.val + 2]!).hmax; have := (input.val[i.val + 3]!).hmax
    have := (input.val[i.val + 4]!).hmax; have := (input.val[i.val + 5]!).hmax
    have := (input.val[i.val + 6]!).hmax; norm_num at *; omega)]
  simp [Finset.sum_range_succ]

private lemma extract_getElem! (l : List U8) (i j : Nat) (hj : j < 8) :
    (l.extract i (i + 8))[j]! = l[i + j]! := by grind

private lemma sum_extract_eq (l : List U8) (i : Nat) (hi : i + 8 ≤ l.length) :
    ∑ j ∈ Finset.range 8, l[i + j]!.val * 2 ^ (8 * j) =
      Nat.ofDigits 256 ((l.extract i (i + 8)).map (·.val)) := by
  have hlen : (l.extract i (i + 8)).length = 8 := by
    simp [List.extract_eq_drop_take, List.length_take, List.length_drop]; omega
  rw [ofDigits_map_val_eq_sum, hlen]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [extract_getElem! l i j hj]
  rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]

/-- The List Bool spec for load8_at: the result's bits are exactly
    the 64 bits starting at byte position i in the input. -/
@[progress]
theorem load8_at_bitList_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      ofU64 result =
        (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64) ⦄ := by
  apply spec_mono (load8_at_val_spec input i h)
  intro result hval
  set rhs := (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64)
  have hlen : rhs.length = 64 := by
    simp [rhs, List.extract_eq_drop_take, List.length_take, List.length_drop, ofByteList_length]
    omega
  have hval_eq : result.val = toNat rhs := by
    have hval' : result.val = ∑ j ∈ Finset.range 8,
        input.val[i.val + j]!.val * 2 ^ (8 * j) := by
      simp only [Slice.getElem!_Nat_eq] at hval; exact hval
    rw [hval']
    simp only [rhs]
    rw [show 8 * i.val + 64 = 8 * (i.val + 8) from by ring]
    rw [ofByteList_extract input.val i.val (i.val + 8) (by omega)]
    rw [toNat_ofByteList]
    rw [sum_extract_eq input.val i.val (by omega)]
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
  exact ofNat_equiv_of_lt (64 - k.toNat) 64 (x.val / 2 ^ k.toNat)
    (by omega) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc x.val < 2 ^ 64 := x.hmax
        _ = 2 ^ (64 - k.toNat) * 2 ^ k.toNat := by
          rw [← Nat.pow_add]; congr 1; omega)

/-- Masking a U64 with `2^n - 1` takes the first n bits. -/
@[progress]
theorem u64_and_mask_bitList_spec (x mask : U64) (n : Nat)
    (hn : n ≤ 64) (hmask : mask.val = 2 ^ n - 1) :
    lift (x &&& mask) ⦃ z => ofU64 z ≈ₗ (ofU64 x).take n ⦄ := by
  simp only [lift, spec_ok]
  have hval : (x &&& mask).val = x.val % 2 ^ n := by
    rw [UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod]
  simp only [ofU64, hval]
  rw [ofNat_take n 64 x.val (by omega), ← ofNat_mod n x.val]
  exact ofNat_equiv_of_lt n 64 (x.val % 2 ^ n) (by omega)
    (Nat.mod_lt _ (by positivity))

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
theorem field51_eq_of_bitList
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    Field51_as_Nat result = U8x32_as_Nat bytes % 2 ^ 255 := by
  have hlimb : ∀ (i : Nat) (hi : i < 5),
      result[i]!.val = toNat ((ofByteArray bytes).extract (51 * i) (51 * i + 51)) := by
    intro i hi
    rw [← toNat_ofU64 result[i]!]
    exact (hequiv ⟨i, hi⟩).toNat_eq
  unfold Field51_as_Nat
  have hsum : ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * result[i]!.val =
      ∑ i ∈ Finset.range 5,
        toNat ((ofByteArray bytes).extract (51 * i) (51 * i + 51)) * 2 ^ (51 * i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hlimb i hi]; ring
  rw [hsum, ← toNat_split_chunks (ofByteArray bytes) 51 5 (by rw [ofByteArray_length]; norm_num),
    show 51 * 5 = 255 from by norm_num]
  rw [toNat_take 255 (ofByteArray bytes), toNat_ofByteArray]

/-- The limb bound follows from Equiv (the extract has length ≤ 51). -/
theorem limb_bound_of_equiv
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    ∀ i : Fin 5, result[i]!.val < 2 ^ 51 := by
  intro i
  rw [← toNat_ofU64 result[i]!, (hequiv i).toNat_eq]
  exact (toNat_lt_pow _).trans_le (Nat.pow_le_pow_right (by omega) (by
    simp [List.extract_eq_drop_take, List.length_take, List.length_drop, ofByteArray_length]))

/-! ## The pure List Bool specification for from_bytes -/

/-- The pure List Bool spec for from_bytes, using `BitList.Equiv` (≈ₗ). -/
@[progress]
theorem from_bytes_bitList_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      let allBits := ofByteArray bytes
      ∀ i : Fin 5,
        ofU64 result[i]! ≈ₗ allBits.extract (51 * i.val) (51 * i.val + 51) ⦄ := by
  unfold from_bytes
  progress as ⟨i_shl, hi_shl1, _⟩
  progress as ⟨low_51_bit_mask, hmask_val, _⟩
  have hmask51 : low_51_bit_mask.val = 2 ^ 51 - 1 := by
    rw [hmask_val, hi_shl1]; scalar_tac
  progress*
  have hs_val : ∀ (sx : Slice U8), sx = bytes.to_slice → (ofByteList sx.val) = ofByteList bytes.val := by
    intro sx hsx; rw [hsx]; simp [Array.to_slice]
  intro i; fin_cases i <;> simp only [Array.make, ofByteArray]
  · have h1 := i1_post; rw [hs_val s s_post] at h1
    exact i2_post.trans (h1.take 51 |>.trans (by
      simp only [List.extract_eq_drop_take, List.take_take]
      intro i; rfl))
  · have h3 := i3_post; rw [hs_val s1 s1_post] at h3
    exact i5_post.trans ((i4_post.take 51).trans ((h3.drop 3 |>.take 51).trans (by
      simp only [Nat.reduceMul, Nat.reduceAdd, List.extract_eq_drop_take, Nat.reduceSub,
        List.drop_take, List.drop_drop, List.take_take, Nat.reduceLeDiff, inf_of_le_left]
      intro i; rfl)))
  · have h6 := i6_post; rw [hs_val s2 s2_post] at h6
    exact i8_post.trans ((i7_post.take 51).trans ((h6.drop 6 |>.take 51).trans (by
      simp only [Nat.reduceMul, Nat.reduceAdd, List.extract_eq_drop_take, Nat.reduceSub,
        List.drop_take, List.drop_drop, List.take_take, Nat.reduceLeDiff, inf_of_le_left]
      intro i; rfl)))
  · have h9 := i9_post; rw [hs_val s3 s3_post] at h9
    exact i11_post.trans ((i10_post.take 51).trans ((h9.drop 1 |>.take 51).trans (by
      simp only [Nat.reduceMul, Nat.reduceAdd, List.extract_eq_drop_take, Nat.reduceSub,
        List.drop_take, List.drop_drop, List.take_take, Nat.reduceLeDiff, inf_of_le_left]
      intro i; rfl)))
  · have h12 := i12_post; rw [hs_val s4 s4_post] at h12
    exact i14_post.trans ((i13_post.take 51).trans ((h12.drop 12 |>.take 51).trans (by
      simp only [Nat.reduceMul, Nat.reduceAdd, List.extract_eq_drop_take, Nat.reduceSub,
        List.drop_take, List.drop_drop, List.take_take, Nat.reduceLeDiff, inf_of_le_left]
      intro i; rfl)))

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

end curve25519_dalek.backend.serial.u64.field.FieldElement51
