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
set_option linter.style.induction false

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

/-- The Nat-level spec for load8_at: the result is the little-endian
    combination of 8 consecutive bytes. -/
@[progress]
theorem load8_at_val_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      result.val = ∑ j ∈ Finset.range 8,
        input[i.val + j]!.val * 2 ^ (8 * j) ⦄ := by
  sorry
  -- Unfold load8_at. It computes:
  --   input[i] | (input[i+1] << 8) | ... | (input[i+7] << 56)
  --
  -- By Aeneas specs:
  --   U8.cast_U64_val_eq: cast to U64 preserves value
  --   U64.ShiftLeft_spec: (x <<< k).val = x.val * 2^k (when no overflow)
  --   UScalar.val_or: (x ||| y).val = x.val ||| y.val
  --
  -- OR on disjoint bit ranges equals addition:
  --   Each byte occupies a disjoint 8-bit range [8j, 8j+8).
  --   result.val = ∑ j, input[i+j].val * 2^(8*j). ✓

/-- The List Bool spec for load8_at: the result's bits are exactly
    the 64 bits starting at byte position i in the input. -/
@[progress]
theorem load8_at_bitList_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      ofU64 result =
        (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64) ⦄ := by
  unfold from_bytes.load8_at
  progress*
  -- Goal: ofU64 (i32 ||| i36) = (ofByteList input.val).extract (8*i.val) (8*i.val + 64)
  -- Strategy: show toNat equality, then use round-trip.
  -- Both sides have length 64 when converted to List Bool.
  -- Suffices to show their toNat values are equal.
  -- Strategy: show both sides equal when converted to Nat, then use round-trip
  set rhs := (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64)
  have hlen : rhs.length = 64 := by
    simp [rhs, List.extract_eq_drop_take, List.length_take, List.length_drop, ofByteList_length]
    omega
  suffices hval : (i32 ||| i36).val = toNat rhs by
    simp only [ofU64]
    conv_rhs => rw [← ofNat_toNat rhs, hlen]
    rw [hval]
  -- Express RHS via ofByteList_extract and toNat_ofByteList
  have hrhs : toNat rhs =
      toNat (ofByteList (input.val.extract i.val (i.val + 8))) := by
    simp only [rhs]
    rw [show 8 * i.val + 64 = 8 * (i.val + 8) from by ring]
    rw [ofByteList_extract input.val i.val (i.val + 8) (by omega)]
  rw [hrhs, toNat_ofByteList]
  -- Goal: (i32 ||| i36).val = Nat.ofDigits 256 ((input.val.extract i.val (i.val+8)).map (·.val))
  -- Simplify LHS: expand OR chain using val_or and shift specs
  -- Each byte occupies a disjoint 8-bit range, so OR = addition
  simp only [UScalar.val_or]
  -- Expand the bytes
  set b0 := input.val[i.val]!
  set b1 := input.val[i.val + 1]!
  set b2 := input.val[i.val + 2]!
  set b3 := input.val[i.val + 3]!
  set b4 := input.val[i.val + 4]!
  set b5 := input.val[i.val + 5]!
  set b6 := input.val[i.val + 6]!
  set b7 := input.val[i.val + 7]!
  -- Rewrite all the post conditions
  simp only [i1_post, i2_post, i4_post, i5_post, i9_post, i10_post, i14_post, i15_post,
    i19_post, i20_post, i24_post, i25_post, i29_post, i30_post, i34_post, i35_post] at *
  simp only [i3_post, i8_post, i13_post, i18_post, i23_post, i28_post, i33_post] at *
  -- Now use bvify to convert to bitvector
  bvify 64 at *
  bv_decide
  all_goals sorry
  -- From load8_at_val_spec:
  --   result.val = ∑ j, input[i+j].val * 2^(8*j)
  --             = toNat (ofByteList (input.val.extract i.val (i.val + 8)))
  --
  -- By ofNat_toNat round-trip (since the byte sublist has 64 bits):
  --   ofU64 result = ofByteList (input.val.extract i.val (i.val + 8))
  --   = (ofByteList input.val).extract (8*i.val) (8*i.val + 64)  [ofByteList_extract]

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
  rw [hval, Nat.shiftRight_eq_div_pow]
  -- Goal: ofNat 64 (x.val / 2^k.toNat) ≈ₗ (ofNat 64 x.val).drop k.toNat
  -- RHS = ofNat (64 - k.toNat) (x.val / 2^k.toNat) by ofNat_drop
  rw [ofNat_drop k.toNat 64 x.val (by omega)]
  -- Goal: ofNat 64 (x.val / 2^k.toNat) ≈ₗ ofNat (64 - k.toNat) (x.val / 2^k.toNat)
  exact ofNat_equiv_of_lt (64 - k.toNat) 64 (x.val / 2 ^ k.toNat)
    (by omega) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc x.val < 2 ^ 64 := x.hmax
        _ = 2 ^ (64 - k.toNat) * 2 ^ k.toNat := by
          rw [← Nat.pow_add]; congr 1; omega)
  -- By U64.ShiftRight_IScalar_spec: z.val = x.val >>> k.toNat = x.val / 2^k.toNat.
  -- ofU64 z = ofNat 64 (x.val / 2^k.toNat)
  -- (ofU64 x).drop k.toNat = (ofNat 64 x.val).drop k.toNat
  --   = ofNat (64 - k.toNat) (x.val / 2^k.toNat)   [ofNat_drop]
  -- By ofNat_equiv_of_lt (since x.val / 2^k.toNat < 2^(64 - k.toNat)):
  --   ofNat 64 (x.val / 2^k.toNat) ≈ₗ ofNat (64 - k.toNat) (x.val / 2^k.toNat). ✓

/-- Masking a U64 with `2^n - 1` takes the first n bits. -/
@[progress]
theorem u64_and_mask_bitList_spec (x mask : U64) (n : Nat)
    (hn : n ≤ 64) (hmask : mask.val = 2 ^ n - 1) :
    lift (x &&& mask) ⦃ z => ofU64 z ≈ₗ (ofU64 x).take n ⦄ := by
  simp only [lift, spec_ok]
  -- Goal: ofU64 (x &&& mask) ≈ₗ (ofU64 x).take n
  have hval : (x &&& mask).val = x.val % 2 ^ n := by
    rw [UScalar.val_and, hmask, land_pow_two_sub_one_eq_mod]
  simp only [ofU64, hval]
  -- Goal: ofNat 64 (x.val % 2^n) ≈ₗ (ofNat 64 x.val).take n
  rw [ofNat_take n 64 x.val (by omega)]
  -- Goal: ofNat 64 (x.val % 2^n) ≈ₗ ofNat n x.val
  rw [← ofNat_mod n x.val]
  exact ofNat_equiv_of_lt n 64 (x.val % 2 ^ n) (by omega)
    (Nat.mod_lt _ (by positivity))
  -- By UScalar.val_and: (x &&& mask).val = x.val &&& mask.val = x.val &&& (2^n - 1).
  -- By land_pow_two_sub_one_eq_mod: x.val &&& (2^n - 1) = x.val % 2^n.
  -- ofU64 (x &&& mask) = ofNat 64 (x.val % 2^n)
  --   ≈ₗ ofNat n (x.val % 2^n)           [ofNat_equiv_of_lt, val < 2^n]
  --   = ofNat n x.val                      [ofNat_mod]
  --   = (ofNat 64 x.val).take n            [ofNat_take]
  --   = (ofU64 x).take n. ✓

/-- load8_at in List Bool terms, as a progress-compatible spec. -/
@[progress]
theorem load8_at_bitList_progress_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      ofU64 result ≈ₗ
        (ofByteList input.val).extract (8 * i.val) (8 * i.val + 64) ⦄ := by
  exact spec_mono (load8_at_bitList_spec input i h) fun result heq => heq ▸ BitList.Equiv.refl _
  -- By load8_at_bitList_spec (which gives equality, not just ≈ₗ).
  -- Equality implies Equiv. ✓

/-! ## Bridge: List Bool spec implies Nat spec -/

/-- Equiv implies the limb value equals the slice value. -/
theorem field51_eq_of_bitList
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    Field51_as_Nat result = U8x32_as_Nat bytes % 2 ^ 255 := by
  -- Step 1: Rewrite each limb value using Equiv
  have hlimb : ∀ (i : Nat) (hi : i < 5),
      result[i]!.val = toNat ((ofByteArray bytes).extract (51 * i) (51 * i + 51)) := by
    intro i hi
    rw [← toNat_ofU64 result[i]!]
    exact (hequiv ⟨i, hi⟩).toNat_eq
  -- Step 2: Rewrite Field51_as_Nat using Finset.sum_congr
  unfold Field51_as_Nat
  have hsum : ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * result[i]!.val =
      ∑ i ∈ Finset.range 5,
        toNat ((ofByteArray bytes).extract (51 * i) (51 * i + 51)) * 2 ^ (51 * i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hlimb i hi]; ring
  rw [hsum]
  -- Step 3: Apply toNat_split_chunks
  rw [← toNat_split_chunks (ofByteArray bytes) 51 5 (by rw [ofByteArray_length]; norm_num)]
  -- Step 4: Apply toNat_take and toNat_ofByteArray
  rw [show 51 * 5 = 255 from by norm_num]
  rw [toNat_take 255 (ofByteArray bytes)]
  rw [toNat_ofByteArray]
  -- For each i:
  --   result[i].val = toNat (ofU64 result[i])                  [toNat_ofU64]
  --                 = toNat (allBits.extract (51*i) (51*i+51)) [Equiv.toNat_eq]
  -- Field51_as_Nat = ∑ i, result[i].val * 2^(51*i)
  --   = ∑ i, toNat (allBits.extract (51*i) (51*i+51)) * 2^(51*i)
  --   = toNat (allBits.take 255)                [toNat_split_chunks, k=51, n=5]
  --   = toNat (ofByteArray bytes) % 2^255       [toNat_take]
  --   = U8x32_as_Nat bytes % 2^255              [toNat_ofByteArray]

/-- The limb bound follows from Equiv (the extract has length ≤ 51). -/
theorem limb_bound_of_equiv
    (result : FieldElement51) (bytes : Array U8 32#usize)
    (hequiv : ∀ i : Fin 5,
      ofU64 result[i]! ≈ₗ
        (ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)) :
    ∀ i : Fin 5, result[i]!.val < 2 ^ 51 := by
  intro i
  have hequiv_i := hequiv i
  rw [← toNat_ofU64 result[i]!]
  rw [hequiv_i.toNat_eq]
  calc toNat ((ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51))
      < 2 ^ ((ofByteArray bytes).extract (51 * i.val) (51 * i.val + 51)).length :=
        toNat_lt_pow _
    _ ≤ 2 ^ 51 := by
        apply Nat.pow_le_pow_right (by omega)
        simp [List.extract_eq_drop_take, List.length_take, List.length_drop, ofByteArray_length]
  -- result[i].val = toNat (ofU64 result[i])    [toNat_ofU64]
  --              = toNat (extract ...)           [Equiv.toNat_eq]
  -- extract has length ≤ 51, so toNat < 2^51   [toNat_lt_pow]. ✓

/-! ## The pure List Bool specification for from_bytes -/

/-- The pure List Bool spec for from_bytes, using `BitList.Equiv` (≈ₗ). -/
@[progress]
theorem from_bytes_bitList_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      let allBits := ofByteArray bytes
      ∀ i : Fin 5,
        ofU64 result[i]! ≈ₗ allBits.extract (51 * i.val) (51 * i.val + 51) ⦄ := by
  unfold from_bytes
  /-
  ⊢ (do
    let i ← 1#u64 <<< 51#i32
    let low_51_bit_mask ← i - 1#u64
    let s ← lift bytes.to_slice
    let i1 ← from_bytes.load8_at s 0#usize
    let i2 ← lift (i1 &&& low_51_bit_mask)
    let s1 ← lift bytes.to_slice
    let i3 ← from_bytes.load8_at s1 6#usize
    let i4 ← i3 >>> 3#i32
    let i5 ← lift (i4 &&& low_51_bit_mask)
    let s2 ← lift bytes.to_slice
    let i6 ← from_bytes.load8_at s2 12#usize
    let i7 ← i6 >>> 6#i32
    let i8 ← lift (i7 &&& low_51_bit_mask)
    let s3 ← lift bytes.to_slice
    let i9 ← from_bytes.load8_at s3 19#usize
    let i10 ← i9 >>> 1#i32
    let i11 ← lift (i10 &&& low_51_bit_mask)
    let s4 ← lift bytes.to_slice
    let i12 ← from_bytes.load8_at s4 24#usize
    let i13 ← i12 >>> 12#i32
    let i14 ← lift (i13 &&& low_51_bit_mask)
    ok (Array.make 5#usize [i2, i5, i8, i11, i14] ⋯)) ⦃
  result =>
  let allBits := ofByteArray bytes;
  ∀ (i : Fin 5), ofU64 result[i]! ≈ₗ allBits.extract (51 * ↑i) (51 * ↑i + 51) ⦄
  -/
  -- Step through the mask computation
  progress as ⟨i_shl, hi_shl1, _⟩   -- 1 <<< 51
  progress as ⟨low_51_bit_mask, hmask_val, _⟩  -- i - 1
  have hmask51 : low_51_bit_mask.val = 2 ^ 51 - 1 := by
    rw [hmask_val, hi_shl1]; scalar_tac
  -- Use progress* now that hmask51 is in scope
  progress*
  -- Remaining: prove ∀ i : Fin 5, ofU64 result[i]! ≈ₗ ...
  -- The result is Array.make 5 [i2, i5, i8, i11, i14].
  -- Each ix has a chain of ≈ₗ hypotheses from progress*.
  -- We need to compose them and simplify.
  -- Helper: compose Equiv chain for each limb
  -- All slices s, s1, ... have the same val as bytes.val
  -- The goal uses ofByteArray bytes = ofByteList bytes.val
  -- Each slice has val = bytes.val
  have hs_val : ∀ (sx : Slice U8), sx = bytes.to_slice → (ofByteList sx.val) = ofByteList bytes.val := by
    intro sx hsx; rw [hsx]; simp [Array.to_slice]
  intro i; fin_cases i <;> simp only [Array.make, ofByteArray]
  -- Case 0: ofU64 i2 ≈ₗ (ofByteList bytes.val).extract 0 51
  -- i2 ≈ₗ take 51 (ofU64 i1), i1 ≈ₗ extract 0 64 of ofByteList s.val
  · have h1 := i1_post; rw [hs_val s s_post] at h1
    exact i2_post.trans (h1.take 51 |>.trans (by
      simp [List.extract_eq_drop_take, List.take_take]; exact BitList.Equiv.refl _))
  -- Case 1: ofU64 i5 ≈ₗ (ofByteList bytes.val).extract 51 102
  · have h3 := i3_post; rw [hs_val s1 s1_post] at h3
    exact i5_post.trans ((i4_post.take 51).trans ((h3.drop 3 |>.take 51).trans (by
      simp [List.extract_eq_drop_take, List.drop_drop, List.drop_take, List.take_take]
      exact BitList.Equiv.refl _)))
  -- Case 2: ofU64 i8 ≈ₗ (ofByteList bytes.val).extract 102 153
  · have h6 := i6_post; rw [hs_val s2 s2_post] at h6
    exact i8_post.trans ((i7_post.take 51).trans ((h6.drop 6 |>.take 51).trans (by
      simp [List.extract_eq_drop_take, List.drop_drop, List.drop_take, List.take_take]
      exact BitList.Equiv.refl _)))
  -- Case 3: ofU64 i11 ≈ₗ (ofByteList bytes.val).extract 153 204
  · have h9 := i9_post; rw [hs_val s3 s3_post] at h9
    exact i11_post.trans ((i10_post.take 51).trans ((h9.drop 1 |>.take 51).trans (by
      simp [List.extract_eq_drop_take, List.drop_drop, List.drop_take, List.take_take]
      exact BitList.Equiv.refl _)))
  -- Case 4: ofU64 i14 ≈ₗ (ofByteList bytes.val).extract 204 255
  · have h12 := i12_post; rw [hs_val s4 s4_post] at h12
    exact i14_post.trans ((i13_post.take 51).trans ((h12.drop 12 |>.take 51).trans (by
      simp [List.extract_eq_drop_take, List.drop_drop, List.drop_take, List.take_take]
      exact BitList.Equiv.refl _)))
  -- Unfold from_bytes. For each limb i with byte offset j and shift k:
  --   result[i] = (load8_at(bytes.to_slice, j) >>> k) &&& low_51_bit_mask
  --
  -- Step 1 (load8_at): By load8_at_bitList_spec,
  --   ofU64 (load8_at s j) = (ofByteList s.val).extract (8*j) (8*j + 64)
  --   Since s = bytes.to_slice, s.val = bytes.val (by Array.val_to_slice),
  --   = (ofByteArray bytes).extract (8*j) (8*j + 64)
  --
  -- Step 2 (shift + mask at Nat level):
  --   U64.ShiftRight_spec: (x >>> k).val = x.val >>> k.val
  --   UScalar.val_and: (x &&& y).val = x.val &&& y.val
  --   Nat.shiftRight_eq: n >>> k = n / 2^k
  --   land_pow_two_sub_one_eq_mod: n &&& (2^51-1) = n % 2^51
  --   Combined: result[i].val = (load8_at_val / 2^k) % 2^51
  --
  -- Step 3 (convert to List Bool):
  --   ofU64 result[i] = ofNat 64 ((load8_at_val / 2^k) % 2^51)
  --   ≈ₗ ofNat 51 ((load8_at_val / 2^k) % 2^51)   [ofNat_equiv_of_lt, val < 2^51]
  --   = ofNat 51 (load8_at_val / 2^k)               [ofNat_mod]
  --   = (ofNat 64 load8_at_val).extract k (k+51)    [ofNat_extract]
  --   = allBits.extract (8*j) (8*j+64) |>.extract k (k+51)  [load8_at result]
  --   = allBits.extract (8*j+k) (8*j+k+51)          [extract_extract]
  --
  -- Step 4 (check 8*j + k = 51*i for each limb):
  --   i=0: j=0,  k=0  → 0   = 51*0  ✓
  --   i=1: j=6,  k=3  → 51  = 51*1  ✓
  --   i=2: j=12, k=6  → 102 = 51*2  ✓
  --   i=3: j=19, k=1  → 153 = 51*3  ✓
  --   i=4: j=24, k=12 → 204 = 51*4  ✓

/-! ## Final spec -/

@[progress, externally_verified]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  progress as ⟨result, hresult⟩
  have heq := field51_eq_of_bitList result bytes hresult
  have hbound := limb_bound_of_equiv result bytes hresult
  refine ⟨?_, fun i hi => hbound ⟨i, hi⟩⟩
  show Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p]
  rw [heq]


end curve25519_dalek.backend.serial.u64.field.FieldElement51
