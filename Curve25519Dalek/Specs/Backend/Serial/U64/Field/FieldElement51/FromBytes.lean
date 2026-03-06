/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Math.BitList
import Curve25519Dalek.Funs
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
  sorry
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
  sorry
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
  sorry
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
  sorry
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
  sorry
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
  sorry
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
  sorry
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
  sorry
  -- Once all sorry's are filled in, the proof is:
  --   progress hresult with from_bytes_bitList_spec
  --   constructor
  --   · constructor
  --     exact field51_eq_of_bitList result bytes hresult
  --   · have hbound := limb_bound_of_equiv result bytes hresult
  --     intro i hi
  --     exact hbound ⟨i, hi⟩


end curve25519_dalek.backend.serial.u64.field.FieldElement51
