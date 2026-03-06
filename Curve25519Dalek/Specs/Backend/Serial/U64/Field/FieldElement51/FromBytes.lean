/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Math.Basic
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

## Why the spec holds

**Value reconstruction:**
  `Field51_as_Nat result = limb0 + limb1 * 2^51 + limb2 * 2^102 + limb3 * 2^153 + limb4 * 2^204`
Since limb `i` is the numeric value of `bits[51i .. 51(i+1))`, multiplying by `2^(51i)`
places those bits back in their original positions. The sum reconstructs exactly
`bits[0..255)` as a number, which equals `U8x32_as_Nat bytes % 2^255`.

**Bound:** Each limb is at most 51 bits wide, so `result[i] < 2^51`.

## Coercions needed

To `List Bool` (all LSB-first):
  - `U8.toBits  : U8  → List Bool`  — 8 bits
  - `U64.toBits : U64 → List Bool`  — 64 bits
  - `Slice U8   → List Bool`        — concatenation of each byte's bits
  - `Array U8 32 → List Bool`       — same, fixed length 256

From `List Bool`:
  - `bitsToNat : List Bool → Nat`   — numeric value: `∑ i, if bs[i] then 2^i else 0`

## Key lemmas

Connecting list operations to arithmetic:
  - `bitsToNat (List.drop k bs) = bitsToNat bs / 2^k`   — right shift is drop
  - `bitsToNat (List.take k bs) = bitsToNat bs % 2^k`   — mask is take
  - `bitsToNat (U64.toBits x) = x.val`
  - `bitsToNat (U8.toBits x) = x.val`

Connecting `load8_at` to list extraction:
  - `U64.toBits (load8_at s i) = (sliceToBits s).extract (8*i) 64`

Length lemmas:
  - `(U8.toBits x).length = 8`
  - `(U64.toBits x).length = 64`
  - `(arrayToBits bytes).length = 256`

The splitting lemma (heart of the proof):
  If `bs` has length ≥ 255, then
  `bitsToNat (bs.take 255) = ∑ i in range 5, bitsToNat (bs.extract (51*i) 51) * 2^(51*i)`

## Plan

1. Define the `toBits` / `bitsToNat` infrastructure (separate file or section).
2. Prove the key lemmas above.
3. Prove `load8_at` spec: extracts a 64-bit sublist starting at bit `8*i`.
4. Prove `from_bytes` spec by composing the lemmas.
-/


@[progress]
theorem load8_at_spec_bitwise (input : Slice U8) (i : Usize) (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ result =>
      True ⦄ := by
  unfold from_bytes.load8_at
  sorry


@[progress, externally_verified]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by
  unfold from_bytes
  sorry


end curve25519_dalek.backend.serial.u64.field.FieldElement51
