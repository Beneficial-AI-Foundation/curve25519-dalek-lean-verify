/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.BitList
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorem for `Scalar52::to_bytes`

Specification and proof for `Scalar52::to_bytes`.

This function converts the structure to its byte representation.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## Rust Source

```rust
/// Pack the limbs of this `Scalar52` into 32 bytes
pub fn to_bytes(self) -> [u8; 32] {
    let mut s = [0u8; 32];

    s[ 0] = (self.0[ 0] >> 0) as u8;
    s[ 1] = (self.0[ 0] >> 8) as u8;
    s[ 2] = (self.0[ 0] >> 16) as u8;
    s[ 3] = (self.0[ 0] >> 24) as u8;
    s[ 4] = (self.0[ 0] >> 32) as u8;
    s[ 5] = (self.0[ 0] >> 40) as u8;
    s[ 6] = ((self.0[ 0] >> 48) | (self.0[ 1] << 4)) as u8;
    s[ 7] = (self.0[ 1] >> 4) as u8;
    s[ 8] = (self.0[ 1] >> 12) as u8;
    s[ 9] = (self.0[ 1] >> 20) as u8;
    s[10] = (self.0[ 1] >> 28) as u8;
    s[11] = (self.0[ 1] >> 36) as u8;
    s[12] = (self.0[ 1] >> 44) as u8;
    s[13] = (self.0[ 2] >> 0) as u8;
    s[14] = (self.0[ 2] >> 8) as u8;
    s[15] = (self.0[ 2] >> 16) as u8;
    s[16] = (self.0[ 2] >> 24) as u8;
    s[17] = (self.0[ 2] >> 32) as u8;
    s[18] = (self.0[ 2] >> 40) as u8;
    s[19] = ((self.0[ 2] >> 48) | (self.0[ 3] << 4)) as u8;
    s[20] = (self.0[ 3] >> 4) as u8;
    s[21] = (self.0[ 3] >> 12) as u8;
    s[22] = (self.0[ 3] >> 20) as u8;
    s[23] = (self.0[ 3] >> 28) as u8;
    s[24] = (self.0[ 3] >> 36) as u8;
    s[25] = (self.0[ 3] >> 44) as u8;
    s[26] = (self.0[ 4] >> 0) as u8;
    s[27] = (self.0[ 4] >> 8) as u8;
    s[28] = (self.0[ 4] >> 16) as u8;
    s[29] = (self.0[ 4] >> 24) as u8;
    s[30] = (self.0[ 4] >> 32) as u8;
    s[31] = (self.0[ 4] >> 40) as u8;

    s
}
```

## Bit layout

Each limb holds 52 bits. Since 52 = 6×8 + 4, each limb fills 6 full bytes plus 4 bits that
spill into a shared byte with the adjacent limb. The two shared bytes are s[6] and s[19],
constructed via OR of the overflow bits from one limb and the start bits of the next.

  | Limb | Bits | Bytes                              | Shared |
  |------|------|------------------------------------|--------|
  |  0   | 0–51 | s[0]–s[5], lower nibble of s[6]    | s[6]   |
  |  1   | 0–51 | upper nibble of s[6], s[7]–s[12]   | s[6]   |
  |  2   | 0–51 | s[13]–s[18], lower nibble of s[19] | s[19]  |
  |  3   | 0–51 | upper nibble of s[19], s[20]–s[25] | s[19]  |
  |  4   | 0–47 | s[26]–s[31] (48 bits)              | none   |

Limb 4 uses only 48 of its 52 bits because the precondition `Scalar52_as_Nat self < L < 2^253`
implies `self[4] < 2^(253−208) = 2^45 < 2^48`.

Total: limbs hold 5×52 = 260 bits, but the value fits in 32×8 = 256 bits.

## Proof overview

We express each of the 32 byte assignments as a `BitList.extract` equality, use
`List.extract_append_extract` to merge adjacent extracts into limb-level equivalences,
then convert to `Nat` via `toNat` and close with `grind`.
-/

set_option linter.style.setOption false
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52
open List BitList

/-
natural language description:

    • Takes an unpacked scalar u (five 52-bit limbs stored in U64 values) and
      returns a 32-byte array b that represents the same 256-bit integer value modulo L
      in little-endian byte representation.

natural language specs:

    • u8x32_to_nat(b) ≡ scalar_to_nat(u) (mod L)
-/

/-- The limb bound follows from Equiv. -/
theorem as_nat_bound_of_equiv (self : Scalar52) (result : Array U8 32#usize)
    (h : ∀ i : Fin 4,
      ofU64 self[i]! ≈ₗ (ofByteArray result).extract (52 * i.val) (52 * i.val + 52))
    (h' : (ofU64 self[4]).extract 0 48 ≈ₗ (ofByteArray result).extract 208 256)
    (hbound : Scalar52_as_Nat self < L) :
    U8x32_as_Nat result < L := by
    sorry

/-- Equiv implies the limb value equals the slice value. -/
theorem scalar52_eq_of_bitList (self : Scalar52) (result : Array U8 32#usize)
    (h : ∀ i : Fin 4,
      ofU64 self[i]! ≈ₗ (ofByteArray result).extract (52 * i.val) (52 * i.val + 52))
    (h' : (ofU64 self[4]).extract 0 48 ≈ₗ (ofByteArray result).extract 208 256)
    (hbound : Scalar52_as_Nat self < L) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
    sorry

/-- The pure List Bool spec for to_bytes, using `BitList.Equiv` (≈ₗ). -/
@[progress]
theorem to_bytes_bitList_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Array U8 32#usize) =>
      (∀ i : Fin 4,
        ofU64 self[i]! ≈ₗ (ofByteArray result).extract (52 * i.val) (52 * i.val + 52)) ∧
        (ofU64 self[4]).extract 0 48 ≈ₗ (ofByteArray result).extract 208 256 ⦄ := by
    sorry

/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
@[externally_verified, progress] -- proven in Verus
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧
      U8x32_as_Nat result < L ⦄ := by
    progress*
    constructor
    · -- To prove U8x32_as_Nat result = Scalar52_as_Nat self
      rw [scalar52_eq_of_bitList self result _]; repeat assumption
    · -- To prove U8x32_as_Nat result < L
      apply as_nat_bound_of_equiv self result _ _ _; repeat assumption

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
