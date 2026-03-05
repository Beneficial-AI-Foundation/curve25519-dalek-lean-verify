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

/- **Updated plan:**

- Define functions which map from `Slice U8` and `U64` to `List bool`
- Write a spec for `from_bytes.load8_at` using this
- Prove this spec
- Define functions connecting List bool to Nat
- Write similar specs for `>>>` and bit masking

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
        // load bits [  0, 64), no shift
        [  load8_at(bytes,  0)        & low_51_bit_mask
        // load bits [ 48,112), shift to [ 51,112)
        , (load8_at(bytes,  6) >>  3) & low_51_bit_mask
        // load bits [ 96,160), shift to [102,160)
        , (load8_at(bytes, 12) >>  6) & low_51_bit_mask
        // load bits [152,216), shift to [153,216)
        , (load8_at(bytes, 19) >>  1) & low_51_bit_mask
        // load bits [192,256), shift to [204,112)
        , (load8_at(bytes, 24) >> 12) & low_51_bit_mask
        ])
    }
```

-/

/-! ## Bit-level representations -/

end curve25519_dalek.backend.serial.u64.field.FieldElement51

/-- The bit representation of a natural number as a list of booleans (LSB first),
    truncated/padded to `len` bits. -/
def Nat.toBits (n : Nat) (len : Nat) : List Bool :=
  (List.range len).map n.testBit

namespace Aeneas.Std

/-- The bits of a `UScalar` value (LSB first), with length determined by the scalar type. -/
def UScalar.toBits {ty : UScalarTy} (x : UScalar ty) : List Bool :=
  x.val.toBits ty.numBits

/-- The bits of a scalar slice, formed by concatenating each element's bits in order. -/
def Slice.toBits {ty : UScalarTy} (s : Slice (UScalar ty)) : List Bool :=
  s.val.flatMap UScalar.toBits

end Aeneas.Std

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51
open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! ## Spec for `load8_at` -/

/-- Spec for `backend.serial.u64.field.FieldElement51.from_bytes.load8_at`.
Loads 8 bytes from a slice starting at index `i` and interprets them as a little-endian U64.
The 64 bits of the result are exactly the concatenated bits of `input[i..i+8]`. -/
@[progress]
theorem load8_at_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    from_bytes.load8_at input i ⦃ (result : U64) =>
      result.toBits = input.toBits.extract (i.val * 8) (i.val * 8 + 64) ⦄ := by
  unfold from_bytes.load8_at
  sorry


/-! ## Spec for `from_bytes` -/
/- **Spec for `backend.serial.u64.field.FieldElement51.from_bytes`**:
Constructs a FieldElement51 from the low 255 bits of a 32-byte (256-bit) array.
The function:
1. Loads 8-byte chunks from the input
2. Extracts 51-bit limbs with appropriate shifts and masks
3. The high bit (bit 255) is masked off - only the low 255 bits are used
**Warning**: This function does not check that the input uses the canonical representative.
It masks the high bit, but will decode 2^255 - 18 to 1.
Specification:
- Always succeeds for 32-byte input
- The resulting field element value (mod p) equals the little-endian interpretation
  of the bytes with the high bit (bit 255) cleared
-/


@[progress, externally_verified]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2^51) ∧
      result.IsValid ⦄ := by
  unfold from_bytes
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
