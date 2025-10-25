/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

set_option linter.style.setOption false
set_option maxHeartbeats 1000000

/-! # from_bytes

Specification and proof for `FieldElement51::from_bytes`.

This function constructs a field element from a 32-byte array.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Spec for `load8_at` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.from_bytes.load8_at`**:

Loads 8 bytes from a slice starting at index `i` and interprets them as a little-endian U64.

Specification:
- Requires at least 8 bytes available from index i
- Returns the 64-bit value formed by bytes[i..i+8] in little-endian order
-/
-- @[progress]
theorem load8_at_spec (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    ∃ result, from_bytes.load8_at input i = ok result ∧
    result.val = ∑ j ∈ Finset.range 8, 2^(8*j) * (input.val[i.val + j]!).val := by
  unfold from_bytes.load8_at
  progress*

  sorry

/-- **Bit-level spec for `backend.serial.u64.field.FieldElement51.from_bytes.load8_at`**:

Each bit j of the result corresponds to bit (j mod 8) of byte (j / 8) in the input slice.

Specification phrased in terms of individual bits:
- Bit j of the result equals bit (j mod 8) of input[i + j/8]
- This captures the little-endian byte ordering where lower-indexed bytes contribute to lower bits
-/
@[progress]
theorem load8_at_spec_bitwise (input : Slice U8) (i : Usize)
    (h : i.val + 8 ≤ input.val.length) :
    ∃ result, from_bytes.load8_at input i = ok result ∧
    ∀ j : Nat, j < 64 →
      result.val.testBit j = (input.val[i.val + j / 8]!).val.testBit (j % 8) := by
  unfold from_bytes.load8_at
  progress*
  intro j hj
  simp [*]
  have : j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 ∨ j / 8 = 3 ∨
      j / 8 = 4 ∨ j / 8 = 5 ∨ j / 8 = 6 ∨ j / 8 = 7 := by omega
  obtain hc | hc | hc | hc | hc | hc | hc | hc := this
  · rw [hc]
    have : j < 8 := by omega
    repeat rw [Nat.mod_eq_of_lt]
    simp [Nat.testBit_shiftLeft]
    grind
    grind
    simp only [U64.size, U64.numBits]
    rw [Nat.shiftLeft_eq]



  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry



/-! ## Spec for `from_bytes` -/

/-- **Spec for `backend.serial.u64.field.FieldElement51.from_bytes`**:

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
@[progress]
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    ∃ result, from_bytes bytes = ok result ∧
    U64x5_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] := by
  sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
