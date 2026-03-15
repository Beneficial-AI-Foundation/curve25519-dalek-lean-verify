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

    s[ 0] =  (self.0[ 0] >>  0)                      as u8;
    s[ 1] =  (self.0[ 0] >>  8)                      as u8;
    s[ 2] =  (self.0[ 0] >> 16)                      as u8;
    s[ 3] =  (self.0[ 0] >> 24)                      as u8;
    s[ 4] =  (self.0[ 0] >> 32)                      as u8;
    s[ 5] =  (self.0[ 0] >> 40)                      as u8;
    s[ 6] = ((self.0[ 0] >> 48) | (self.0[ 1] << 4)) as u8;
    s[ 7] =  (self.0[ 1] >>  4)                      as u8;
    s[ 8] =  (self.0[ 1] >> 12)                      as u8;
    s[ 9] =  (self.0[ 1] >> 20)                      as u8;
    s[10] =  (self.0[ 1] >> 28)                      as u8;
    s[11] =  (self.0[ 1] >> 36)                      as u8;
    s[12] =  (self.0[ 1] >> 44)                      as u8;
    s[13] =  (self.0[ 2] >>  0)                      as u8;
    s[14] =  (self.0[ 2] >>  8)                      as u8;
    s[15] =  (self.0[ 2] >> 16)                      as u8;
    s[16] =  (self.0[ 2] >> 24)                      as u8;
    s[17] =  (self.0[ 2] >> 32)                      as u8;
    s[18] =  (self.0[ 2] >> 40)                      as u8;
    s[19] = ((self.0[ 2] >> 48) | (self.0[ 3] << 4)) as u8;
    s[20] =  (self.0[ 3] >>  4)                      as u8;
    s[21] =  (self.0[ 3] >> 12)                      as u8;
    s[22] =  (self.0[ 3] >> 20)                      as u8;
    s[23] =  (self.0[ 3] >> 28)                      as u8;
    s[24] =  (self.0[ 3] >> 36)                      as u8;
    s[25] =  (self.0[ 3] >> 44)                      as u8;
    s[26] =  (self.0[ 4] >>  0)                      as u8;
    s[27] =  (self.0[ 4] >>  8)                      as u8;
    s[28] =  (self.0[ 4] >> 16)                      as u8;
    s[29] =  (self.0[ 4] >> 24)                      as u8;
    s[30] =  (self.0[ 4] >> 32)                      as u8;
    s[31] =  (self.0[ 4] >> 40)                      as u8;

    s
}
```

## Proof Overview

TODO

-/

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



/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- No panic (always returns successfully)
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
@[progress] -- proven in Verus
theorem to_bytes_spec (self : Scalar52) (h : ∀ i : Fin 5, self[i].val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) /- Add : Limbs bounded & u is canonical -/ :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self /- Change to equality, not just [MOD L] -/ ∧
      U8x32_as_Nat result < L ⦄ := by
    unfold to_bytes
    progress*
    have : U8x32_as_Nat result = Scalar52_as_Nat self := by
      sorry
    refine ⟨this, ?_⟩
    rw [this]
    exact h'

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
