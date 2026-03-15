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

## Bit layout

Each limb holds 52 bits. Since 52 = 6×8 + 4, each limb fills 6 full bytes plus 4 bits that
spill into a shared byte with the adjacent limb. The two shared bytes are s[6] and s[19],
constructed via OR of the overflow bits from one limb and the start bits of the next.

  | Limb | Bits  | Bytes                              | Shared |
  |------|-------|------------------------------------|--------|
  |  0   | 0–51  | s[0]–s[5], lower nibble of s[6]    | s[6]   |
  |  1   | 0–51  | upper nibble of s[6], s[7]–s[12]   | s[6]   |
  |  2   | 0–51  | s[13]–s[18], lower nibble of s[19] | s[19]  |
  |  3   | 0–51  | upper nibble of s[19], s[20]–s[25] | s[19]  |
  |  4   | 0–47  | s[26]–s[31] (48 bits)              | none   |

Limb 4 uses only 48 of its 52 bits because the precondition `Scalar52_as_Nat self < L < 2^253`
implies `self[4] < 2^(253−208) = 2^45 < 2^48`.

Total: limbs hold 5×52 = 260 bits, but the value fits in 32×8 = 256 bits.

## Proof overview

We prove 5 results, one for each limb, describing the rows of the above table in terms of `BitList`.


-/

set_option linter.style.setOption false
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52
open List BitList


/-- Interpret a Scalar52 (five u64 limbs used to represent 52 bits each) as a natural number -/
def Scalar52_as_Nat' (limbs : Array U64 5#usize) : Nat :=
  ∑ i : Fin 5, 2^(52 * i.val) * (limbs[i]!).val

-- Note: this is a strengthening of `Scalar52_top_limb_lt_of_as_Nat_lt` in Aux.lean (which gives
-- < 2^51 from < 2^259). This tighter bound should be moved to the central location.
/-- If `Scalar52_as_Nat a < L`, then the top limb `a[4]` is bounded by `2^45`.
This follows because `2^208 * a[4] ≤ Scalar52_as_Nat a < L < 2^253`. -/
theorem Scalar52_top_limb_lt_of_canonical (a : Array U64 5#usize) (h : Scalar52_as_Nat' a < L) :
  a[4].val < 2 ^ 45 := by
  unfold Scalar52_as_Nat' at h
  have : 2 ^ 208 * a[(4 : Fin 5)].val ≤ ∑ (j : Fin 5), 2 ^ (52 * j.val) * a[j].val := by
    have := Finset.single_le_sum (f := fun j : Fin 5 => 2 ^ (52 * j.val) * a[j].val)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ (4 : Fin 5))
    simpa using this
  have : L < 2 ^ 253 := by unfold L; omega
  grind

/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
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
      -- We first prove

      -- As `BitList`, self[0] corresponds to s[0]–s[5] and the lower nibble of s[6]
      --
      sorry
    refine ⟨this, ?_⟩
    rw [this]
    exact h'

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
