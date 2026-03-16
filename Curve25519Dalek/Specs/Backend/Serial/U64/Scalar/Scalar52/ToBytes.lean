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
attribute [local simp] Array.length_eq

-- Note: this is a strengthening of `Scalar52_top_limb_lt_of_as_Nat_lt` in Aux.lean (which gives
-- < 2^51 from < 2^259). This tighter bound should be moved to the central location.
/-- If `Scalar52_as_Nat a < L`, then the top limb `a[4]` is bounded by `2^45`.
This follows because `2^208 * a[4] ≤ Scalar52_as_Nat a < L < 2^253`. -/
theorem Scalar52_top_limb_lt_of_canonical (a : Array U64 5#usize) (h : Scalar52_as_Nat a < L) :
  a[4].val < 2 ^ 45 := by
  unfold Scalar52_as_Nat at h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h
  have : L < 2 ^ 253 := by unfold L; omega
  grind

/-- Two bit lists of the same length with the same `toNat` value are equal. -/
theorem eq_of_toNat_eq_of_length_eq (bs₁ bs₂ : List Bool)
    (h : toNat bs₁ = toNat bs₂) (hl : bs₁.length = bs₂.length) : bs₁ = bs₂ := by
  conv_lhs => rw [← ofNat_toNat bs₁]
  conv_rhs => rw [← ofNat_toNat bs₂]
  rw [hl, h]

/-- Two bit lists of the same length with the same `toNat` value are Equiv. -/
theorem Equiv.of_toNat_eq_of_length_eq (bs₁ bs₂ : List Bool)
    (h : toNat bs₁ = toNat bs₂) (hl : bs₁.length = bs₂.length) : bs₁ ≈ₗ bs₂ := by
  rw [eq_of_toNat_eq_of_length_eq bs₁ bs₂ h hl]

/-- At a shared byte (s[6] or s[19]), the lower and upper nibble contributions recombine:
    `(x % 2^4) * 2^a + (x / 2^4) * 2^(a+4) = x * 2^a`. -/
theorem shared_byte_recombine (x a : Nat) :
    (x % 2 ^ 4) * 2 ^ a + (x / 2 ^ 4) * 2 ^ (a + 4) = x * 2 ^ a := by
  conv_lhs => rw [show (2 : Nat) ^ (a + 4) = 2 ^ 4 * 2 ^ a from by ring]
  have : x / 2 ^ 4 * (2 ^ 4 * 2 ^ a) = x / 2 ^ 4 * 2 ^ 4 * 2 ^ a := by ring
  rw [this, ← Nat.add_mul]
  congr 1; omega

/-- Bridge from 5 BitList limb equivalences to the Nat-level equality
    `U8x32_as_Nat result = Scalar52_as_Nat self`. -/
theorem scalar52_eq_of_bitList_limbs
    (self : Scalar52) (result : Aeneas.Std.Array U8 32#usize)
    (h : ∀ i : Fin 5, self[i].val < 2 ^ 52)
    (h4_bound : self[4].val < 2 ^ 48)
    (hlimb0 : (ofU64 self[0]).take 52 ≈ₗ
        ofU8 result[0]! ++ ofU8 result[1]! ++ ofU8 result[2]! ++
        ofU8 result[3]! ++ ofU8 result[4]! ++ ofU8 result[5]! ++
        (ofU8 result[6]!).take 4)
    (hlimb1 : (ofU64 self[1]).take 52 ≈ₗ
        (ofU8 result[6]!).drop 4 ++
        ofU8 result[7]! ++ ofU8 result[8]! ++ ofU8 result[9]! ++
        ofU8 result[10]! ++ ofU8 result[11]! ++ ofU8 result[12]!)
    (hlimb2 : (ofU64 self[2]).take 52 ≈ₗ
        ofU8 result[13]! ++ ofU8 result[14]! ++ ofU8 result[15]! ++
        ofU8 result[16]! ++ ofU8 result[17]! ++ ofU8 result[18]! ++
        (ofU8 result[19]!).take 4)
    (hlimb3 : (ofU64 self[3]).take 52 ≈ₗ
        (ofU8 result[19]!).drop 4 ++
        ofU8 result[20]! ++ ofU8 result[21]! ++ ofU8 result[22]! ++
        ofU8 result[23]! ++ ofU8 result[24]! ++ ofU8 result[25]!)
    (hlimb4 : (ofU64 self[4]).take 48 ≈ₗ
        ofU8 result[26]! ++ ofU8 result[27]! ++ ofU8 result[28]! ++
        ofU8 result[29]! ++ ofU8 result[30]! ++ ofU8 result[31]!) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
  -- Convert each BitList equivalence to a Nat identity
  have h0 := hlimb0.toNat_eq
  have h1 := hlimb1.toNat_eq
  have h2 := hlimb2.toNat_eq
  have h3 := hlimb3.toNat_eq
  have h4 := hlimb4.toNat_eq
  -- Phase 1: Expand toNat of bit list operations
  simp only [toNat_take, toNat_drop, toNat_append, toNat_ofU8, toNat_ofU64,
    ofU8_length, ofNat_length, length_take, length_drop, length_append,
    Nat.min_def, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceLT, ite_true, ite_false] at h0 h1 h2 h3 h4
  -- Expand both Nat sums
  unfold U8x32_as_Nat Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.reducePow, Nat.reduceMul, one_mul]
  -- Provide limb bounds for omega and recombine shared bytes
  have hb0 : self[0].val < 2 ^ 52 := h ⟨0, by omega⟩
  have hb1 : self[1].val < 2 ^ 52 := h ⟨1, by omega⟩
  have hb2 : self[2].val < 2 ^ 52 := h ⟨2, by omega⟩
  have hb3 : self[3].val < 2 ^ 52 := h ⟨3, by omega⟩
  have hb6 := shared_byte_recombine result[6]!.val 48
  have hb19 := shared_byte_recombine result[19]!.val 152
  -- Normalize all getElem! to getElem so self[i]! (from Scalar52_as_Nat) and
  -- self[i] (from hlimb hypotheses) become the same term.
  -- Aeneas disables List.getElem!_eq_getElem?_getD, so we must apply it explicitly.
  -- We provide explicit length facts so simp can discharge getElem? side conditions.
  have hls : self.val.length = 5 := self.property
  have hlr : result.val.length = 32 := result.property
  simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem, Option.getD_some, hls, hlr, Nat.reduceLT] at *
  grind

/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
@[progress]
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧
      U8x32_as_Nat result < L ⦄ := by
    unfold to_bytes
    progress*

    /- To use `result[i]` (Fin-indexed) instead of `result[i]!`, uncomment the following.
       The elaborator's `get_elem_tactic` triggers expensive `whnf` on the 32-deep `.set` chain;
       pre-proving these bounds lets `assumption` shortcut that.
    have hresult : result.val.length = 32 := result.length_eq
    have : 0 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 1 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 2 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 3 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 4 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 5 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 6 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 7 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 8 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 9 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 10 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 11 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 12 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 13 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 14 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 15 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 16 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 17 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 18 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 19 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 20 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 21 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 22 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 23 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 24 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 25 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 26 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 27 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 28 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 29 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 30 < result.val.length := by simp only [hresult, Nat.reduceLT]
    have : 31 < result.val.length := by simp only [hresult, Nat.reduceLT]
    -/

    have : U8x32_as_Nat result = Scalar52_as_Nat self := by
      -- We first prove

      -- As `BitList`, self[0] corresponds to s[0]–s[5] and the lower nibble of s[6]
      have hlimb0 : (ofU64 self[0]).take 52 ≈ₗ
          ofU8 result[0]! ++ ofU8 result[1]! ++ ofU8 result[2]! ++
          ofU8 result[3]! ++ ofU8 result[4]! ++ ofU8 result[5]! ++
          (ofU8 result[6]!).take 4 := by sorry
      -- As `BitList`, self[1] corresponds to upper nibble of s[6] and s[7]–s[12]
      have hlimb1 : (ofU64 self[1]).take 52 ≈ₗ
          (ofU8 result[6]!).drop 4 ++
          ofU8 result[7]! ++ ofU8 result[8]! ++ ofU8 result[9]! ++
          ofU8 result[10]! ++ ofU8 result[11]! ++ ofU8 result[12]! := by sorry
      -- As `BitList`, self[2] corresponds to s[13]–s[18] and the lower nibble of s[19]
      have hlimb2 : (ofU64 self[2]).take 52 ≈ₗ
          ofU8 result[13]! ++ ofU8 result[14]! ++ ofU8 result[15]! ++
          ofU8 result[16]! ++ ofU8 result[17]! ++ ofU8 result[18]! ++
          (ofU8 result[19]!).take 4 := by sorry
      -- As `BitList`, self[3] corresponds to upper nibble of s[19] and s[20]–s[25]
      have hlimb3 : (ofU64 self[3]).take 52 ≈ₗ
          (ofU8 result[19]!).drop 4 ++
          ofU8 result[20]! ++ ofU8 result[21]! ++ ofU8 result[22]! ++
          ofU8 result[23]! ++ ofU8 result[24]! ++ ofU8 result[25]! := by sorry
      -- As `BitList`, self[4] corresponds to s[26]–s[31] (48 bits, top limb < 2^45)
      have hlimb4 : (ofU64 self[4]).take 48 ≈ₗ
          ofU8 result[26]! ++ ofU8 result[27]! ++ ofU8 result[28]! ++
          ofU8 result[29]! ++ ofU8 result[30]! ++ ofU8 result[31]! := by
        apply Equiv.of_toNat_eq_of_length_eq
        · -- toNat equality
          subst_vars
          simp [toNat_take, toNat_append, toNat_ofU8, toNat_ofU64,
            ofU8_length, ofNat_length, length_take, length_drop, length_append,
            Nat.min_def, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
            Nat.reduceLT, ite_true, ite_false]
          grind
          omega
        · -- length equality
          simp [length_take, length_append, ofU8_length, ofU64_length]
      exact scalar52_eq_of_bitList_limbs self result h
        (by have := Scalar52_top_limb_lt_of_canonical self h'; omega)
        hlimb0 hlimb1 hlimb2 hlimb3 hlimb4
    refine ⟨this, ?_⟩
    rw [this]
    exact h'

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
