/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Lim Jin Xing, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-! # Spec theorem

Specification for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::to_bytes`.

Pack a `Scalar52` (5 little-endian 52-bit limbs) into 32 bytes.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs.

## Bit layout

Each limb spans 52 = 6*8 + 4 bits, so it fills 6 full bytes plus 4 bits shared with the
next limb. Shared bytes `s[6]` and `s[19]` combine the high nibble of one limb with the
low nibble of the next via `(prev >> 48) | (next << 4)`. The top limb uses only 48 bits
(`s[26]-s[31]`) since the canonical bound `Scalar52_as_Nat self < L < 2^253` forces
`self[4] < 2^45 < 2^48`.

## Proof structure

1. `decompose_limb_{52,shift4,48}` and `decompose_or_shared` (`bv_decide`): per-operand
   bit identities tying byte slices to their limb sources.
2. `bytes_match_limbs_52`: a 32-conjunct layout predicate matching the extraction.
3. `byte_packing_eq` (Nat glue): under the layout predicate, the LE byte sum equals
   the radix-2^52 limb sum.
4. `to_bytes_spec`: drive the body with `step*`, prove the layout predicate, conclude.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

attribute [simp_scalar] BitVec.toNat_shiftLeft
attribute [local simp] U64_cast_U8

/-! ## Bit-layer primitives (`bv_decide`) -/

/-- Decompose a 52-bit limb into 6 little-endian bytes plus a 4-bit nibble. -/
private theorem decompose_limb_52 (x : U64) (h : x.val < 2 ^ 52) :
    x.val =
      x.val % 2 ^ 8
      + 2 ^ 8 * (x.val >>> 8 % 2 ^ 8)
      + 2 ^ 16 * (x.val >>> 16 % 2 ^ 8)
      + 2 ^ 24 * (x.val >>> 24 % 2 ^ 8)
      + 2 ^ 32 * (x.val >>> 32 % 2 ^ 8)
      + 2 ^ 40 * (x.val >>> 40 % 2 ^ 8)
      + 2 ^ 48 * (x.val >>> 48) := by
  bvify 64 at *
  bv_decide

/-- Decompose a 52-bit limb shifted left by 4: 4-bit nibble plus 6 little-endian bytes. -/
private theorem decompose_limb_shift4 (x : U64) (h : x.val < 2 ^ 52) :
    x.val <<< 4 % 2 ^ 8
      + 2 ^ 8 * (x.val >>> 4 % 2 ^ 8)
      + 2 ^ 16 * (x.val >>> 12 % 2 ^ 8)
      + 2 ^ 24 * (x.val >>> 20 % 2 ^ 8)
      + 2 ^ 32 * (x.val >>> 28 % 2 ^ 8)
      + 2 ^ 40 * (x.val >>> 36 % 2 ^ 8)
      + 2 ^ 48 * (x.val >>> 44 % 2 ^ 8) =
      2 ^ 4 * x.val := by
  bvify 64 at *
  bv_decide

/-- Decompose a top limb (48 bits) into 6 little-endian bytes. -/
private theorem decompose_limb_48 (x : U64) (h : x.val < 2 ^ 48) :
    x.val =
      x.val % 2 ^ 8
      + 2 ^ 8 * (x.val >>> 8 % 2 ^ 8)
      + 2 ^ 16 * (x.val >>> 16 % 2 ^ 8)
      + 2 ^ 24 * (x.val >>> 24 % 2 ^ 8)
      + 2 ^ 32 * (x.val >>> 32 % 2 ^ 8)
      + 2 ^ 40 * (x.val >>> 40 % 2 ^ 8) := by
  bvify 64 at *
  bv_decide

/-- OR-of-shares primitive: at a shared byte (lower 4 bits from x >>> 48, upper 4 from y << 4),
mod 2^8 splits as sum of the two shifted parts (mod 2^8 each). -/
private theorem decompose_or_shared (x y : U64) (hx : x.val < 2 ^ 52) :
    ((x.val >>> 48 ||| y.val <<< 4 % U64.size) % 2 ^ 8) =
      (x.val >>> 48) + (y.val <<< 4 % 2 ^ 8) := by
  bvify 64 at *
  rw [show BitVec.ofNat 64 (y.val <<< 4 % U64.size) = y.bv <<< 4 from by natify; simp_scalar]
  bv_decide

/-! ## Layout predicate -/

/-- Byte-by-byte packing formula for 5 x 52-bit limbs into 32 LE bytes.
Matches the Rust source and the Lean extraction. The two shared bytes (6 and 19) combine
bits from adjacent limbs. -/
def bytes_match_limbs_52 (L : Scalar52) (s : Std.Array U8 32#usize) : Prop :=
  -- Limb 0 (bits 0-51) -> bytes 0-6
  s.val[0]!.val = L.val[0]!.val % 2 ^ 8 ∧
  s.val[1]!.val = L.val[0]!.val >>> 8 % 2 ^ 8 ∧
  s.val[2]!.val = L.val[0]!.val >>> 16 % 2 ^ 8 ∧
  s.val[3]!.val = L.val[0]!.val >>> 24 % 2 ^ 8 ∧
  s.val[4]!.val = L.val[0]!.val >>> 32 % 2 ^ 8 ∧
  s.val[5]!.val = L.val[0]!.val >>> 40 % 2 ^ 8 ∧
  s.val[6]!.val = (L.val[0]!.val >>> 48 ||| L.val[1]!.val <<< 4 % U64.size) % 2 ^ 8 ∧
  -- Limb 1 (bits 52-103) -> bytes 6-12
  s.val[7]!.val = L.val[1]!.val >>> 4 % 2 ^ 8 ∧
  s.val[8]!.val = L.val[1]!.val >>> 12 % 2 ^ 8 ∧
  s.val[9]!.val = L.val[1]!.val >>> 20 % 2 ^ 8 ∧
  s.val[10]!.val = L.val[1]!.val >>> 28 % 2 ^ 8 ∧
  s.val[11]!.val = L.val[1]!.val >>> 36 % 2 ^ 8 ∧
  s.val[12]!.val = L.val[1]!.val >>> 44 % 2 ^ 8 ∧
  -- Limb 2 (bits 104-155) -> bytes 13-19
  s.val[13]!.val = L.val[2]!.val % 2 ^ 8 ∧
  s.val[14]!.val = L.val[2]!.val >>> 8 % 2 ^ 8 ∧
  s.val[15]!.val = L.val[2]!.val >>> 16 % 2 ^ 8 ∧
  s.val[16]!.val = L.val[2]!.val >>> 24 % 2 ^ 8 ∧
  s.val[17]!.val = L.val[2]!.val >>> 32 % 2 ^ 8 ∧
  s.val[18]!.val = L.val[2]!.val >>> 40 % 2 ^ 8 ∧
  s.val[19]!.val = (L.val[2]!.val >>> 48 ||| L.val[3]!.val <<< 4 % U64.size) % 2 ^ 8 ∧
  -- Limb 3 (bits 156-207) -> bytes 19-25
  s.val[20]!.val = L.val[3]!.val >>> 4 % 2 ^ 8 ∧
  s.val[21]!.val = L.val[3]!.val >>> 12 % 2 ^ 8 ∧
  s.val[22]!.val = L.val[3]!.val >>> 20 % 2 ^ 8 ∧
  s.val[23]!.val = L.val[3]!.val >>> 28 % 2 ^ 8 ∧
  s.val[24]!.val = L.val[3]!.val >>> 36 % 2 ^ 8 ∧
  s.val[25]!.val = L.val[3]!.val >>> 44 % 2 ^ 8 ∧
  -- Limb 4 (bits 208-255) -> bytes 26-31
  s.val[26]!.val = L.val[4]!.val % 2 ^ 8 ∧
  s.val[27]!.val = L.val[4]!.val >>> 8 % 2 ^ 8 ∧
  s.val[28]!.val = L.val[4]!.val >>> 16 % 2 ^ 8 ∧
  s.val[29]!.val = L.val[4]!.val >>> 24 % 2 ^ 8 ∧
  s.val[30]!.val = L.val[4]!.val >>> 32 % 2 ^ 8 ∧
  s.val[31]!.val = L.val[4]!.val >>> 40 % 2 ^ 8

/-! ## Nat-level glue lemma -/

/-- Byte packing correctness: when limbs are within bounds (lowest 4 < 2^52, top < 2^48) and
bytes match the packing formula, the LE byte interpretation equals the radix-2^52 value. -/
private theorem byte_packing_eq (a : Scalar52) (s : Std.Array U8 32#usize)
    (h : ∀ i < 5, a.val[i]!.val < 2 ^ 52) (h4 : a.val[4]!.val < 2 ^ 48)
    (hb : bytes_match_limbs_52 a s) :
    U8x32_as_Nat s = Scalar52_as_Nat a := by
  unfold bytes_match_limbs_52 at hb
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
          hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
          hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31⟩ := hb
  have hd0 := decompose_limb_52 a.val[0]! (h 0 (by omega))
  have hd1 := decompose_limb_shift4 a.val[1]! (h 1 (by omega))
  have hd2 := decompose_limb_52 a.val[2]! (h 2 (by omega))
  have hd3 := decompose_limb_shift4 a.val[3]! (h 3 (by omega))
  have hd4 := decompose_limb_48 a.val[4]! h4
  have hor6 := decompose_or_shared a.val[0]! a.val[1]! (h 0 (by omega))
  have hor19 := decompose_or_shared a.val[2]! a.val[3]! (h 2 (by omega))
  unfold U8x32_as_Nat Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Array.getElem!_Nat_eq, Nat.reduceMul, zero_add,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
    hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
    hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31,
    hor6, hor19]
  linarith

/-! ## Main spec -/

/-- **Spec theorem**

Specification for `curve25519_dalek::backend::serial::u64::scalar::Scalar52::to_bytes`.
• The result byte array represents the same number as the input unpacked scalar
• The result is in canonical form (less than L) -/
@[step]
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧ U8x32_as_Nat result < L ⦄ := by
  unfold to_bytes
  step*
  simp only [Array.getElem!_Nat_eq] at h
  -- `Scalar52_as_Nat self < L < 2^253` forces the top limb below `2^48`.
  have h_top : self.val[4]!.val < 2 ^ 48 := by
    simp only [Scalar52_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, Array.getElem!_Nat_eq] at h'
    have : L < 2 ^ 253 := by unfold L; omega
    omega
  have hbytes : bytes_match_limbs_52 self result := by
    unfold bytes_match_limbs_52
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Array.set_val_eq, getElem!_pos, List.length_set, List.Vector.length_val,
      List.getElem_set_self, List.getElem_set_ne, ne_eq, not_false_eq_true,
      UScalar.ofNatCore_val_eq, U64_cast_U8, UScalar.val_or, Nat.shiftRight_zero,
      Nat.reduceLT, Nat.lt_add_one, Nat.reduceEqDiff, *]
  have hpack := byte_packing_eq self result h h_top hbytes
  exact ⟨hpack, hpack ▸ h'⟩

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
