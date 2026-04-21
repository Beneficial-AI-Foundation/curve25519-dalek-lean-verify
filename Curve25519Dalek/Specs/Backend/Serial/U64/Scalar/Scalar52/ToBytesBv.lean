/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-! # Alternative spec for `Scalar52::to_bytes` via `bv_decide`

Ports the structure used in `FieldElement51.to_bytes_spec`: an abstract byte-layout
predicate, four `bv_decide` primitives (limb recompositions + shared-byte OR split),
a Nat-level "abstract postcondition" lemma, a conformance lemma, and a combined spec.

No `BitList`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-! ## Part 0: local helpers -/

/-- Casting a U64 to U8 takes the value modulo `2^8`. Mirrors the helper in
`FieldElement51.to_bytes` but kept local to avoid the import. -/
@[local simp]
private theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  simp only [UScalar.cast, UScalarTy.U64_numBits_eq, UScalarTy.U8_numBits_eq,
    Aeneas.Bvify.U64.UScalar_bv, BitVec.truncate_eq_setWidth]
  simp only [UScalar.val]
  simp only [UScalarTy.U8_numBits_eq, BitVec.toNat_setWidth, UScalar.bv_toNat,
    UScalarTy.U64_numBits_eq, Aeneas.Bvify.U64.UScalar_bv]

/-! ## Part 1: abstract byte-layout predicate (the "abstract function") -/

/-- Byte-by-byte packing formula for 5 × 52-bit limbs into 32 LE bytes.
Each plain byte is a shifted slice of one limb; the 2 shared bytes (6 and 19) combine
bits from adjacent limbs via OR. -/
def bytes_match_limbs_52 (limbs : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  -- Limb 0 → bytes 0..5 and low nibble of byte 6
  s.val[0]!.val = limbs.val[0]!.val % 2 ^ 8 ∧
  s.val[1]!.val = limbs.val[0]!.val >>> 8 % 2 ^ 8 ∧
  s.val[2]!.val = limbs.val[0]!.val >>> 16 % 2 ^ 8 ∧
  s.val[3]!.val = limbs.val[0]!.val >>> 24 % 2 ^ 8 ∧
  s.val[4]!.val = limbs.val[0]!.val >>> 32 % 2 ^ 8 ∧
  s.val[5]!.val = limbs.val[0]!.val >>> 40 % 2 ^ 8 ∧
  s.val[6]!.val = (limbs.val[0]!.val >>> 48 ||| limbs.val[1]!.val <<< 4 % U64.size) % 2 ^ 8 ∧
  -- Limb 1 → bytes 7..12 (high nibble of byte 6 is shared via the OR above)
  s.val[7]!.val = limbs.val[1]!.val >>> 4 % 2 ^ 8 ∧
  s.val[8]!.val = limbs.val[1]!.val >>> 12 % 2 ^ 8 ∧
  s.val[9]!.val = limbs.val[1]!.val >>> 20 % 2 ^ 8 ∧
  s.val[10]!.val = limbs.val[1]!.val >>> 28 % 2 ^ 8 ∧
  s.val[11]!.val = limbs.val[1]!.val >>> 36 % 2 ^ 8 ∧
  s.val[12]!.val = limbs.val[1]!.val >>> 44 % 2 ^ 8 ∧
  -- Limb 2 → bytes 13..18 and low nibble of byte 19
  s.val[13]!.val = limbs.val[2]!.val % 2 ^ 8 ∧
  s.val[14]!.val = limbs.val[2]!.val >>> 8 % 2 ^ 8 ∧
  s.val[15]!.val = limbs.val[2]!.val >>> 16 % 2 ^ 8 ∧
  s.val[16]!.val = limbs.val[2]!.val >>> 24 % 2 ^ 8 ∧
  s.val[17]!.val = limbs.val[2]!.val >>> 32 % 2 ^ 8 ∧
  s.val[18]!.val = limbs.val[2]!.val >>> 40 % 2 ^ 8 ∧
  s.val[19]!.val = (limbs.val[2]!.val >>> 48 ||| limbs.val[3]!.val <<< 4 % U64.size) % 2 ^ 8 ∧
  -- Limb 3 → bytes 20..25 (high nibble of byte 19 is shared via the OR above)
  s.val[20]!.val = limbs.val[3]!.val >>> 4 % 2 ^ 8 ∧
  s.val[21]!.val = limbs.val[3]!.val >>> 12 % 2 ^ 8 ∧
  s.val[22]!.val = limbs.val[3]!.val >>> 20 % 2 ^ 8 ∧
  s.val[23]!.val = limbs.val[3]!.val >>> 28 % 2 ^ 8 ∧
  s.val[24]!.val = limbs.val[3]!.val >>> 36 % 2 ^ 8 ∧
  s.val[25]!.val = limbs.val[3]!.val >>> 44 % 2 ^ 8 ∧
  -- Limb 4 → bytes 26..31 (48 bits used; top 4 bits ignored — valid when < L)
  s.val[26]!.val = limbs.val[4]!.val % 2 ^ 8 ∧
  s.val[27]!.val = limbs.val[4]!.val >>> 8 % 2 ^ 8 ∧
  s.val[28]!.val = limbs.val[4]!.val >>> 16 % 2 ^ 8 ∧
  s.val[29]!.val = limbs.val[4]!.val >>> 24 % 2 ^ 8 ∧
  s.val[30]!.val = limbs.val[4]!.val >>> 32 % 2 ^ 8 ∧
  s.val[31]!.val = limbs.val[4]!.val >>> 40 % 2 ^ 8

/-! ## Part 2: bv_decide primitives -/

/-- A 52-bit limb decomposes into 6 full bytes plus a 4-bit spillover. -/
theorem recompose_limb_52 (limb : U64) (h : limb.val < 2 ^ 52) :
    limb.val =
      limb.val % 2 ^ 8
    + 2 ^ 8  * (limb.val >>> 8  % 2 ^ 8)
    + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
    + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
    + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
    + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8)
    + 2 ^ 48 * (limb.val >>> 48 % 2 ^ 8) := by
  bvify 64 at *; bv_decide

/-- A 52-bit limb shifted left by 4 decomposes into a 4-bit low-byte fragment
plus 6 full bytes. Used for limbs 1 and 3 whose low nibble spills into the preceding
shared byte (s[6] and s[19]). -/
theorem recompose_limb_52_shift4 (limb : U64) (h : limb.val < 2 ^ 52) :
      (limb.val <<< 4 % 2 ^ 8)
    + 2 ^ 8  * (limb.val >>> 4  % 2 ^ 8)
    + 2 ^ 16 * (limb.val >>> 12 % 2 ^ 8)
    + 2 ^ 24 * (limb.val >>> 20 % 2 ^ 8)
    + 2 ^ 32 * (limb.val >>> 28 % 2 ^ 8)
    + 2 ^ 40 * (limb.val >>> 36 % 2 ^ 8)
    + 2 ^ 48 * (limb.val >>> 44 % 2 ^ 8)
    = 2 ^ 4 * limb.val := by
  bvify 64 at *; bv_decide

/-- A 48-bit top limb decomposes into 6 full bytes (no spillover). -/
theorem recompose_top_limb_48 (limb : U64) (h : limb.val < 2 ^ 48) :
    limb.val =
      limb.val % 2 ^ 8
    + 2 ^ 8  * (limb.val >>> 8  % 2 ^ 8)
    + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
    + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
    + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
    + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8) := by
  bvify 64 at *; bv_decide

/-- OR of non-overlapping shifted halves at a shared byte equals the sum of the
two byte-fragments. Precondition `limb0.val < 2^52` means `limb0 >>> 48 < 2^4`,
and `limb1 <<< 4` has zeros in its bottom 4 bits — the ranges are disjoint. -/
theorem decompose_or_limbs_shift4 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 52) :
    ((limb0.val >>> 48 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
      (limb0.val >>> 48 % 2 ^ 8) + (limb1.val <<< 4 % 2 ^ 8) := by
  bvify 64 at *
  have : BitVec.ofNat 64 (limb1.val <<< 4 % U64.size) = limb1.bv <<< 4 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, U64.size, U64.numBits, Nat.shiftLeft_eq]
  rw [this]; bv_decide

/-! ## Part 3: Postcondition of the abstract function

Given `bytes_match_limbs_52`, the byte-array interpretation equals `Scalar52_as_Nat`. -/

/-- Byte-packing correctness: when the bytes match the abstract layout, the 32-byte
little-endian interpretation equals the radix-2^52 limb interpretation. -/
theorem byte_packing_eq_52 (limbs : Array U64 5#usize) (s : Array U8 32#usize)
    (hlimbs : ∀ i < 5, limbs.val[i]!.val < 2 ^ 52)
    (htop : limbs.val[4]!.val < 2 ^ 48)
    (hbytes : bytes_match_limbs_52 limbs s) :
    U8x32_as_Nat s = Scalar52_as_Nat limbs := by
  unfold bytes_match_limbs_52 at hbytes
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
          hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
          hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31⟩ := hbytes
  have hL0 : limbs.val[0]!.val < 2 ^ 52 := hlimbs 0 (by omega)
  have hL1 : limbs.val[1]!.val < 2 ^ 52 := hlimbs 1 (by omega)
  have hL2 : limbs.val[2]!.val < 2 ^ 52 := hlimbs 2 (by omega)
  have hL3 : limbs.val[3]!.val < 2 ^ 52 := hlimbs 3 (by omega)
  have hd6 := decompose_or_limbs_shift4 limbs.val[0]! limbs.val[1]! hL0
  have hd19 := decompose_or_limbs_shift4 limbs.val[2]! limbs.val[3]! hL2
  have hr0 := recompose_limb_52 limbs.val[0]! hL0
  have hr1 := recompose_limb_52_shift4 limbs.val[1]! hL1
  have hr2 := recompose_limb_52 limbs.val[2]! hL2
  have hr3 := recompose_limb_52_shift4 limbs.val[3]! hL3
  have hr4 := recompose_top_limb_48 limbs.val[4]! htop
  unfold U8x32_as_Nat Scalar52_as_Nat
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    Array.getElem!_Nat_eq, Nat.reduceMul, zero_add,
    hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12,
    hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23,
    hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31,
    hd6, hd19]
  linarith

/-! ## Part 4: top-limb bound from the canonical hypothesis -/

/-- If `Scalar52_as_Nat self < L`, the top limb is bounded by `2^48`
(in fact by `2^45`, but `2^48` suffices for `to_bytes`). -/
theorem top_limb_lt_2_48 (self : Array U64 5#usize) (h' : Scalar52_as_Nat self < L) :
    self.val[4]!.val < 2 ^ 48 := by
  unfold Scalar52_as_Nat at h'
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Array.getElem!_Nat_eq] at h'
  have : L < 2 ^ 253 := by unfold L; omega
  omega

/-! ## Part 5: conformance — Rust `to_bytes` produces a layout-matching byte array -/

set_option maxHeartbeats 1600000 in -- heavy step* over 32 byte assignments
/-- The Rust function `to_bytes` produces a byte array that satisfies
`bytes_match_limbs_52`. -/
theorem to_bytes_matches_layout (self : Scalar52) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      bytes_match_limbs_52 self result ⦄ := by
  unfold to_bytes
  step*
  unfold bytes_match_limbs_52
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (subst_vars
     simp only [Array.set_val_eq, getElem!_pos, List.length_set, List.Vector.length_val,
       List.getElem_set_self, ne_eq, not_false_eq_true, List.getElem_set_ne,
       UScalar.ofNatCore_val_eq,
       Nat.reduceLT, Nat.lt_add_one, Nat.one_lt_ofNat, Nat.ofNat_pos,
       Nat.reduceEqDiff, Nat.succ_ne_self,
       one_ne_zero, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero,
       U64_cast_U8, UScalar.val_or, Nat.shiftRight_zero, *])

/-! ## Part 6: main theorem — combine conformance + abstract postcondition -/

/-- **Alternative spec and proof for `scalar.Scalar52.to_bytes`**:
same statement as the existing `to_bytes_spec` but proved via the abstract
layout predicate and `bv_decide` instead of `BitList`. -/
theorem to_bytes_spec' (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧ U8x32_as_Nat result < L ⦄ := by
  have hval : ∀ i < 5, self.val[i]!.val < 2 ^ 52 := by
    intro i hi; have := h i hi; simpa using this
  have htop := top_limb_lt_2_48 self h'
  exact WP.spec_mono (to_bytes_matches_layout self) fun result hbytes =>
    have heq := byte_packing_eq_52 self result hval htop hbytes
    ⟨heq, heq ▸ h'⟩

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
