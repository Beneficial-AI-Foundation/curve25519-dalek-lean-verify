/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Aeneas.Std.WP

/-! # Spec Theorem for `Scalar::from(u16)`

Specification and proof for `FromScalarU16::from`.

This function embeds a u16 into a Scalar by writing its little-endian bytes.

**Source**: curve25519-dalek/src/scalar.rs
-/

open Aeneas
open scoped Aeneas
open scoped Aeneas.Std.WP
open Aeneas.Std Result
namespace curve25519_dalek.scalar.FromScalarU16

private lemma bitvec_split {n : Nat} (b : BitVec n) :
    b.toNat = (BitVec.setWidth 8 b).toNat + 2^8 * (b >>> 8).toNat := by
  have hmod : (BitVec.setWidth 8 b).toNat = b.toNat % 2^8 := by
    simp [BitVec.toNat_setWidth]
  have hsh : (b >>> 8).toNat = b.toNat >>> 8 := by
    simp [BitVec.toNat_ushiftRight]
  have hdiv : b.toNat >>> 8 = b.toNat / 2^8 := by
    simp [Nat.shiftRight_eq_div_pow]
  have hsplit : b.toNat = b.toNat % 2^8 + 2^8 * (b.toNat / 2^8) :=
    (Nat.mod_add_div _ _).symm
  calc
    b.toNat = b.toNat % 2^8 + 2^8 * (b.toNat / 2^8) := hsplit
    _ = (BitVec.setWidth 8 b).toNat + 2^8 * (b.toNat / 2^8) := by simp [hmod]
    _ = (BitVec.setWidth 8 b).toNat + 2^8 * (b >>> 8).toNat := by simp [hsh, hdiv]

private lemma bitvec_shiftRight_lt (b : BitVec 16) :
    (b >>> 8).toNat < 2^8 := by
  have hb : b.toNat < 2^16 := by simpa using b.isLt
  have hpos : 0 < 2^8 := by decide
  have hb' : b.toNat / 2^8 < 2^8 := by
    apply (Nat.div_lt_iff_lt_mul (k := 2^8) (x := b.toNat) (y := 2^8) hpos).2
    simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using hb'

private lemma bitvec_setWidth_shiftRight_toNat (b : BitVec 16) :
    (BitVec.setWidth 8 (b >>> 8)).toNat = (b >>> 8).toNat := by
  have hlt : (b >>> 8).toNat < 2^8 := bitvec_shiftRight_lt b
  calc
    (BitVec.setWidth 8 (b >>> 8)).toNat = (b >>> 8).toNat % 2^8 := by
      simp [-BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]
    _ = (b >>> 8).toNat := by
      exact Nat.mod_eq_of_lt hlt

private lemma u16_to_le_bytes_val (x : U16) :
    x.val =
      (core.num.U16.to_le_bytes x).val[0]!.val +
        2^8 * (core.num.U16.to_le_bytes x).val[1]!.val := by
  have hbytes : x.bv.toLEBytes =
      BitVec.setWidth 8 x.bv :: BitVec.setWidth 8 (x.bv >>> 8) :: [] := by
    simp [BitVec.toLEBytes.eq_1]
  have hlist :
      (core.num.U16.to_le_bytes x).val =
        x.bv.toLEBytes.map (UScalar.mk (ty := UScalarTy.U8)) := by
    simp [core.num.U16.to_le_bytes]
  have h0 :
      (core.num.U16.to_le_bytes x).val[0]!.val =
        (BitVec.setWidth 8 x.bv).toNat := by
    calc
      (core.num.U16.to_le_bytes x).val[0]!.val
          = ((x.bv.toLEBytes.map (UScalar.mk (ty := UScalarTy.U8)))[0]!).val := by
            simp [hlist]
      _ = (UScalar.mk (ty := UScalarTy.U8) (BitVec.setWidth 8 x.bv)).val := by
            simp [hbytes]
      _ = (BitVec.setWidth 8 x.bv).toNat := by rfl
  have h1 :
      (core.num.U16.to_le_bytes x).val[1]!.val =
        (BitVec.setWidth 8 (x.bv >>> 8)).toNat := by
    calc
      (core.num.U16.to_le_bytes x).val[1]!.val
          = ((x.bv.toLEBytes.map (UScalar.mk (ty := UScalarTy.U8)))[1]!).val := by
            simp [hlist]
      _ =
          (UScalar.mk (ty := UScalarTy.U8)
            (BitVec.setWidth 8 (x.bv >>> 8))).val := by
            simp [hbytes]
      _ = (BitVec.setWidth 8 (x.bv >>> 8)).toNat := by rfl
  have hsplit :
      x.bv.toNat =
        (BitVec.setWidth 8 x.bv).toNat +
          2^8 * (BitVec.setWidth 8 (x.bv >>> 8)).toNat := by
    calc
      x.bv.toNat =
          (BitVec.setWidth 8 x.bv).toNat + 2^8 * (x.bv >>> 8).toNat :=
        bitvec_split x.bv
      _ =
          (BitVec.setWidth 8 x.bv).toNat +
            2^8 * (BitVec.setWidth 8 (x.bv >>> 8)).toNat := by
          rw [bitvec_setWidth_shiftRight_toNat]
  have hsplit' :
      x.val =
        (BitVec.setWidth 8 x.bv).toNat +
          2^8 * (BitVec.setWidth 8 (x.bv >>> 8)).toNat := by
    simpa using hsplit
  calc
    x.val =
        (BitVec.setWidth 8 x.bv).toNat +
          2^8 * (BitVec.setWidth 8 (x.bv >>> 8)).toNat := hsplit'
    _ =
        (core.num.U16.to_le_bytes x).val[0]!.val +
          2^8 * (core.num.U16.to_le_bytes x).val[1]!.val := by
      rw [← h0, ← h1]


private lemma from_u16_eval (x : U16) :
  «from» x =
    ok { bytes := (Array.repeat 32#usize 0#u8).setSlice! 0 (core.num.U16.to_le_bytes x).val } := by
  -- TODO: reduce the index_mut/copy_from_slice pipeline to setSlice!
  sorry

/-
natural language description:

    • Creates a Scalar whose byte representation contains the little-endian
      encoding of x in the first two bytes and zeros elsewhere.

natural language specs:

    • The resulting scalar encodes the same numeric value as x
    • The function always succeeds (no panic)
-/

/-- **Spec and proof concerning `scalar.FromScalarU16.from`**:
- No panic (always returns successfully)
- The resulting Scalar encodes the value x
-/

@[progress]
theorem from_spec (x_u16 : U16) :
  «from» x_u16 ⦃ s => U8x32_as_Nat s.bytes = x_u16.val ⦄ := by
  -- TODO: unfold `from`, rewrite via `from_u16_eval`, reduce `U8x32_as_Nat` to the
  -- first two bytes, then use `u16_to_le_bytes_val`.
  sorry

end curve25519_dalek.scalar.FromScalarU16
