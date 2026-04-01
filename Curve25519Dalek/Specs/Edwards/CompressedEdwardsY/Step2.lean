/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.AsBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign

/-! # Spec Theorem for `CompressedEdwardsY::decompress::step_2`

Specification and proof for the second step of `CompressedEdwardsY::decompress`.

This function performs the final decompression step which:
1. Extracts the sign bit from the compressed representation (byte 31, bit 7)
2. Conditionally negates the x-coordinate according to the sign bit
3. Computes T = X * Y
4. Returns the complete EdwardsPoint in extended coordinates (X, Y, Z, T)

Ported from the Verus spec in dalek-lite/curve25519-dalek/src/edwards.rs (lines 507-539),
which asserts: result.X = if sign then field_neg(X) else X, result.T = field_mul(result.X, Y),
Y and Z unchanged, limb bounds 52-bit.

**Source**: curve25519-dalek/src/edwards.rs, lines 230-248
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51
open curve25519_dalek.backend.serial.u64.field
open Edwards

namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Takes a CompressedEdwardsY and field elements X, Y, Z from step_1
    - Extracts the sign bit from the high bit of byte 31 of the compressed representation
    - Since sqrt_ratio_i returns the nonnegative square root, conditionally negates X
      according to the sign bit to match the encoded sign
    - Computes T = X * Y (the product of x and y coordinates)
    - Returns an EdwardsPoint with coordinates (X, Y, Z, T)

Natural language specs (ported from Verus):

    - The function always succeeds (no panic) given bounded inputs
    - result.X.toField = if sign_bit then -X.toField else X.toField
    - result.T.toField = result.X.toField * Y.toField
    - Y and Z are unchanged
    - Output bounds: result.X limbs ≤ 2^53-1, result.T limbs < 2^52
-/

private lemma fe_eq_of_limbs
    {a b : FieldElement51}
    (h : ∀ i < 5, a[i]! = b[i]!) :
    a = b := by
  simp only [Array.getElem!_Nat_eq] at h
  apply Subtype.ext
  apply List.ext_getElem (by
    simp [a.property, b.property])
  intro n hn _
  have hn5 : n < 5 := by
    simp only [a.property, UScalar.ofNatCore_val_eq] at hn
    exact hn
  have := h n hn5
  simp only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos, hn5] at this
  exact this

private lemma toField_neg
    {X xneg : FieldElement51}
    (h : Field51_as_Nat X +
      Field51_as_Nat xneg ≡ 0 [MOD p]) :
    xneg.toField = -X.toField := by
  simp only [FieldElement51.toField]
  have heq := lift_mod_eq _ 0 h
  simp only [Nat.cast_add, Nat.cast_zero] at heq
  rw [add_comm] at heq
  exact eq_neg_of_add_eq_zero_left heq

private lemma toField_mul
    {a b r : FieldElement51}
    (h : Field51_as_Nat r ≡
      Field51_as_Nat a * Field51_as_Nat b [MOD p]) :
    r.toField = a.toField * b.toField := by
  simp only [FieldElement51.toField]
  have heq := lift_mod_eq _ _ h
  push_cast at heq; exact heq

/-- **Spec for `edwards.decompress.step_2`** (ported from Verus):
- Returns an EdwardsPoint with coordinates (X', Y, Z, T) where:
  - Y and Z are unchanged from the inputs
  - X'.toField = if sign_bit then -X.toField else X.toField
  - X' limbs ≤ 2^53 - 1
  - T.toField = X'.toField * Y.toField
  - T limbs < 2^52
-/
@[step]
theorem step_2_spec
    (repr : edwards.CompressedEdwardsY)
    (X : backend.serial.u64.field.FieldElement51)
    (Y : backend.serial.u64.field.FieldElement51)
    (Z : backend.serial.u64.field.FieldElement51)
    (bytes : Aeneas.Std.Array U8 32#usize)
    (sign_bit : Bool)
    (h_repr : repr.as_bytes = ok bytes)
    (h_byter : sign_bit = (bytes[31]!.val.testBit 7))
    (hX : ∀ i < 5, X[i]!.val ≤ 2 ^ 53 - 1)
    (hY : ∀ i < 5, Y[i]!.val < 2 ^ 51) :
    edwards.decompress.step_2 repr X Y Z ⦃ result =>
      result.Y = Y ∧
      result.Z = Z ∧
      (if sign_bit then
        result.X.toField = -X.toField
      else
        result.X = X) ∧
      (∀ i < 5, result.X[i]!.val ≤ 2 ^ 53 - 1) ∧
      result.T.toField = result.X.toField * Y.toField ∧
      (∀ i < 5, result.T[i]!.val < 2 ^ 52) ⦄ := by
  have h_rb :
      (repr : Array U8 32#usize) = bytes := by
    unfold CompressedEdwardsY.as_bytes at h_repr
    simpa [spec_ok] using h_repr
  unfold edwards.decompress.step_2
  step*
  unfold subtle.Choice.Insts.CoreConvertFromU8.from
  have h_i1_le : i1.val ≤ 1 := by
    rw [i1_post1, Nat.shiftRight_eq_div_pow]
    have : i.val < 256 := by scalar_tac
    exact Nat.le_of_lt_succ
      (Nat.div_lt_of_lt_mul (by omega))
  have h_i1_eq :
      i1.val = bytes[31]!.val / 128 := by
    rw [i1_post1, i_post, a_post, h_rb,
      Nat.shiftRight_eq_div_pow]
    simp [Array.getElem!_Nat_eq]
  have hi1_01 : i1 = 0#u8 ∨ i1 = 1#u8 := by
    rcases Nat.eq_zero_or_pos i1.val with h | h
    · left; exact UScalar.eq_of_val_eq
        (by simpa using h)
    · right; apply UScalar.eq_of_val_eq
      show i1.val = (1#u8 : U8).val
      simp; omega
  rcases hi1_01 with h0 | h1
  · ---- i1 = 0 → sign_bit = false ----
    simp only [h0, ↓reduceDIte, bind_tc_ok, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      Nat.reducePow, Nat.add_one_sub_one]
    step*
    have hsb : sign_bit = false := by
      rw [h_byter, Nat.testBit,
        Nat.shiftRight_eq_div_pow, ← h_i1_eq]
      simp [h0]
    have hXeq : X1 = X := fe_eq_of_limbs
      (fun j hj => by
        have := X1_post j hj
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.not_eq,
          UScalar.ofNatCore_val_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one,
          not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq, ↓reduceIte] at this
        exact this)
    subst hXeq
    simp only [hsb, show (false = true) = False
      from by decide, ite_false, true_and]
    refine ⟨?_, toField_mul fe_post1, ?_⟩ <;>
    (intro j hj;
     simp only [← List.getElem!_eq_getElem?_getD,
       ← Array.getElem!_Nat_eq];
     first | exact hX j hj
           | exact fe_post2 j hj)
  · ---- i1 = 1 → sign_bit = true ----
    simp only [h1,
      show ¬(1#u8 : U8) = (0#u8 : U8)
        from by decide,
      _root_.dite_false, _root_.dite_true]
    step*
    have hsb : sign_bit = true := by
      rw [h_byter, Nat.testBit,
        Nat.shiftRight_eq_div_pow, ← h_i1_eq]
      simp [h1]
    have hXeq : X1 = x_neg := fe_eq_of_limbs
      (fun j hj => by
        have := X1_post j hj
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, ↓reduceIte] at this
        exact this)
    subst hXeq
    simp only [hsb, ite_true]
    refine ⟨toField_neg x_neg_post1,
      ?_, toField_mul fe_post1, fe_post2⟩
    intro j hj
    have := x_neg_post2 j hj; omega

end curve25519_dalek.edwards.CompressedEdwardsY
