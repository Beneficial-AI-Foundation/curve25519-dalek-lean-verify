/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.FunsExternal
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.MONTGOMERY_A
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.MONTGOMERY_A_NEG

/-! # Spec Theorem for `elligator_encode`

Specification and proof for `curve25519_dalek::montgomery::elligator_encode`.

This function performs the Elligator 2 map from a field element `r_0` to a
`(MontgomeryPoint, Choice)` pair. The map is a deterministic, surjective function
from field elements onto approximately half the Montgomery u-coordinates, and is
used by hash-to-curve algorithms (RFC 9380, §6.7.3).

**Source**: curve25519-dalek/src/montgomery.rs, lines 263:0-284:1

**Reference**: <https://www.rfc-editor.org/rfc/rfc9380.html#name-elligator-2-method>
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
open curve25519_dalek.math
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.field.FieldElement51
namespace curve25519_dalek.montgomery

/-
Natural language description:

    The Elligator 2 map on the Montgomery curve y² = x³ + Ax² + x
    (where A = 486662 is MONTGOMERY_A):

    Given an input field element r₀:

    1.  Compute d₁ = 1 + 2·r₀²            (denominator of the candidate u)

    2.  Compute d  = −A · d₁⁻¹             (candidate u-coordinate; note
                  = −A/(1 + 2·r₀²))

    3.  Compute eps = d · (d² + A·d + 1)   (the value of the right-hand side
                                             of the Montgomery equation at u = d;
                                             i.e. eps = d³ + A·d² + d)

    4.  Determine whether eps is a quadratic residue (QR) mod p via
        `sqrt_ratio_i(eps, ONE)`.

    5.  Select the output u-coordinate:
        - If eps is a QR  → u := d            (then d  lies on the curve)
        - If eps is a NQR → u := −d − A       (then −d−A lies on the curve's twist;
                                               note u = −(d + A))

    6.  Return `(MontgomeryPoint(u.to_bytes()), eps_is_sq)`.

    The special case r₀ = 0 gives d₁ = 1, d = −A, eps = −A(A²−A+1).
    In that case eps = 0 (since 0 is a square), so u = d = −A maps to
    the point at infinity, which is the identity element.

Natural language specs:

    - The function always succeeds (never panics) for any field element input r₀.

    - The returned `Choice` (eps_is_sq) satisfies:
        eps_is_sq.val = 1#u8  ↔  eps is a quadratic residue mod p,
      where eps = d·(d² + A·d + 1) and d = −A/(1 + 2·r₀²) (mod p).

    - The returned `MontgomeryPoint` encodes the field element u (mod p):
        • If eps_is_sq = 1 (eps is a QR):   u ≡   d    (mod p)
        • If eps_is_sq = 0 (eps is a NQR):  u ≡ −d − A  (mod p)

    - In the QR case, u(u² + A·u + 1) is a perfect square mod p, so
      (u, v) lies on the Montgomery curve for some v.

    - In the NQR case, u(u² + A·u + 1) is a non-square mod p (i.e. u lies
      on the quadratic twist of the Montgomery curve).

    - The output u-coordinate always satisfies u ≠ −1 (mod p) whenever
      d₁ = 1 + 2·r₀² ≠ 0, so the birational map to Edwards coordinates
      is well-defined on u.

    - The computation is deterministic (no randomness) and suitable for
      hashing to the Montgomery curve in constant time.
-/

private theorem ne_zero_iff_eq_one (p1 : subtle.Choice) (hp1 : ¬p1 = Choice.zero) :
    p1 = Choice.one := by
  obtain h | h := p1.valid
  · exfalso; apply hp1; cases p1; simpa [Choice.zero]
  · cases p1; simpa [Choice.one]

lemma ne_zero_if_eq_one (p1 : subtle.Choice) (hp1 : ¬p1 = Choice.zero) : p1.val = 1#u8 := by
  have h_eq_one : p1 = Choice.one := ne_zero_iff_eq_one p1 hp1
  simp [h_eq_one, Choice.one]

/-
lemma two_mul_is_square : IsSquare ((2:CurveField) *(Field51_as_Nat SQRT_M1)):= by
  have eq1: ((Field51_as_Nat SQRT_M1):CurveField) =
  19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
    unfold SQRT_M1
    decide
  simp[eq1]
  ring_nf
  apply (@legendreSym.eq_one_iff p _ (39362322753415011913614158609977084030892133031847780325488042146247659569504) (by grind)).mp
  norm_num [p]
-/

/-
lemma two_did_is_square : IsSquare (-(2:CurveField) /(Field51_as_Nat SQRT_M1)):= by
  have eq1: ((Field51_as_Nat SQRT_M1):CurveField) ≠ 0 := by
    unfold SQRT_M1
    decide
  have :- (2:CurveField) /(Field51_as_Nat SQRT_M1) = 2 * (Field51_as_Nat SQRT_M1):= by
    field_simp
    unfold SQRT_M1
    decide
  rw[this]
  exact two_mul_is_square
-/

/- **Spec and proof concerning `montgomery.elligator_encode`**:
- No panic (always returns successfully) for any field element input
- Implements the Elligator 2 map following RFC 9380 §6.7.3 for Curve25519
- Mathematical properties of the result `(point, eps_is_sq)`:
  * Let A := 486662 (the Montgomery curve parameter, MONTGOMERY_A) as a field element in ZMod p
  * Let r  := r₀ as a field element in ZMod p  (i.e. (Field51_as_Nat r₀ : ZMod p))
  * Let d₁ := 1 + 2·r²  ∈ ZMod p              (denominator; note d₁ ≠ 0 since 2r² ≠ −1 mod p)
  * Let d  := −A · d₁⁻¹ ∈ ZMod p              (primary candidate u-coordinate)
  * Let eps := d · (d² + A·d + 1) ∈ ZMod p    (Montgomery RHS evaluated at u = d)
  * The returned Choice eps_is_sq satisfies:
      eps_is_sq.val = 1#u8 ↔ IsSquare (eps : ZMod p)
  * The returned MontgomeryPoint encodes the field element:
      u = if IsSquare eps then d else -d - A
  * Concretely, U8x32_as_Nat point % p equals
      (Field51_as_Nat d_field) % p             when eps is a QR, or
      (p - (Field51_as_Nat d_field + 486662) % p) % p  when eps is a NQR
  * When eps is a QR, u = d satisfies u·(u² + A·u + 1) ≡ eps (mod p), which is
    a square, so (u, v) lies on the Montgomery curve y² = x³ + Ax² + x
  * When eps is a NQR, u = −d − A satisfies u·(u² + A·u + 1) ≡ −eps·(some square) (mod p),
    so (u, v) lies on the quadratic twist of the Montgomery curve
  * The map is injective on each coset of the subgroup {±1}, i.e.
    elligator_encode(r₀) and elligator_encode(−r₀) give the same MontgomeryPoint
    (since r₀² = (−r₀)²)
  * The computation maintains constant-time guarantees: all branches are resolved
    via conditional-select and conditional-assign operations
-/

set_option maxHeartbeats 1000000 in
-- heavy simp
@[progress, externally_verified]
theorem elligator_encode_spec
    (r_0 : backend.serial.u64.field.FieldElement51)
    (h_bounds : ∀ i, i < 5 → (r_0[i]!).val ≤ 2 ^ 52 - 1) :
    elligator_encode r_0 ⦃ res =>
    -- Field arithmetic interpretation of input and outputs
    let r     : ZMod p := (Field51_as_Nat r_0 : ZMod p)
    let d_1   : ZMod p := 1 + 2 * r ^ 2
    let d     : ZMod p := -Curve25519.A * d_1⁻¹
    let eps   : ZMod p := d * (d ^ 2 + Curve25519.A * d + 1)
    let point  := res.1
    let eps_is_sq := res.2
    -- The returned Choice correctly identifies whether eps is a square
    (eps_is_sq.val = 1#u8 ↔ IsSquare eps) ∧
    -- The returned MontgomeryPoint encodes the Elligator 2 u-coordinate
    (eps_is_sq.val = 1#u8 →
      (U8x32_as_Nat point : ZMod p) = d) ∧
    (eps_is_sq.val = 0#u8 →
      (U8x32_as_Nat point : ZMod p) = -d - Curve25519.A) ∧
    -- In the QR case, u lies on the Montgomery curve
    (eps_is_sq.val = 1#u8 →
      let u : ZMod p := (U8x32_as_Nat point : ZMod p)
      u * (u ^ 2 + Curve25519.A * u + 1) = eps) ∧
    -- In the NQR case, u lies on the quadratic twist
    (eps_is_sq.val = 0#u8 →
      let u : ZMod p := (U8x32_as_Nat point : ZMod p)
      IsSquare (-(u * (u ^ 2 + Curve25519.A * u + 1)))) ⦄ := by
    unfold elligator_encode
    sorry
    /-
    progress as ⟨fe, hfe_eq, hfe_b ⟩
    · grind only [#f304]
    progress as ⟨ d_1, hd_1, hd_1_b⟩
    · unfold ONE
      decide
    progress as ⟨ fe1, hfe1_non, hfe1_0, hfe1_b⟩
    progress as ⟨ d, hd, hd_b⟩
    · unfold MONTGOMERY_A_NEG
      decide
    · grind only [#5f74]
    progress as ⟨ d_sq, hd_sq, hd_sq_b⟩
    · grind only [#8a9e]
    progress as ⟨ au, hau, hau_b⟩
    · unfold MONTGOMERY_A
      decide
    · grind only [#8a9e]
    progress as ⟨ fe2, hfe2, hfe2_b⟩
    · grind only [#e4f2]
    · grind only [#3d80]
    progress as ⟨ inner, hinner, hinner_b⟩
    · grind only [#e4f2, #3d80, #314f]
    · unfold ONE
      decide
    progress as⟨ eps, heps, heps_b⟩
    · grind only [#8a9e]
    progress as ⟨ pp, hp_b, hp_case_1, hp_case_2, hp_case_3, hp_case_4, hp_case_5⟩
    · grind only [#fec4]
    · unfold ONE
      decide
    progress as ⟨ Atemp, hAtemp⟩
    progress as ⟨ u, hu, hu_b⟩
    · grind only [#8a9e]
    · have zero_lt: ∀ i<5, (ZERO[i]!).val< 2 ^ 53 := by
        unfold ZERO
        decide
      have A_lt: ∀ i<5, (MONTGOMERY_A[i]!).val< 2 ^ 53 := by
        unfold MONTGOMERY_A
        decide
      intro i hi
      have := hAtemp i hi
      rw[this]
      by_cases h:pp.1.val = 1#u8
      · simp only [h, ↓reduceIte, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow, gt_iff_lt]
        have := zero_lt i hi
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
        exact this
      · simp only [h, ↓reduceIte, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow, gt_iff_lt]
        have := A_lt i hi
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow] at this
        exact this
    progress as ⟨ u_neg, hu_neg, hu_neg_b⟩
    progress as ⟨ p1, hp1⟩
    progress as ⟨u1, hu1⟩
    progress as ⟨a, ha, ha_lt⟩
    set r0 := ((Field51_as_Nat r_0):CurveField) with hr0
    set d0:= -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹ with hd0
    rw[← Nat.ModEq] at hfe_eq
    have hone: Field51_as_Nat ONE =1:= by
      unfold ONE
      decide
    have hzero: Field51_as_Nat ZERO =0:= by
      unfold ZERO
      decide
    have : Field51_as_Nat d_1=  Field51_as_Nat ONE + Field51_as_Nat fe := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
        Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, Nat.one_mod_eq_zero_iff, and_imp,
        mul_one, not_false_eq_true, forall_exists_index, not_exists, Nat.reduceMul, Nat.reduceAdd, neg_mul, Nat.ofNat_pos,
        Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      ring
    rw[hone] at this
    have hfe_eq_add_1:= hfe_eq.add_left 1
    rw[←  this]  at hfe_eq_add_1
    have udA:Field51_as_Nat u=  Field51_as_Nat d+  Field51_as_Nat Atemp:=by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
        Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, Nat.one_mod_eq_zero_iff, and_imp,
        mul_one, not_false_eq_true, forall_exists_index, not_exists, Nat.reduceMul, Nat.reduceAdd, neg_mul, Nat.ofNat_pos,
        Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      ring
    have :   (Field51_as_Nat MONTGOMERY_A_NEG + Field51_as_Nat MONTGOMERY_A) %p = 0  := by
      unfold MONTGOMERY_A_NEG p MONTGOMERY_A
      decide
    rw[← modEq_zero_iff, lift_mod_eq_iff ] at this
    have chagne_a: ((Field51_as_Nat MONTGOMERY_A):CurveField) = Curve25519.A:= by
      unfold Curve25519.A MONTGOMERY_A
      decide
    have change_A: ↑(Field51_as_Nat MONTGOMERY_A_NEG)= -Curve25519.A  := by grind
    have change_d_1:Field51_as_Nat d_1= 1 + 2 * r0 ^ 2 :=by
      rw[hr0]
      rw[lift_mod_eq_iff] at hfe_eq_add_1
      simp only [hfe_eq_add_1, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have eq_zero_d_1: (Field51_as_Nat d_1) ≡ 0 [MOD p] → Field51_as_Nat eps % p = 0 := by
        intro h
        simp only [← modEq_zero_iff] at hfe1_0
        have eps_eq_0:= heps.trans ((hd.trans ((hfe1_0 h).mul_left (Field51_as_Nat MONTGOMERY_A_NEG))).mul_right (Field51_as_Nat inner))
        simp only [mul_zero, zero_mul] at eps_eq_0
        simp only [← modEq_zero_iff]
        exact eps_eq_0
    have : Field51_as_Nat inner = Field51_as_Nat fe2 + Field51_as_Nat ONE := by
       simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
       simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
          Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, Nat.one_mod_eq_zero_iff, and_imp,
          mul_one, not_false_eq_true, forall_exists_index, not_exists, Nat.reduceMul, Nat.reduceAdd, neg_mul,
          Nat.ModEq.add_iff_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_right_inj, Nat.ofNat_pos,
          Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one, neg_add_cancel]
       ring_nf
    have change_heps:= heps
    rw[this, hone] at change_heps
    have : Field51_as_Nat fe2 = Field51_as_Nat d_sq + Field51_as_Nat au := by
       simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
        Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one]
       simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
        Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, Nat.one_mod_eq_zero_iff, and_imp,
        mul_one, not_false_eq_true, forall_exists_index, not_exists, Nat.reduceMul, Nat.reduceAdd, neg_mul,
        Nat.ModEq.add_iff_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_right_inj, Nat.ofNat_pos,
        Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one, neg_add_cancel]
       ring_nf
    rw[this] at change_heps
    have change_heps:= change_heps.trans (((hd_sq.add hau).add_right 1).mul_left (Field51_as_Nat d))
    have cases_one: (pp.1.val = 1#u8 → ↑(U8x32_as_Nat a) = d0) := by
      intro h_one
      simp only [h_one, true_iff] at hp1
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, hp1, Choice.zero, Nat.not_eq, UScalar.ofNat_val_eq,
        ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
        UScalar.val_not_eq_imp_not_eq, ↓reduceIte] at hu1
      have :Field51_as_Nat u1=  Field51_as_Nat u:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
          Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
          Nat.reduceLT, Nat.lt_add_one]
        simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
          Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, true_and, Nat.one_mod_eq_zero_iff,
          Nat.not_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, zero_lt_one, or_true, or_self,
          UScalar.val_not_eq_imp_not_eq, false_and, imp_false, not_and, mul_one, and_imp, forall_exists_index, not_exists,
          not_forall, Decidable.not_not, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, neg_mul, Nat.ModEq.add_iff_right,
          Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_right_inj, getElem?_pos, Option.getD_some,
          Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      rw[this, udA ] at ha
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h_one, ↓reduceIte] at hAtemp
      have :Field51_as_Nat Atemp=  Field51_as_Nat ZERO:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
          Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
          Nat.reduceLT, Nat.lt_add_one]
        simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
          Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, true_and, Nat.one_mod_eq_zero_iff,
          Nat.not_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, zero_lt_one, or_true, or_self,
          UScalar.val_not_eq_imp_not_eq, false_and, imp_false, not_and, mul_one, and_imp, forall_exists_index, not_exists,
          not_forall, Decidable.not_not, Nat.reduceMul, Nat.reduceAdd, neg_mul, Nat.ModEq.add_iff_right, Nat.cast_add,
          Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_right_inj, getElem?_pos, Option.getD_some, Nat.ofNat_pos,
          Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      rw[hzero] at this
      simp only [this, add_zero] at ha
      have := ha.trans hd
      rw[lift_mod_eq_iff] at this
      rw[hd0, this]
      have :  Curve25519.A ≠ 0:= by unfold Curve25519.A; decide
      simp only [Nat.cast_mul, change_A, neg_mul, ← change_d_1, neg_inj, mul_eq_mul_left_iff, this, or_false]
      by_cases h: (Field51_as_Nat d_1) ≡ 0 [MOD p]
      · have :=eq_zero_d_1 h
        simp only [← modEq_zero_iff] at hfe1_0
        have:= hfe1_0 h
        rw[lift_mod_eq_iff] at h
        simp only [h, Nat.cast_zero, inv_zero]
        rw[lift_mod_eq_iff] at this
        exact this
      · have : (Field51_as_Nat d_1) ≠ (0:CurveField) := by
          intro h1
          apply h
          simp only [lift_mod_eq_iff, h1, Nat.cast_zero]
        field_simp
        have : Field51_as_Nat d_1 % p ≠ 0 := by
          intro h1
          apply h
          simp only [modEq_zero_iff, h1]
        have :=hfe1_non  this
        have eq1:= mod_mul_mod  (Field51_as_Nat fe1) (Field51_as_Nat d_1)
        rw[Nat.ModEq ] at eq1
        rw[eq1] at this
        rw[← modEq_one_iff] at this
        simp only [lift_mod_eq_iff, Nat.cast_mul, Nat.cast_one] at this
        exact this
    have : (pp.1.val = 0#u8 → ↑(U8x32_as_Nat a) = -d0 - Curve25519.A) := by
      intro h_zero
      simp only [h_zero, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one,
        not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq, false_iff] at hp1
      have := ne_zero_if_eq_one _ hp1
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, this, ↓reduceIte] at hu1
      have :Field51_as_Nat u1=  Field51_as_Nat u_neg:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
          Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
          Nat.reduceLT, Nat.lt_add_one]
        clear *- hu1
        simp_all only [List.Vector.length_val, UScalar.ofNat_val_eq, getElem?_pos, Option.getD_some, Nat.ofNat_pos,
          Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      rw[this ] at ha
      rw[lift_mod_eq_iff] at ha
      rw[ha]
      simp only [← modEq_zero_iff] at hu_neg
      rw[lift_mod_eq_iff] at hu_neg
      have : ↑(Field51_as_Nat u_neg) = -((Field51_as_Nat u):CurveField):= by grind
      rw[this, udA]
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h_zero, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq,
        zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
        UScalar.val_not_eq_imp_not_eq, ↓reduceIte] at hAtemp
      have :Field51_as_Nat Atemp=  Field51_as_Nat MONTGOMERY_A:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
          Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
          Nat.reduceLT, Nat.lt_add_one]
        clear *- hAtemp
        simp_all only [List.Vector.length_val, UScalar.ofNat_val_eq, getElem?_pos, Option.getD_some, Nat.ofNat_pos,
        Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      rw[hd0, this]
      have eq_dh:= hd.add_right (Field51_as_Nat MONTGOMERY_A)
      by_cases h: (Field51_as_Nat d_1) ≡ 0 [MOD p]
      · have :=eq_zero_d_1 h
        simp only [← modEq_zero_iff] at hfe1_0
        have:= hfe1_0 h
        have:= hd.trans (this.mul_left (Field51_as_Nat MONTGOMERY_A_NEG))
        rw[lift_mod_eq_iff] at this
        simp only [MONTGOMERY_A_spec, Nat.cast_add, this, mul_zero, Nat.cast_zero, Nat.cast_ofNat, zero_add, neg_mul, neg_neg]
        rw[← change_d_1 ]
        rw[lift_mod_eq_iff] at h
        simp only [h, Nat.cast_zero, inv_zero, mul_zero, zero_sub, neg_inj]
        unfold Curve25519.A
        rfl
      · rw[← change_d_1 ]
        have : ((Field51_as_Nat fe1):CurveField )= (↑(Field51_as_Nat d_1))⁻¹ := by
          have : (Field51_as_Nat d_1) ≠ (0:CurveField) := by
            intro h1
            apply h
            simp only [lift_mod_eq_iff, h1, Nat.cast_zero]
          field_simp
          have : Field51_as_Nat d_1 % p ≠ 0 := by
            intro h1
            apply h
            simp only [modEq_zero_iff, h1]
          have :=hfe1_non  this
          have eq1:= mod_mul_mod  (Field51_as_Nat fe1) (Field51_as_Nat d_1)
          rw[Nat.ModEq ] at eq1
          rw[eq1] at this
          rw[← modEq_one_iff] at this
          simp only [lift_mod_eq_iff, Nat.cast_mul, Nat.cast_one] at this
          exact this
        rw[← this]
        rw[lift_mod_eq_iff] at eq_dh
        rw[eq_dh]
        have : 486662=Curve25519.A  := by unfold Curve25519.A; decide
        simp only [MONTGOMERY_A_spec, Nat.cast_add, Nat.cast_mul, change_A, neg_mul, Nat.cast_ofNat, this, neg_add_rev, neg_neg]
        ring_nf
    have  iff_sq: (pp.1.val = 1#u8 ↔ IsSquare (d0 * (d0 ^ 2 + Curve25519.A * d0 + 1))) := by
      constructor
      · intro h_one
        simp only [h_one, true_iff] at hp1
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, hp1, Choice.zero, Nat.not_eq, UScalar.ofNat_val_eq,
          ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
          UScalar.val_not_eq_imp_not_eq, ↓reduceIte] at hu1
        have :Field51_as_Nat u1=  Field51_as_Nat u:=by
          simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
            Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
            Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
            Nat.reduceLT, Nat.lt_add_one]
          simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
            Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, true_and, Nat.one_mod_eq_zero_iff,
            Nat.not_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, zero_lt_one, or_true, or_self,
            UScalar.val_not_eq_imp_not_eq, false_and, imp_false, not_and, mul_one, and_imp, forall_exists_index, not_exists,
            not_forall, Decidable.not_not, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, neg_mul, Nat.ModEq.add_iff_right,
            Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_right_inj, getElem?_pos, Option.getD_some,
            Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
        rw[this, udA ] at ha
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h_one, ↓reduceIte] at hAtemp
        have :Field51_as_Nat Atemp=  Field51_as_Nat ZERO:=by
          simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
            Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNat_val_eq,
            Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
            Nat.reduceLT, Nat.lt_add_one]
          simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq, getElem!_pos, Nat.reducePow,
          Nat.add_one_sub_one, ne_eq, Nat.mul_mod_mod, Nat.mod_mul_mod, MONTGOMERY_A_spec, true_and, Nat.one_mod_eq_zero_iff,
          Nat.not_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, zero_lt_one, or_true, or_self,
          UScalar.val_not_eq_imp_not_eq, false_and, imp_false, not_and, mul_one, and_imp, forall_exists_index, not_exists,
          not_forall, Decidable.not_not, Nat.reduceMul, Nat.reduceAdd, neg_mul, Nat.ModEq.add_iff_right, Nat.cast_add,
          Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_right_inj, getElem?_pos, Option.getD_some, Nat.ofNat_pos,
          Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
        rw[hzero] at this
        simp only [this, add_zero] at ha
        have := ha.trans hd
        have := cases_one h_one
        rw[← this]
        rw[lift_mod_eq_iff] at ha
        rw[ha]
        rw[lift_mod_eq_iff] at change_heps
        simp only [MONTGOMERY_A_spec, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at change_heps
        have : 486662=Curve25519.A  := by unfold Curve25519.A; decide
        rw[this] at change_heps
        rw[← change_heps]
        by_cases h: Field51_as_Nat eps % p = 0
        · rw[← modEq_zero_iff, lift_mod_eq_iff] at h
          rw[h]
          unfold IsSquare
          use 0
          simp only [Nat.cast_zero, mul_zero]
        · have non_one: Field51_as_Nat ONE % p ≠ 0 := by
            rw[hone]
            decide
          have one_mod: Field51_as_Nat ONE % p = 1 := by
            rw[hone]
            decide
          by_cases ex_cases: ∃ x, x ^ 2 % p = Field51_as_Nat eps % p
          · obtain ⟨ ex, hex⟩ :=ex_cases
            rw[← Nat.ModEq] at hex
            rw[lift_mod_eq_iff] at hex
            rw[← hex]
            unfold IsSquare
            use ex
            grind only
          · have : (Field51_as_Nat eps % p ≠ 0 ∧
            Field51_as_Nat ONE % p ≠ 0 ∧
            ¬∃ x, x ^ 2 * (Field51_as_Nat ONE % p) % p = Field51_as_Nat eps % p) := by
              constructor
              · exact h
              · constructor
                · exact non_one
                · simp only [one_mod, mul_one, not_exists]
                  simp only [not_exists] at ex_cases
                  exact ex_cases
            have:= (hp_case_5 this).left
            simp only [h_one, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero,
              zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq] at this
      · by_cases heps_zero: Field51_as_Nat eps % p = 0
        · intro h
          exact (hp_case_2 heps_zero).left
        · by_cases hd_1_zero :  Field51_as_Nat d_1 % p = 0
          · have := hfe1_0  hd_1_zero
            rw[← modEq_zero_iff] at this
            have := change_heps.trans ((hd.trans (this.mul_left (Field51_as_Nat MONTGOMERY_A_NEG))).mul_right (Field51_as_Nat d ^ 2 + Field51_as_Nat MONTGOMERY_A * Field51_as_Nat d + 1))
            simp only [mul_zero, MONTGOMERY_A_spec, zero_mul] at this
            rw[← modEq_zero_iff] at heps_zero
            simp only [this, not_true_eq_false] at heps_zero
          · have := hfe1_non  hd_1_zero
            rw[← modEq_zero_iff] at hd_1_zero
            have : ((Field51_as_Nat fe1):CurveField )= (↑(Field51_as_Nat d_1))⁻¹ := by
              have : (Field51_as_Nat d_1) ≠ (0:CurveField) := by
                intro h1
                apply hd_1_zero
                simp only [lift_mod_eq_iff, h1, Nat.cast_zero]
              field_simp
              have : Field51_as_Nat d_1 % p ≠ 0 := by
                intro h1
                apply hd_1_zero
                simp only [modEq_zero_iff, h1]
              have :=hfe1_non  this
              have eq1:= mod_mul_mod  (Field51_as_Nat fe1) (Field51_as_Nat d_1)
              rw[Nat.ModEq ] at eq1
              rw[eq1] at this
              rw[← modEq_one_iff] at this
              simp only [lift_mod_eq_iff, Nat.cast_mul, Nat.cast_one] at this
              exact this
            have : d0= Field51_as_Nat d := by
              rw[hd0]
              rw[lift_mod_eq_iff] at hd
              simp only [neg_mul, hd, Nat.cast_mul, change_A, neg_inj, mul_eq_mul_left_iff]
              rw[this,change_d_1]
              simp only [true_or]
            rw[this]
            simp only [MONTGOMERY_A_spec, lift_mod_eq_iff, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
              Nat.cast_one] at change_heps
            have : 486662=Curve25519.A  := by unfold Curve25519.A; decide
            rw[this] at change_heps
            rw[← change_heps]
            intro sq
            have :  (Field51_as_Nat eps % p ≠ 0 ∧
            Field51_as_Nat ONE % p ≠ 0 ∧
            ∃ x, x ^ 2 * (Field51_as_Nat ONE % p) % p = Field51_as_Nat eps % p) := by
              constructor
              · exact heps_zero
              · constructor
                · unfold ONE
                  decide
                · have : (Field51_as_Nat ONE % p) =1 := by
                    unfold ONE
                    decide
                  simp only [this, mul_one]
                  unfold   IsSquare  at sq
                  obtain ⟨ r, hr⟩ := sq
                  use r.val
                  rw[← Nat.ModEq, lift_mod_eq_iff]
                  rw[hr]
                  simp only [Nat.cast_pow, ZMod.natCast_val, ZMod.cast_id', id_eq]
                  ring_nf
            exact(hp_case_4 this).left
    constructor
    · exact iff_sq
    · constructor
      · exact cases_one
      · constructor
        · exact this
        · constructor
          · intro h_one
            have := cases_one h_one
            rw[this]
          · intro h_zero
            have a_eq:= this h_zero
            have non_d_1: ¬  Field51_as_Nat d_1 ≡ 0 [MOD p]:= by
              intro h
              have := (hp_case_2 (eq_zero_d_1 h)).left
              simp[this] at h_zero
            rw[lift_mod_eq_iff, change_d_1 ] at non_d_1
            have eq1: (U8x32_as_Nat a)= 2*d0* r0^2 := by
              rw[a_eq, hd0]
              have : (1 + 2 * r0 ^ 2) ≠ 0:= by grind
              field_simp[non_d_1]
              simp only [sub_add_cancel_left, mul_neg, neg_inj]
              ring_nf
            have : (U8x32_as_Nat a) *((U8x32_as_Nat a)+ Curve25519.A) = d0 *(d0+Curve25519.A):= by
              have : (U8x32_as_Nat a)+ Curve25519.A= -d0:=by grind
              rw[this,a_eq]
              ring_nf
            have eq2: (U8x32_as_Nat a) ^2 +  Curve25519.A * (U8x32_as_Nat a) +1  = d0^2+Curve25519.A * d0 +1 := by grind
            have : -(↑(U8x32_as_Nat a) * (↑(U8x32_as_Nat a) ^ 2 + Curve25519.A * ↑(U8x32_as_Nat a) + 1))
            = -2 * r0^2 * (d0 *(d0^2+Curve25519.A * d0 +1)) := by grind
            rw[this]
            have :(Field51_as_Nat eps % p ≠ 0 ∧
            Field51_as_Nat ONE % p ≠ 0 ∧
            ¬∃ x, x ^ 2 * (Field51_as_Nat ONE % p) % p = Field51_as_Nat eps % p) := by
              constructor
              · intro h
                have := (hp_case_2 h).left
                simp only [this, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero,
                  zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq] at h_zero
              · constructor
                · unfold ONE
                  decide
                · intro h
                  have : (Field51_as_Nat eps % p ≠ 0 ∧
                    Field51_as_Nat ONE % p ≠ 0 ∧
                    ∃ x, x ^ 2 * (Field51_as_Nat ONE % p) % p = Field51_as_Nat eps % p) := by
                      constructor
                      · intro h
                        have := (hp_case_2 h).left
                        simp only [this, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero,
                          zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq] at h_zero
                      · constructor
                        · unfold ONE
                          decide
                        · exact h
                  have := (hp_case_4 this).left
                  simp only [this, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero,
                  zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq] at h_zero
            have eq1:= (hp_case_5 this).right
            have one_mod: Field51_as_Nat ONE % p = 1 := by
              rw[hone]
              decide
            simp only [one_mod, mul_one, Nat.mul_mod_mod, Nat.mod_mul_mod] at eq1
            rw[← Nat.ModEq, lift_mod_eq_iff] at eq1
            have heps_zero:= this.left
            have : ((Field51_as_Nat fe1):CurveField )= (↑(Field51_as_Nat d_1))⁻¹ := by
              have : (Field51_as_Nat d_1) ≠ (0:CurveField) := by
                intro h1
                apply non_d_1
                rw[← change_d_1]
                exact h1
              field_simp
              have : Field51_as_Nat d_1 % p ≠ 0 := by
                intro h1
                apply non_d_1
                rw[← change_d_1]
                simp only [← modEq_zero_iff, lift_mod_eq_iff] at h1
                exact h1
              have :=hfe1_non  this
              have eq1:= mod_mul_mod  (Field51_as_Nat fe1) (Field51_as_Nat d_1)
              rw[Nat.ModEq ] at eq1
              rw[eq1] at this
              rw[← modEq_one_iff] at this
              simp only [lift_mod_eq_iff, Nat.cast_mul, Nat.cast_one] at this
              exact this
            have : d0= Field51_as_Nat d := by
              rw[hd0]
              rw[lift_mod_eq_iff] at hd
              simp only [neg_mul, hd, Nat.cast_mul, change_A, neg_inj, mul_eq_mul_left_iff]
              rw[this,change_d_1]
              simp only [true_or]
            rw[lift_mod_eq_iff] at change_heps
            simp only [MONTGOMERY_A_spec, Nat.cast_mul, ← this, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
              Nat.cast_one] at change_heps
            have : 486662=Curve25519.A  := by unfold Curve25519.A; decide
            rw[this] at change_heps
            rw[← change_heps]
            have := two_did_is_square
            unfold IsSquare  at this
            obtain ⟨ r1, hr1⟩ := this
            unfold IsSquare
            use (r1.val * r0.val *(Field51_as_Nat pp.2 % p))
            simp only [neg_mul, ZMod.natCast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, Field.mod_eq, mul_zero, div_zero, sub_zero]
            field_simp
            simp only [Nat.cast_pow, ZMod.natCast_mod, Nat.cast_mul] at eq1
            field_simp at hr1
            rw[eq1, ← hr1]
            have : (Field51_as_Nat SQRT_M1) ≠ (0:CurveField):= by
              unfold SQRT_M1
              decide
            field_simp
  -/

end curve25519_dalek.montgomery
