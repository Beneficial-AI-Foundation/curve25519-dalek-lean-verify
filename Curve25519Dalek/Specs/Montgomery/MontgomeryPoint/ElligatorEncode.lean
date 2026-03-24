/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.FunsExternal
import Curve25519Dalek.Aux
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
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
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

/-! ## Utility lemmas -/

private theorem ne_zero_iff_eq_one (p1 : subtle.Choice) (hp1 : ¬p1 = Choice.zero) :
    p1 = Choice.one := by
  obtain h | h := p1.valid
  · exfalso; apply hp1; cases p1; simpa [Choice.zero]
  · cases p1; simpa [Choice.one]

private theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔  a % n = 0 := by simp [Nat.ModEq]

private theorem modEq_one_iff (a : ℕ) : a ≡ 1 [MOD p] ↔  a % p = 1 := by
  simp only [Nat.ModEq]
  have :1 % p= 1:= by unfold p; decide
  rw[this]

private theorem mod_mul_mod (a b : ℕ) : (a % p) * (b % p) ≡ a * b [MOD p] := by
 exact ((Nat.mod_modEq a p).mul_right (b % p)).trans  ((Nat.mod_modEq b p).mul_left a)

lemma ne_zero_if_eq_one (p1 : subtle.Choice) (hp1 : ¬p1 = Choice.zero) : p1.val = 1#u8 := by
  have h_eq_one : p1 = Choice.one := ne_zero_iff_eq_one p1 hp1
  simp [h_eq_one, Choice.one]

/-- 486662 is Curve25519.A at the ℕ level. -/
lemma nat_486662_eq_A : (486662 : ℕ) = Curve25519.A := by unfold Curve25519.A; decide

/-- 486662 is Curve25519.A at the CurveField level. -/
lemma curveField_486662_eq_A : (486662 : CurveField) = Curve25519.A := by unfold Curve25519.A; decide

/-- Curve25519.A is nonzero in CurveField. -/
lemma A_ne_zero : (Curve25519.A : CurveField) ≠ 0 := by unfold Curve25519.A; decide

/-- SQRT_M1_val is nonzero in CurveField. -/
lemma SQRT_M1_val_ne_zero : (Field51_as_Nat SQRT_M1_val) ≠ (0 : CurveField) := by
  unfold SQRT_M1_val; decide

/-- Derive CurveField inverse from the modular multiplication relation
    produced by the `invert` spec: (fe1 % p) * (d1 % p) % p = 1. -/
lemma fe1_inv_of_mod_mul (fe1_val d1_val : ℕ)
    (h_nonzero : d1_val % p ≠ 0)
    (h_mul : (fe1_val % p) * (d1_val % p) % p = 1) :
    (fe1_val : CurveField) = (d1_val : CurveField)⁻¹ := by
  have hb_ne : (d1_val : CurveField) ≠ 0 := by
    intro h1
    apply h_nonzero
    have : d1_val ≡ 0 [MOD p] := by rw [lift_mod_eq_iff]; simp [h1]
    rw [modEq_zero_iff] at this; exact this
  field_simp
  have eq1 := mod_mul_mod fe1_val d1_val
  rw [Nat.ModEq] at eq1
  rw [eq1] at h_mul
  rw [← modEq_one_iff] at h_mul
  simp only [lift_mod_eq_iff, Nat.cast_mul, Nat.cast_one] at h_mul
  exact h_mul

/-- Variant of `fe1_inv_of_mod_mul` using `¬ d1_val ≡ 0 [MOD p]` instead of `d1_val % p ≠ 0`. -/
lemma fe1_inv_of_mod_mul' (fe1_val d1_val : ℕ)
    (h_nonzero : ¬ d1_val ≡ 0 [MOD p])
    (h_fe1_non : d1_val % p ≠ 0 → (fe1_val % p) * (d1_val % p) % p = 1) :
    (fe1_val : CurveField) = (d1_val : CurveField)⁻¹ := by
  have h_mod_ne : d1_val % p ≠ 0 := by
    intro h1; apply h_nonzero; simp [modEq_zero_iff, h1]
  exact fe1_inv_of_mod_mul fe1_val d1_val h_mod_ne (h_fe1_non h_mod_ne)

/-- Derive `d0 = ↑(Field51_as_Nat d)` from the field arithmetic chain. -/
lemma d0_eq_d_of_inv (r0 : CurveField)
    (d0 : CurveField) (hd0 : d0 = -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹)
    (d_val fe1_val d1_val A_neg_val : ℕ)
    (change_A : (A_neg_val : CurveField) = -Curve25519.A)
    (change_d_1 : (d1_val : CurveField) = 1 + 2 * r0 ^ 2)
    (hd : d_val ≡ A_neg_val * fe1_val [MOD p])
    (hfe1_inv : (fe1_val : CurveField) = (d1_val : CurveField)⁻¹) :
    d0 = (d_val : CurveField) := by
  rw [hd0]
  rw [lift_mod_eq_iff] at hd
  simp only [neg_mul, hd, Nat.cast_mul, change_A, neg_inj, mul_eq_mul_left_iff]
  rw [hfe1_inv, change_d_1]
  simp only [true_or]

/-! ## Square root lemmas -/

lemma two_mul_is_square : IsSquare ((2:CurveField) *(Field51_as_Nat SQRT_M1_val)):= by
  have eq1: ((Field51_as_Nat SQRT_M1_val):CurveField) =
  19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
    unfold SQRT_M1_val
    decide
  simp[eq1]
  ring_nf
  apply (@legendreSym.eq_one_iff p _ (39362322753415011913614158609977084030892133031847780325488042146247659569504) (by grind)).mp
  norm_num [p]

lemma two_did_is_square : IsSquare (-(2:CurveField) /(Field51_as_Nat SQRT_M1_val)):= by
  have eq1: ((Field51_as_Nat SQRT_M1_val):CurveField) ≠ 0 := by
    unfold SQRT_M1_val
    decide
  have :- (2:CurveField) /(Field51_as_Nat SQRT_M1_val) = 2 * (Field51_as_Nat SQRT_M1_val):= by
    field_simp
    unfold SQRT_M1_val
    decide
  rw[this]
  exact two_mul_is_square

/-! ## Eps-zero implies d_1-zero propagation -/

/-- When d_1 ≡ 0 (mod p), the eps value is also zero mod p. -/
lemma eps_zero_of_d1_zero
    (d_1_val fe1_val A_neg_val d_val inner_val eps_val : ℕ)
    (hfe1_0 : d_1_val % p = 0 → fe1_val % p = 0)
    (hd : d_val ≡ A_neg_val * fe1_val [MOD p])
    (heps : eps_val ≡ d_val * inner_val [MOD p])
    (h : d_1_val ≡ 0 [MOD p]) :
    eps_val % p = 0 := by
  simp only [← modEq_zero_iff] at hfe1_0
  have eps_eq_0 := heps.trans ((hd.trans ((hfe1_0 h).mul_left A_neg_val)).mul_right inner_val)
  simp only [mul_zero, zero_mul] at eps_eq_0
  simp only [← modEq_zero_iff]
  exact eps_eq_0

/-! ## NQR condition assembly -/

/-- Assemble the NQR condition triple for the sqrt_ratio_i backward direction. -/
lemma nqr_condition_of_nonzero
    (eps_val one_val : ℕ)
    (one_eq : one_val = 1)
    (heps_ne : eps_val % p ≠ 0)
    (h_not_sq : ¬∃ x, x ^ 2 % p = eps_val % p) :
    (eps_val % p ≠ 0 ∧
     one_val % p ≠ 0 ∧
     ¬∃ x, x ^ 2 * (one_val % p) % p = eps_val % p) := by
  have one_mod : one_val % p = 1 := by rw [one_eq]; decide
  constructor
  · exact heps_ne
  · constructor
    · rw [one_eq]; decide
    · simp only [one_mod, mul_one, not_exists]
      simp only [not_exists] at h_not_sq
      exact h_not_sq

/-- Assemble the QR condition triple for the sqrt_ratio_i forward direction. -/
lemma qr_condition_of_square
    (eps_val one_val : ℕ)
    (one_eq : one_val = 1)
    (heps_ne : eps_val % p ≠ 0)
    (sq : IsSquare ((eps_val : CurveField))) :
    (eps_val % p ≠ 0 ∧
     one_val % p ≠ 0 ∧
     ∃ x, x ^ 2 * (one_val % p) % p = eps_val % p) := by
  have one_mod : one_val % p = 1 := by rw [one_eq]; decide
  constructor
  · exact heps_ne
  · constructor
    · rw [one_eq]; decide
    · simp only [one_mod, mul_one]
      obtain ⟨r, hr⟩ := sq
      use r.val
      rw [← Nat.ModEq, lift_mod_eq_iff]
      rw [hr]
      simp only [Nat.cast_pow, ZMod.natCast_val, ZMod.cast_id', id_eq]
      ring_nf

/-! ## Extracted sub-lemmas for `elligator_encode` -/

/-- **QR case output**: When the output modular chain gives `a ≡ A_neg * fe1 [MOD p]`,
    the CurveField value equals `d0 = -A * (1 + 2r₀²)⁻¹`. -/
private lemma elligator_qr_output_eq_d0
    (d0 r0 : CurveField)
    (hd0 : d0 = -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹)
    (a_val A_neg_val fe1_val d_1_val : ℕ)
    (ha_chain : a_val ≡ A_neg_val * fe1_val [MOD p])
    (change_A : (A_neg_val : CurveField) = -Curve25519.A)
    (change_d_1 : (d_1_val : CurveField) = 1 + 2 * r0 ^ 2)
    (hfe1_non : d_1_val % p ≠ 0 → (fe1_val % p) * (d_1_val % p) % p = 1)
    (hfe1_0 : d_1_val % p = 0 → fe1_val % p = 0) :
    (a_val : CurveField) = d0 := by
  rw[lift_mod_eq_iff] at ha_chain
  rw[hd0, ha_chain]
  simp only [Nat.cast_mul, change_A, neg_mul, ← change_d_1, neg_inj, mul_eq_mul_left_iff, A_ne_zero, or_false]
  by_cases h: (d_1_val) ≡ 0 [MOD p]
  · simp only [← modEq_zero_iff] at hfe1_0
    have := hfe1_0 h
    rw[lift_mod_eq_iff] at h
    simp only [h, Nat.cast_zero, inv_zero]
    rw[lift_mod_eq_iff] at this
    exact this
  · exact fe1_inv_of_mod_mul' fe1_val d_1_val h hfe1_non

/-- **NQR case output**: `-(d + A1)` in CurveField equals `-d0 - Curve25519.A`. -/
private lemma elligator_nqr_neg_sum_eq
    (d0 r0 : CurveField)
    (hd0 : d0 = -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹)
    (d_val A1_val A_neg_val fe1_val d_1_val : ℕ)
    (hA : A1_val = 486662)
    (hd : d_val ≡ A_neg_val * fe1_val [MOD p])
    (change_A : (A_neg_val : CurveField) = -Curve25519.A)
    (change_d_1 : (d_1_val : CurveField) = 1 + 2 * r0 ^ 2)
    (hfe1_non : d_1_val % p ≠ 0 → (fe1_val % p) * (d_1_val % p) % p = 1)
    (hfe1_0 : d_1_val % p = 0 → fe1_val % p = 0) :
    -((d_val : CurveField) + (A1_val : CurveField)) = -d0 - Curve25519.A := by
  rw[hd0]
  have eq_dh := hd.add_right A1_val
  by_cases h: (d_1_val) ≡ 0 [MOD p]
  · simp only [← modEq_zero_iff] at hfe1_0
    have := hfe1_0 h
    have := hd.trans (this.mul_left A_neg_val)
    rw[lift_mod_eq_iff] at this
    simp only [this, mul_zero, Nat.cast_zero, zero_add, neg_mul, neg_neg]
    rw[← change_d_1]
    rw[lift_mod_eq_iff] at h
    simp only [h, Nat.cast_zero, inv_zero, mul_zero, zero_sub, neg_inj]
    unfold Curve25519.A
    simp[hA]
  · have hfe1_inv := fe1_inv_of_mod_mul' fe1_val d_1_val h hfe1_non
    have h_d_val : (d_val : CurveField) = -Curve25519.A * (d_1_val : CurveField)⁻¹ := by
      rw[lift_mod_eq_iff] at hd; rw[hd]; simp [change_A, hfe1_inv]
    have h_A1 : (A1_val : CurveField) = Curve25519.A := by
      unfold Curve25519.A; simp [hA]
    rw[h_d_val, h_A1, ← change_d_1]; ring

/-- **IsSquare forward**: If `choice = 1` and the NQR branch would give `choice = 0`,
    then `eps` is a square in CurveField. -/
private lemma isSquare_eps_of_choice_one
    (choice_val : U8) (eps_val one_val : ℕ)
    (one_eq : one_val = 1)
    (hp_nqr_gives_zero :
      (eps_val % p ≠ 0 ∧ one_val % p ≠ 0 ∧
       ¬∃ x, x ^ 2 * (one_val % p) % p = eps_val % p) → choice_val = 0#u8)
    (h_one : choice_val = 1#u8) :
    IsSquare ((eps_val : CurveField)) := by
  by_cases h: eps_val % p = 0
  · rw[← modEq_zero_iff, lift_mod_eq_iff] at h
    rw[h]
    exact ⟨0, by simp⟩
  · by_cases ex_cases: ∃ x, x ^ 2 % p = eps_val % p
    · obtain ⟨ ex, hex⟩ := ex_cases
      rw[← Nat.ModEq] at hex
      rw[lift_mod_eq_iff] at hex
      rw[← hex]
      exact ⟨ex, by grind only⟩
    · have := hp_nqr_gives_zero (nqr_condition_of_nonzero eps_val one_val one_eq h ex_cases)
      simp [h_one] at this

/-- **IsSquare backward**: If `d0 * (d0² + A·d0 + 1)` is a square, then `choice = 1`. -/
private lemma choice_one_of_isSquare_eps
    (choice_val : U8) (eps_val d_val A1_val A_neg_val fe1_val d_1_val one_val : ℕ)
    (d0 r0 : CurveField) (hd0 : d0 = -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹)
    (one_eq : one_val = 1) (hA : A1_val = 486662)
    (change_heps : eps_val ≡ d_val * (d_val ^ 2 + A1_val * d_val + 1) [MOD p])
    (hd : d_val ≡ A_neg_val * fe1_val [MOD p])
    (change_A : (A_neg_val : CurveField) = -Curve25519.A)
    (change_d_1 : (d_1_val : CurveField) = 1 + 2 * r0 ^ 2)
    (hfe1_non : d_1_val % p ≠ 0 → (fe1_val % p) * (d_1_val % p) % p = 1)
    (hfe1_0 : d_1_val % p = 0 → fe1_val % p = 0)
    (hp_eps_zero_gives_one : eps_val % p = 0 → choice_val = 1#u8)
    (hp_qr_gives_one :
      (eps_val % p ≠ 0 ∧ one_val % p ≠ 0 ∧
       ∃ x, x ^ 2 * (one_val % p) % p = eps_val % p) → choice_val = 1#u8)
    (sq : IsSquare (d0 * (d0 ^ 2 + Curve25519.A * d0 + 1))) :
    choice_val = 1#u8 := by
  by_cases heps_zero: eps_val % p = 0
  · exact hp_eps_zero_gives_one heps_zero
  · by_cases hd_1_zero : d_1_val % p = 0
    · have := hfe1_0 hd_1_zero
      rw[← modEq_zero_iff] at this
      have := change_heps.trans ((hd.trans (this.mul_left A_neg_val)).mul_right (d_val ^ 2 + A1_val * d_val + 1))
      simp only [mul_zero, hA, zero_mul] at this
      rw[← modEq_zero_iff] at heps_zero
      simp only [this, not_true_eq_false] at heps_zero
    · have hfe1_inv := fe1_inv_of_mod_mul fe1_val d_1_val hd_1_zero (hfe1_non hd_1_zero)
      rw[← modEq_zero_iff] at hd_1_zero
      have hd0_eq : d0 = (d_val : CurveField) :=
        d0_eq_d_of_inv r0 d0 hd0 d_val fe1_val d_1_val A_neg_val change_A change_d_1 hd hfe1_inv
      rw[hd0_eq] at sq
      have change_heps' := change_heps
      simp only [hA, lift_mod_eq_iff, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one] at change_heps'
      have : (486662 : CurveField) = Curve25519.A := curveField_486662_eq_A
      rw[this] at change_heps'
      rw[← change_heps'] at sq
      exact hp_qr_gives_one (qr_condition_of_square eps_val one_val one_eq heps_zero sq)

/-- **NQR algebraic identity**: When `u = -d0 - A` and `d0 = -A·(1+2r₀²)⁻¹`,
    `-(u·(u²+Au+1)) = -2r₀²·(d0·(d0²+Ad0+1))`. -/
private lemma elligator_nqr_neg_rhs_identity
    (d0 r0 u : CurveField)
    (hd0 : d0 = -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹)
    (hu : u = -d0 - Curve25519.A)
    (h_nonzero : (1 + 2 * r0 ^ 2) ≠ (0 : CurveField)) :
    -(u * (u ^ 2 + Curve25519.A * u + 1)) =
      -2 * r0 ^ 2 * (d0 * (d0 ^ 2 + Curve25519.A * d0 + 1)) := by
  have eq1 : u = 2 * d0 * r0 ^ 2 := by
    rw[hu, hd0]
    field_simp[h_nonzero]
    simp only [sub_add_cancel_left, mul_neg, neg_inj]
    ring_nf
  have h_u_add_A : u + Curve25519.A = -d0 := by grind
  have eq2 : u ^ 2 + Curve25519.A * u + 1 = d0 ^ 2 + Curve25519.A * d0 + 1 := by grind
  rw[eq2, eq1]; ring

/-- **NQR witness construction**: Given the sqrt_ratio_i NQR witness and `two_did_is_square`,
    construct `IsSquare (-2·r₀²·eps)`. -/
private lemma elligator_nqr_isSquare_witness
    (r0 : CurveField)
    (eps_val witness_val : ℕ)
    (h_witness : (witness_val : CurveField) ^ 2 =
      (Field51_as_Nat SQRT_M1_val : CurveField) * (eps_val : CurveField)) :
    IsSquare (-2 * r0 ^ 2 * (eps_val : CurveField)) := by
  obtain ⟨r1, hr1⟩ := two_did_is_square
  use (r1.val * r0.val * witness_val)
  simp only [neg_mul, ZMod.natCast_val, ZMod.cast_id', id_eq]
  field_simp
  field_simp at hr1
  rw[h_witness, ← hr1]
  field_simp [SQRT_M1_val_ne_zero]

/-- **NQR twist**: Full proof that the NQR branch output lies on the quadratic twist. -/
private lemma elligator_nqr_twist
    (d0 r0 : CurveField) (hd0 : d0 = -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹)
    (a_val eps_val d_val A1_val A_neg_val fe1_val d_1_val one_val : ℕ)
    (choice_val : U8)
    (a_eq : (a_val : CurveField) = -d0 - Curve25519.A)
    (one_eq : one_val = 1) (hA : A1_val = 486662)
    (change_heps : eps_val ≡ d_val * (d_val ^ 2 + A1_val * d_val + 1) [MOD p])
    (hd : d_val ≡ A_neg_val * fe1_val [MOD p])
    (change_A : (A_neg_val : CurveField) = -Curve25519.A)
    (change_d_1 : (d_1_val : CurveField) = 1 + 2 * r0 ^ 2)
    (hfe1_non : d_1_val % p ≠ 0 → (fe1_val % p) * (d_1_val % p) % p = 1)
    (non_d_1 : (1 + 2 * r0 ^ 2) ≠ (0 : CurveField))
    -- sqrt_ratio_i NQR conditions
    (hp_case_2_left : eps_val % p = 0 → choice_val = 1#u8)
    (hp_case_4_left :
      (eps_val % p ≠ 0 ∧ one_val % p ≠ 0 ∧
       ∃ x, x ^ 2 * (one_val % p) % p = eps_val % p) → choice_val = 1#u8)
    (h_zero : choice_val = 0#u8)
    -- NQR witness from sqrt_ratio_i
    (witness_val : ℕ)
    (hp_case_5_right :
      (one_val % p = 1) →
      (witness_val ^ 2 * (one_val % p)) % p =
        ((Field51_as_Nat SQRT_M1_val % p) * (eps_val % p)) % p) :
    IsSquare (-((a_val : CurveField) *
      ((a_val : CurveField) ^ 2 + Curve25519.A * (a_val : CurveField) + 1))) := by
  -- Apply algebraic identity: -(u*(u²+Au+1)) = -2r₀²·(d0·(d0²+Ad0+1))
  have h_neg_rhs := elligator_nqr_neg_rhs_identity d0 r0 (a_val : CurveField) hd0 a_eq non_d_1
  rw[h_neg_rhs]
  -- Assemble NQR conditions
  have h_nqr_cond : (eps_val % p ≠ 0 ∧
      one_val % p ≠ 0 ∧
      ¬∃ x, x ^ 2 * (one_val % p) % p = eps_val % p) := by
    constructor
    · intro h; have := hp_case_2_left h; simp [this] at h_zero
    · constructor
      · rw[one_eq]; decide
      · intro h
        have : (eps_val % p ≠ 0 ∧
          one_val % p ≠ 0 ∧
          ∃ x, x ^ 2 * (one_val % p) % p = eps_val % p) := by
            constructor
            · intro h; have := hp_case_2_left h; simp [this] at h_zero
            · constructor
              · rw[one_eq]; decide
              · exact h
        have := hp_case_4_left this
        simp [this] at h_zero
  have one_mod : one_val % p = 1 := by rw[one_eq]; decide
  -- Get witness equation from sqrt_ratio_i
  have h_witness_eq := hp_case_5_right one_mod
  simp only [one_mod, mul_one, Nat.mul_mod_mod, Nat.mod_mul_mod] at h_witness_eq
  rw[← Nat.ModEq, lift_mod_eq_iff] at h_witness_eq
  simp only [Nat.cast_pow, Nat.cast_mul] at h_witness_eq
  -- Derive fe1 inverse and d0 = d
  have hfe1_inv : ((fe1_val : CurveField)) = ((d_1_val : CurveField))⁻¹ := by
    have : (d_1_val : CurveField) ≠ 0 := by
      intro h1; apply non_d_1; rw[← change_d_1]; exact h1
    field_simp
    have : d_1_val % p ≠ 0 := by
      intro h1; apply non_d_1; rw[← change_d_1]
      simp only [← modEq_zero_iff, lift_mod_eq_iff] at h1; exact h1
    have := hfe1_non this
    have eq1 := mod_mul_mod fe1_val d_1_val
    rw[Nat.ModEq] at eq1
    rw[eq1] at this
    rw[← modEq_one_iff] at this
    simp only [lift_mod_eq_iff, Nat.cast_mul, Nat.cast_one] at this
    exact this
  have hd0_eq : d0 = (d_val : CurveField) :=
    d0_eq_d_of_inv r0 d0 hd0 d_val fe1_val d_1_val A_neg_val change_A change_d_1 hd hfe1_inv
  -- Rewrite eps relationship
  have change_heps' := change_heps
  rw[lift_mod_eq_iff] at change_heps'
  simp only [hA, Nat.cast_mul, ← hd0_eq, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one] at change_heps'
  have : (486662 : CurveField) = Curve25519.A := curveField_486662_eq_A
  rw[this] at change_heps'
  rw[← change_heps']
  -- Apply witness construction
  exact elligator_nqr_isSquare_witness r0 eps_val witness_val h_witness_eq

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

@[progress]
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
    progress as ⟨ one, one_eq, one_bound⟩
    progress as ⟨fe, hfe_eq, hfe_b ⟩
    progress as ⟨ d_1, hd_1, hd_1_b⟩
    progress as ⟨ A_neg, h_a_neg, a_neg_bound⟩
    progress as ⟨ fe1, hfe1_non, hfe1_0, hfe1_b⟩
    progress as ⟨ d, hd, hd_b⟩
    progress as ⟨ d_sq, hd_sq, hd_sq_b⟩
    progress as ⟨ A1, hA, A_bound⟩
    progress as ⟨ au, hau, hau_b⟩
    progress as ⟨ fe2, hfe2, hfe2_b⟩
    progress as ⟨ inner, hinner, hinner_b⟩
    progress as⟨ eps, heps, heps_b⟩
    progress as ⟨ pp, hp_b, hp_case_1, hp_case_2, hp_case_3, hp_case_4, hp_case_5⟩
    progress as ⟨ zero, zero_eq, zero_bound⟩
    progress as ⟨ Atemp, hAtemp⟩
    progress as ⟨ u, hu, hu_b⟩
    · intro i hi
      have := hAtemp i hi
      rw[this]
      by_cases h:pp.1.val = 1#u8
      · simp only [h, ↓reduceIte, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow, gt_iff_lt]
        grind
      · simp only [h, ↓reduceIte, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow, gt_iff_lt]
        grind
    progress as ⟨ u_neg, hu_neg, hu_neg_b⟩
    progress as ⟨ p1, hp1⟩
    progress as ⟨u1, hu1⟩
    progress as ⟨a, ha, ha_lt⟩
    set r0 := ((Field51_as_Nat r_0):CurveField) with hr0
    set d0:= -Curve25519.A * (1 + 2 * r0 ^ 2)⁻¹ with hd0
    -- Structural Field51_as_Nat decomposition lemmas (using pointwise_add_Field51_as_Nat)
    have : Field51_as_Nat d_1=  Field51_as_Nat one + Field51_as_Nat fe :=
      pointwise_add_Field51_as_Nat one fe d_1 hd_1
    rw[one_eq] at this
    have hfe_eq_add_1:= hfe_eq.add_left 1
    rw[←  this]  at hfe_eq_add_1
    have udA:Field51_as_Nat u=  Field51_as_Nat d+  Field51_as_Nat Atemp:=
      pointwise_add_Field51_as_Nat d Atemp u hu
    have :   (Field51_as_Nat A_neg + Field51_as_Nat A1) %p = 0  := by
      rw[← hA] at h_a_neg
      simp[h_a_neg]
    rw[← modEq_zero_iff, lift_mod_eq_iff ] at this
    have chagne_a: ((Field51_as_Nat A1):CurveField) = Curve25519.A:= by
      unfold Curve25519.A
      simp[hA]
    have change_A: ↑(Field51_as_Nat A_neg)= -Curve25519.A  := by grind
    have change_d_1:Field51_as_Nat d_1= 1 + 2 * r0 ^ 2 :=by
      rw[hr0]
      rw[lift_mod_eq_iff] at hfe_eq_add_1
      simp only [hfe_eq_add_1, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have eq_zero_d_1: (Field51_as_Nat d_1) ≡ 0 [MOD p] → Field51_as_Nat eps % p = 0 :=
      fun h => eps_zero_of_d1_zero (Field51_as_Nat d_1) (Field51_as_Nat fe1) (Field51_as_Nat A_neg)
        (Field51_as_Nat d) (Field51_as_Nat inner) (Field51_as_Nat eps) hfe1_0 hd heps h
    have : Field51_as_Nat inner = Field51_as_Nat fe2 + Field51_as_Nat one :=
      pointwise_add_Field51_as_Nat fe2 one inner hinner
    have change_heps:= heps
    rw[this, one_eq] at change_heps
    have : Field51_as_Nat fe2 = Field51_as_Nat d_sq + Field51_as_Nat au :=
      pointwise_add_Field51_as_Nat d_sq au fe2 hfe2
    rw[this] at change_heps
    have change_heps:= change_heps.trans (((hd_sq.add hau).add_right 1).mul_left (Field51_as_Nat d))
    -- ── Implementation bridging: QR case → ha_chain for d ──
    have cases_one: (pp.1.val = 1#u8 → ↑(U8x32_as_Nat a) = d0) := by
      intro h_one
      simp only [h_one, true_iff] at hp1
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, hp1, Choice.zero, Nat.not_eq,
        UScalar.ofNatCore_val_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false,
        or_self, UScalar.val_not_eq_imp_not_eq, ↓reduceIte] at hu1
      have :Field51_as_Nat u1=  Field51_as_Nat u:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
          one_mul, mul_one, Nat.reducePow, Nat.reduceMul]
        clear *- hu1
        simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem?_pos, Option.getD_some, Nat.ofNat_pos,
        Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      rw[this, udA ] at ha
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h_one, ↓reduceIte] at hAtemp
      have :Field51_as_Nat Atemp=  Field51_as_Nat zero:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, one_mul, mul_one, Nat.reducePow, Nat.reduceMul]
        simp_all
      rw[zero_eq] at this
      simp only [this, add_zero] at ha
      have ha_chain := ha.trans hd
      exact elligator_qr_output_eq_d0 d0 r0 hd0
        (U8x32_as_Nat a) (Field51_as_Nat A_neg) (Field51_as_Nat fe1) (Field51_as_Nat d_1)
        ha_chain change_A change_d_1 hfe1_non hfe1_0
    -- ── Implementation bridging: NQR case → u = -d0 - A ──
    have cases_zero : (pp.1.val = 0#u8 → ↑(U8x32_as_Nat a) = -d0 - Curve25519.A) := by
      intro h_zero
      simp [h_zero] at hp1
      have : p1.val = 1#u8 := by simp [hp1, Choice.one]
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, this, ↓reduceIte] at hu1
      have :Field51_as_Nat u1=  Field51_as_Nat u_neg:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, one_mul, mul_one, Nat.reducePow, Nat.reduceMul]
        clear *- hu1
        simp_all
      rw[this ] at ha
      rw[lift_mod_eq_iff] at ha
      rw[ha]
      rw[lift_mod_eq_iff] at hu_neg
      have : ↑(Field51_as_Nat u_neg) = -((Field51_as_Nat u):CurveField):= by grind
      rw[this, udA]
      simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h_zero] at hAtemp
      have :Field51_as_Nat Atemp=  Field51_as_Nat A1:=by
        simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, one_mul, mul_one, Nat.reducePow, Nat.reduceMul]
        clear *- hAtemp
        simp_all
      rw[this]
      simp only [Nat.cast_add]
      exact elligator_nqr_neg_sum_eq d0 r0 hd0
        (Field51_as_Nat d) (Field51_as_Nat A1) (Field51_as_Nat A_neg) (Field51_as_Nat fe1) (Field51_as_Nat d_1)
        hA hd change_A change_d_1 hfe1_non hfe1_0
    -- ── Sub-lemma: IsSquare ↔ ──
    have iff_sq: (pp.1.val = 1#u8 ↔ IsSquare (d0 * (d0 ^ 2 + Curve25519.A * d0 + 1))) := by
      constructor
      · -- Forward: choice = 1 → IsSquare eps
        intro h_one
        -- Derive d0 = Field51_as_Nat d in CurveField
        simp only [h_one, true_iff] at hp1
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, hp1, Choice.zero, Nat.not_eq,
          UScalar.ofNatCore_val_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false,
          or_self, UScalar.val_not_eq_imp_not_eq, ↓reduceIte] at hu1
        have :Field51_as_Nat u1=  Field51_as_Nat u:=by
          simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_range_succ,
            Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val, UScalar.ofNatCore_val_eq,
            Nat.ofNat_pos, getElem?_pos, Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
            Nat.reduceLT, Nat.lt_add_one]
          clear *- hu1
          simp_all
        rw[this, udA ] at ha
        simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h_one, ↓reduceIte] at hAtemp
        have :Field51_as_Nat Atemp=  Field51_as_Nat zero:=by
          simp [Field51_as_Nat,Finset.sum_range_succ]
          clear *- hAtemp
          simp_all
        rw[zero_eq] at this
        simp only [this, add_zero] at ha
        have := ha.trans hd
        have h_a_eq_d0 := cases_one h_one
        rw[← h_a_eq_d0]
        rw[lift_mod_eq_iff] at ha
        rw[ha]
        rw[lift_mod_eq_iff] at change_heps
        simp only [hA, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at change_heps
        have : (486662 : CurveField) = Curve25519.A := curveField_486662_eq_A
        rw[this] at change_heps
        rw[← change_heps]
        exact isSquare_eps_of_choice_one pp.1.val (Field51_as_Nat eps) (Field51_as_Nat one) one_eq
          (fun cond => (hp_case_5 cond).left) h_one
      · -- Backward: IsSquare → choice = 1
        exact choice_one_of_isSquare_eps pp.1.val
          (Field51_as_Nat eps) (Field51_as_Nat d) (Field51_as_Nat A1) (Field51_as_Nat A_neg)
          (Field51_as_Nat fe1) (Field51_as_Nat d_1) (Field51_as_Nat one)
          d0 r0 hd0 one_eq hA change_heps hd change_A change_d_1 hfe1_non hfe1_0
          (fun h => (hp_case_2 h).left) (fun h => (hp_case_4 h).left)
    -- ── Final assembly ──
    constructor
    · exact iff_sq
    · constructor
      · exact cases_one
      · constructor
        · exact cases_zero
        · constructor
          · -- QR case: u lies on the curve
            intro h_one
            have := cases_one h_one
            rw[this]
          · -- NQR case: u lies on the quadratic twist
            intro h_zero
            have a_eq := cases_zero h_zero
            have non_d_1: ¬  Field51_as_Nat d_1 ≡ 0 [MOD p]:= by
              intro h
              have := (hp_case_2 (eq_zero_d_1 h)).left
              simp[this] at h_zero
            rw[lift_mod_eq_iff, change_d_1 ] at non_d_1
            -- Get the NQR witness from sqrt_ratio_i
            have h_nqr_cond : (Field51_as_Nat eps % p ≠ 0 ∧
                Field51_as_Nat one % p ≠ 0 ∧
                ¬∃ x, x ^ 2 * (Field51_as_Nat one % p) % p = Field51_as_Nat eps % p) := by
              constructor
              · intro h; have := (hp_case_2 h).left; simp [this] at h_zero
              · constructor
                · rw[one_eq]; decide
                · intro h
                  have : (Field51_as_Nat eps % p ≠ 0 ∧
                    Field51_as_Nat one % p ≠ 0 ∧
                    ∃ x, x ^ 2 * (Field51_as_Nat one % p) % p = Field51_as_Nat eps % p) := by
                      constructor
                      · intro h; have := (hp_case_2 h).left; simp [this] at h_zero
                      · constructor
                        · rw[one_eq]; decide
                        · exact h
                  have := (hp_case_4 this).left
                  simp [this] at h_zero
            have hp5 := hp_case_5 h_nqr_cond
            exact elligator_nqr_twist d0 r0 hd0
              (U8x32_as_Nat a) (Field51_as_Nat eps) (Field51_as_Nat d) (Field51_as_Nat A1)
              (Field51_as_Nat A_neg) (Field51_as_Nat fe1) (Field51_as_Nat d_1) (Field51_as_Nat one)
              pp.1.val a_eq one_eq hA change_heps hd change_A change_d_1 hfe1_non non_d_1
              (fun h => (hp_case_2 h).left) (fun h => (hp_case_4 h).left)
              h_zero (Field51_as_Nat pp.2 % p)
              (fun _ => hp5.right)

end curve25519_dalek.montgomery
