/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.FunsExternal
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.ONE_MINUS_EDWARDS_D_SQUARED
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EDWARDS_D
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.MINUS_ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SQRT_AD_MINUS_ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EDWARDS_D_MINUS_ONE_SQUARED

/-! # Spec Theorem for `RistrettoPoint::elligator_ristretto_flavor`

Specification and proof for `RistrettoPoint::elligator_ristretto_flavor`.

This function implements the Ristretto Elligator map, which is the MAP function
defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4).

It maps an arbitrary field element s to a valid Ristretto point.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.math
open Edwards curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.ristretto.RistrettoPoint

/-- **Elligator invariant**: the value s1 produced by the Elligator map never satisfies s1² = -1.
This ensures the denominator 1 + s1² is never zero in 𝔽_p.

**Proof sketch** (both cases yield a quadratic in r with non-square discriminant):
- The Elligator map computes r = √(-1)·s², N_s = (r+1)(1-d²), D = (-1-dr)(r+d),
  then applies sqrt_ratio_i(N_s, D) to get s1 satisfying either:
  - **Case A** (square): s1²·D = N_s, so s1²=-1 gives N_s+D = 0.
    Expanding: -(d²+d+1)r² - 2(1+d)r - d = 0 with Δ = -4(d³-d-1), a non-square mod p.
  - **Case B** (non-square): s1²·D = r·N_s, so s1²=-1 gives r·N_s+D = 0.
    Expanding: (1-d-d²)r² - 2d²r - d = 0 with Δ = 4d(d-1)²(d+1).
    Since d is a non-square and (1+d) is a square, d(1+d) is a non-square, so Δ is a non-square.
-/
private lemma elligator_s1_sq_ne_neg_one
    (r_F N_s_F D_F s1_F : CurveField)
    (hNs : N_s_F = (r_F + 1) * (1 - (d : CurveField) ^ 2))
    (hD : D_F = (-1 - (d : CurveField) * r_F) * (r_F + (d : CurveField)))
    (h_cases : s1_F ^ 2 * D_F = N_s_F ∨ s1_F ^ 2 * D_F = r_F * N_s_F)
    : s1_F ^ 2 ≠ -1 := by
  set dd := (d : CurveField) with hdd
  -- The discriminant 4d(d-1)²(d+1) is not a square (d non-square, 1+d square ⟹ d(1+d) non-square)
  have h_disc_not_sq : ¬IsSquare (4 * dd * (dd - 1) ^ 2 * (dd + 1)) := by
    have h_eq : 4 * dd * (dd - 1) ^ 2 * (dd + 1) =
        (Int.cast (4 * (d : ℤ) * ((d : ℤ) - 1) ^ 2 * ((d : ℤ) + 1)) : CurveField) := by
      push_cast; ring
    rw [h_eq]
    exact (legendreSym.eq_neg_one_iff p).mp (by norm_num [d, p])
  intro h_neg1
  rcases h_cases with hA | hB
  · -- Case A: s1² · D = N_s, with s1² = -1 gives N_s + D = 0
    have h_sum : N_s_F + D_F = 0 := by
      have : N_s_F = -D_F := by
        calc N_s_F = s1_F ^ 2 * D_F := hA.symm
          _ = -1 * D_F := by rw [h_neg1]
          _ = -D_F := by ring
      rw [this]; ring
    -- Expand to polynomial in r_F
    have h_expanded : (r_F + 1) * (1 - dd ^ 2) + (-1 - dd * r_F) * (r_F + dd) = 0 := by
      rw [← hNs, ← hD]; exact h_sum
    have h_poly : dd * r_F ^ 2 + 2 * dd ^ 2 * r_F + (dd + dd ^ 2 - 1) = 0 := by
      linear_combination -h_expanded
    -- Complete the square: (2d·r + 2d²)² = 4d(d-1)²(d+1)
    have h_sq : (2 * dd * r_F + 2 * dd ^ 2) ^ 2 = 4 * dd * (dd - 1) ^ 2 * (dd + 1) := by
      have : (2 * dd * r_F + 2 * dd ^ 2) ^ 2 =
        4 * dd * (dd * r_F ^ 2 + 2 * dd ^ 2 * r_F + (dd + dd ^ 2 - 1)) +
        4 * dd * (dd - 1) ^ 2 * (dd + 1) := by ring
      rw [this, h_poly, mul_zero, zero_add]
    exact h_disc_not_sq ⟨2 * dd * r_F + 2 * dd ^ 2, by rw [← sq]; exact h_sq.symm⟩
  · -- Case B: s1² · D = r · N_s, with s1² = -1 gives r · N_s + D = 0
    have h_sum : r_F * N_s_F + D_F = 0 := by
      have : r_F * N_s_F = -D_F := by
        calc r_F * N_s_F = s1_F ^ 2 * D_F := hB.symm
          _ = -1 * D_F := by rw [h_neg1]
          _ = -D_F := by ring
      rw [this]; ring
    have h_expanded : r_F * ((r_F + 1) * (1 - dd ^ 2)) + (-1 - dd * r_F) * (r_F + dd) = 0 := by
      rw [← hNs, ← hD]; exact h_sum
    have h_poly : (1 - dd - dd ^ 2) * r_F ^ 2 - 2 * dd ^ 2 * r_F - dd = 0 := by
      linear_combination h_expanded
    -- Complete the square: (2(1-d-d²)·r - 2d²)² = 4d(d-1)²(d+1)
    have h_sq : (2 * (1 - dd - dd ^ 2) * r_F - 2 * dd ^ 2) ^ 2 =
        4 * dd * (dd - 1) ^ 2 * (dd + 1) := by
      have : (2 * (1 - dd - dd ^ 2) * r_F - 2 * dd ^ 2) ^ 2 =
        4 * (1 - dd - dd ^ 2) * ((1 - dd - dd ^ 2) * r_F ^ 2 - 2 * dd ^ 2 * r_F - dd) +
        4 * dd * (dd - 1) ^ 2 * (dd + 1) := by ring
      rw [this, h_poly, mul_zero, zero_add]
    exact h_disc_not_sq ⟨2 * (1 - dd - dd ^ 2) * r_F - 2 * dd ^ 2, by rw [← sq]; exact h_sq.symm⟩

/-- The twisted Edwards curve equation `a·X²T² + Y²Z² = Z²T² + d·X²Y²` holds for
the Elligator completed point coordinates when `ω² = -d-1` and the "inner identity"
`(d+1)·Nt² = D²·((1+σ)² + d·(1-σ)²)` holds (where σ = s²).
This lemma handles the factorization: after substituting X=2sD, Y=1-s², Z=Nt·ω, T=1+s²,
the curve equation reduces to `4s²·[(d+1)Nt² - D²·P(s²,d)] = 0`. -/
private lemma elligator_curve_eq_of_inner {dd s Df Nt w : CurveField}
    (hw : w ^ 2 = -dd - 1)
    (h_inner : s = 0 ∨
      (dd + 1) * Nt ^ 2 = Df ^ 2 * ((1 + s ^ 2) ^ 2 + dd * (1 - s ^ 2) ^ 2)) :
    -1 * (2 * s * Df) ^ 2 * (1 + s ^ 2) ^ 2 +
      (1 - s ^ 2) ^ 2 * (Nt * w) ^ 2 =
    (Nt * w) ^ 2 * (1 + s ^ 2) ^ 2 +
      dd * (2 * s * Df) ^ 2 * (1 - s ^ 2) ^ 2 := by
  rcases h_inner with hs0 | h
  · rw [hs0]; ring
  · linear_combination 4 * s ^ 2 * h + (-4 * s ^ 2 * Nt ^ 2) * hw

/-- Case A ring identity: when c₁ = -1 (square case), Nₜ = -(r-1)(d-1)²-D,
the inner identity `(d+1)Nₜ² = (D+Nₛ)² + d(D-Nₛ)²` holds as a polynomial identity in r, d. -/
private lemma inner_ring_A (dd r : CurveField) :
    (dd + 1) * (-(r - 1) * (dd - 1) ^ 2 - (-1 - dd * r) * (r + dd)) ^ 2 =
    ((-1 - dd * r) * (r + dd) + (r + 1) * (1 - dd ^ 2)) ^ 2 +
    dd * ((-1 - dd * r) * (r + dd) - (r + 1) * (1 - dd ^ 2)) ^ 2 := by ring

/-- Case B ring identity: when c₁ = r (non-square case), Nₜ = r(r-1)(d-1)²-D,
the inner identity `(d+1)Nₜ² = (D+rNₛ)² + d(D-rNₛ)²` holds as a polynomial identity in r, d. -/
private lemma inner_ring_B (dd r : CurveField) :
    (dd + 1) * (r * (r - 1) * (dd - 1) ^ 2 - (-1 - dd * r) * (r + dd)) ^ 2 =
    ((-1 - dd * r) * (r + dd) + r * ((r + 1) * (1 - dd ^ 2))) ^ 2 +
    dd * ((-1 - dd * r) * (r + dd) - r * ((r + 1) * (1 - dd ^ 2))) ^ 2 := by ring

/-- Bridge lemma: when s²D = Nₛ, converts `(D+Nₛ)² + d(D-Nₛ)²` to `D²((1+s²)² + d(1-s²)²)`. -/
private lemma constr_to_squares {dd s Df Ns : CurveField}
    (h : s ^ 2 * Df = Ns) :
    (Df + Ns) ^ 2 + dd * (Df - Ns) ^ 2 =
    Df ^ 2 * ((1 + s ^ 2) ^ 2 + dd * (1 - s ^ 2) ^ 2) := by
  linear_combination
    -((2 - 2 * dd) * Df + (1 + dd) * (Ns + s ^ 2 * Df)) * h

/-- Bridge lemma (case B): when s²D = r·Nₛ, converts `(D+rNₛ)² + d(D-rNₛ)²` to `D²((1+s²)² + d(1-s²)²)`. -/
private lemma constr_to_squares_r {dd s r Df Ns : CurveField}
    (h : s ^ 2 * Df = r * Ns) :
    (Df + r * Ns) ^ 2 + dd * (Df - r * Ns) ^ 2 =
    Df ^ 2 * ((1 + s ^ 2) ^ 2 + dd * (1 - s ^ 2) ^ 2) := by
  linear_combination
    -((2 - 2 * dd) * Df + (1 + dd) * (r * Ns + s ^ 2 * Df)) * h

/-- If d is not a square and -1 is a square in a field, then d·x² + y² = 0 implies x = 0 ∧ y = 0.
Used to show N_t ≠ 0 in the Elligator map. -/
private lemma non_square_quad_zero {d x y : CurveField}
    (hd : ¬IsSquare d) (hm1 : IsSquare (-1 : CurveField))
    (h : d * x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have key : d * x ^ 2 = -(y ^ 2) := by linear_combination h
  have hx : x = 0 := by
    by_contra hx
    obtain ⟨α, hα⟩ := hm1
    have h1 : d * x ^ 2 = (α * y) ^ 2 := by linear_combination key + y ^ 2 * hα
    have h2 : d = (α * y / x) * (α * y / x) := by field_simp; linear_combination h1
    exact hd ⟨_, h2⟩
  exact ⟨hx, sq_eq_zero_iff.mp (by rw [hx] at h; simpa using h)⟩

/-- Conditional field element assignment: if choice flag = 1, result = first operand. -/
private lemma cond_f51_eq {z x y : backend.serial.u64.field.FieldElement51}
    {c : subtle.Choice}
    (hpost : ∀ i < 5, z[i]! = if c.val = 1#u8 then x[i]! else y[i]!)
    (hc : c.val = 1#u8) : Field51_as_Nat z = Field51_as_Nat x := by
  unfold Field51_as_Nat; apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi; have h := hpost i hi; simp only [Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, hc, ↓reduceIte] at h; simp only [Array.getElem!_Nat_eq,
      List.getElem!_eq_getElem?_getD, h]

/-- Conditional field element assignment: if choice flag ≠ 1, result = second operand. -/
private lemma cond_f51_eq_neg {z x y : backend.serial.u64.field.FieldElement51}
    {c : subtle.Choice}
    (hpost : ∀ i < 5, z[i]! = if c.val = 1#u8 then x[i]! else y[i]!)
    (hc : ¬(c.val = 1#u8)) : Field51_as_Nat z = Field51_as_Nat y := by
  unfold Field51_as_Nat; apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi; have h := hpost i hi; simp only [Array.getElem!_Nat_eq,
    List.getElem!_eq_getElem?_getD, hc, ↓reduceIte] at h; simp only [Array.getElem!_Nat_eq,
      List.getElem!_eq_getElem?_getD, h]

/-- If Field51_as_Nat x ≡ 0 (mod p), then x.toField = 0. -/
private lemma toField_of_mod_zero {x : backend.serial.u64.field.FieldElement51}
    (h : Field51_as_Nat x % p = 0) : x.toField = 0 := by
  unfold toField
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_iff_mod_eq_zero.mpr h)

/-- Lift (a%p)²*(b%p) %p = c%p to CurveField equality a²*b = c. -/
private lemma lift_sq_mod {a b c : ℕ}
    (h : (a % p) ^ 2 * (b % p) % p = c % p) :
    (a : CurveField) ^ 2 * (b : CurveField) = (c : CurveField) := by
  have hme := ((Nat.mod_modEq a p).symm.pow 2).mul
    (Nat.mod_modEq b p).symm |>.trans h
  have h := lift_mod_eq _ _ hme; push_cast at h; exact h

/-- Shared field-lift bundle for the Elligator construction.
Used in both the intermediate `CompletedPoint.IsValid` proof and the final semantic bridge. -/
private lemma lift_bridge_bundle
    (cp_T one s_sq s1 r_plus_one r one_minus_d_sq N_s r_plus_d d
      c_minus_dr d_times_r c D r_minus_one c2 c_r_minus_one c_r_minus_one_d
      N_t d_minus_one_sq : backend.serial.u64.field.FieldElement51)
    (h_cp_T_nat : Field51_as_Nat cp_T = Field51_as_Nat one + Field51_as_Nat s_sq)
    (s_sq_post1 : Field51_as_Nat s_sq ≡ Field51_as_Nat s1 ^ 2 [MOD p])
    (one_post1 : Field51_as_Nat one = 1)
    (h_rpo_nat : Field51_as_Nat r_plus_one = Field51_as_Nat r + Field51_as_Nat one)
    (one_minus_d_sq_post1 : Field51_as_Nat one_minus_d_sq = (1 + p - _root_.d ^ 2 % p) % p)
    (N_s_post1 : Field51_as_Nat N_s ≡ Field51_as_Nat r_plus_one * Field51_as_Nat one_minus_d_sq [MOD p])
    (h_rpd_nat : Field51_as_Nat r_plus_d = Field51_as_Nat r + Field51_as_Nat d)
    (d_post1 : Field51_as_Nat d = _root_.d)
    (c_minus_dr_post2 : (Field51_as_Nat c_minus_dr + Field51_as_Nat d_times_r) % p = Field51_as_Nat c % p)
    (d_times_r_post1 : Field51_as_Nat d_times_r ≡ Field51_as_Nat d * Field51_as_Nat r [MOD p])
    (c_post1 : Field51_as_Nat c = p - 1)
    (D_post1 : Field51_as_Nat D ≡ Field51_as_Nat c_minus_dr * Field51_as_Nat r_plus_d [MOD p])
    (r_minus_one_post2 : (Field51_as_Nat r_minus_one + Field51_as_Nat one) % p = Field51_as_Nat r % p)
    (c_r_minus_one_post1 : Field51_as_Nat c_r_minus_one ≡ Field51_as_Nat c2 * Field51_as_Nat r_minus_one [MOD p])
    (c_r_minus_one_d_post1 :
      Field51_as_Nat c_r_minus_one_d ≡ Field51_as_Nat c_r_minus_one * Field51_as_Nat d_minus_one_sq [MOD p])
    (N_t_post2 : (Field51_as_Nat N_t + Field51_as_Nat D) % p = Field51_as_Nat c_r_minus_one_d % p)
    (d_minus_one_sq_post1 : Field51_as_Nat d_minus_one_sq = (_root_.d - 1) ^ 2 % p) :
    cp_T.toField = 1 + s1.toField ^ 2 ∧
    r_plus_one.toField = r.toField + 1 ∧
    one_minus_d_sq.toField = 1 - Ed25519.d ^ 2 ∧
    N_s.toField = (r.toField + 1) * (1 - Ed25519.d ^ 2) ∧
    r_plus_d.toField = r.toField + Ed25519.d ∧
    c_minus_dr.toField = -1 - Ed25519.d * r.toField ∧
    D.toField = (-1 - Ed25519.d * r.toField) * (r.toField + Ed25519.d) ∧
    r_minus_one.toField = r.toField - 1 ∧
    c_r_minus_one.toField = c2.toField * r_minus_one.toField ∧
    c_r_minus_one_d.toField = c_r_minus_one.toField * d_minus_one_sq.toField ∧
    N_t.toField + D.toField = c_r_minus_one_d.toField ∧
    N_t.toField =
      c2.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
  have h_cp_T_F : cp_T.toField = 1 + s1.toField ^ 2 := by
    unfold toField
    have hsq := lift_mod_eq _ _ s_sq_post1
    rw [h_cp_T_nat]; push_cast
    push_cast at hsq; rw [hsq, one_post1]
    simp only [Nat.cast_one]
  have h_rpo_F : r_plus_one.toField = r.toField + 1 := by
    unfold toField
    rw [h_rpo_nat]; push_cast; rw [one_post1]; simp only [Nat.cast_one]
  have h_omds_F : one_minus_d_sq.toField = 1 - Ed25519.d ^ 2 := by
    unfold toField; rw [one_minus_d_sq_post1]
    have h_sum : ((1 + p - _root_.d ^ 2 % p) % p + _root_.d ^ 2) % p = 1 % p := by
      norm_num [_root_.d, p]
    have h := lift_mod_eq _ _ h_sum; push_cast at h
    change _ = 1 - (_root_.d : CurveField) ^ 2; linear_combination h
  have h_ns_eq_F : N_s.toField = (r.toField + 1) * (1 - Ed25519.d ^ 2) := by
    have hN : N_s.toField = r_plus_one.toField * one_minus_d_sq.toField := by
      unfold toField; have h := lift_mod_eq _ _ N_s_post1; push_cast at h; exact h
    rw [hN, h_rpo_F, h_omds_F]
  have h_rpd_F : r_plus_d.toField = r.toField + Ed25519.d := by
    unfold toField
    rw [h_rpd_nat]; push_cast; rw [d_post1]; rfl
  have h_cmdr_F : c_minus_dr.toField = -1 - Ed25519.d * r.toField := by
    have hD_sub : c_minus_dr.toField + d_times_r.toField = c.toField := by
      unfold toField; have h := lift_mod_eq _ _ c_minus_dr_post2; push_cast at h; exact h
    have hD_dr : d_times_r.toField = d.toField * r.toField := by
      unfold toField; have h := lift_mod_eq _ _ d_times_r_post1; push_cast at h; exact h
    have hc_F : c.toField = -1 := by
      unfold toField; rw [c_post1]
      have h_sum : (p - 1 + 1) % p = 0 % p := by norm_num [p]
      have h := lift_mod_eq _ _ h_sum; push_cast at h; linear_combination h
    have hd_F : d.toField = Ed25519.d := by
      unfold toField; rw [d_post1]; rfl
    rw [hc_F] at hD_sub; rw [hd_F] at hD_dr
    linear_combination hD_sub - hD_dr
  have h_D_eq_F : D.toField =
      (-1 - Ed25519.d * r.toField) * (r.toField + Ed25519.d) := by
    have hD : D.toField = c_minus_dr.toField * r_plus_d.toField := by
      unfold toField; have h := lift_mod_eq _ _ D_post1; push_cast at h; exact h
    rw [hD, h_cmdr_F, h_rpd_F]
  have h_rm1_F : r_minus_one.toField = r.toField - 1 := by
    unfold toField; have h := lift_mod_eq _ _ r_minus_one_post2
    push_cast at h; rw [one_post1, Nat.cast_one] at h; linear_combination h
  have h_cr_F : c_r_minus_one.toField = c2.toField * r_minus_one.toField := by
    unfold toField; have h := lift_mod_eq _ _ c_r_minus_one_post1
    push_cast at h; exact h
  have h_crd_F : c_r_minus_one_d.toField = c_r_minus_one.toField *
      d_minus_one_sq.toField := by
    unfold toField; have h := lift_mod_eq _ _ c_r_minus_one_d_post1
    push_cast at h; exact h
  have h_Nt_add_F : N_t.toField + D.toField = c_r_minus_one_d.toField := by
    unfold toField; have h := lift_mod_eq _ _ N_t_post2; push_cast at h; exact h
  have h_Nt_eq_F : N_t.toField =
      c2.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
    have : N_t.toField = c_r_minus_one_d.toField - D.toField := by
      linear_combination h_Nt_add_F
    rw [this, h_crd_F, h_cr_F, h_rm1_F]; unfold toField; rw [d_minus_one_sq_post1]; rfl
  exact ⟨h_cp_T_F, h_rpo_F, h_omds_F, h_ns_eq_F, h_rpd_F, h_cmdr_F,
    h_D_eq_F, h_rm1_F, h_cr_F, h_crd_F, h_Nt_add_F, h_Nt_eq_F⟩

/-
natural language description:

• Takes a field element s and maps it to a valid RistrettoPoint using the Elligator map:

  https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4

  Arithmetics are performed in the field 𝔽ₚ where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic) for all valid field element inputs s
• The output is indeed a valid RistrettoPoint (i.e., an even Edwards point that lies on the curve)
• The output matches the pure mathematical Elligator map applied to the field value of s
-/

set_option maxHeartbeats 1200000 in -- needed for complex progress
/-- **Spec and proof concerning `ristretto.RistrettoPoint.elligator_ristretto_flavor`**:
• The function always succeeds (no panic) for all valid field element inputs
• The output is indeed a valid RistrettoPoint (i.e., an even Edwards point that lies on the curve)
• The output point corresponds to `elligator_ristretto_flavor_pure s.toField`, bridging
  the implementation to the pure mathematical Elligator map defined in Representation.lean
-/
@[progress]
theorem elligator_ristretto_flavor_spec
    (s : backend.serial.u64.field.FieldElement51)
    (h_s_valid : s.IsValid) :
    elligator_ristretto_flavor s ⦃ result =>
    result.IsValid ∧
    result.toPoint = (elligator_ristretto_flavor_pure s.toField).val ⦄ := by
  unfold elligator_ristretto_flavor
  progress*
  · -- ∀ i < 5, ↑c2[i]! < 2 ^ 54
    intro i hi
    have h := c2_post i hi
    simp only [h]
    split
    · have := r_post2 i hi; omega
    · have := c_post2 i hi; omega
  · intro i hi; simp only [s1_post i hi]; split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post2 i hi; omega
      · have := s_prime_post2 i hi; omega
    · grind
  · intro i hi; simp only [s1_post i hi]; split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post2 i hi; omega
      · have := s_prime_post2 i hi; omega
    · grind
  · intro i hi; simp only [s1_post i hi]; split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post2 i hi; omega
      · have := s_prime_post2 i hi; omega
    · grind
  · -- CompletedPoint.IsValid { X := cp_X, Y := cp_Y, Z := cp_Z, T := cp_T }
    rename_i x _ x_post1 x_post2 N_post_x N_post1_D N_post2_D N_post3_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have h_cp_T_nat : Field51_as_Nat cp_T = Field51_as_Nat one + Field51_as_Nat s_sq := by
      unfold Field51_as_Nat
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi; rw [cp_T_post1 i hi, mul_add]
    have h_rpo_nat : Field51_as_Nat r_plus_one = Field51_as_Nat r + Field51_as_Nat one := by
      unfold Field51_as_Nat
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi; rw [r_plus_one_post1 i hi, mul_add]
    have h_rpd_nat : Field51_as_Nat r_plus_d =
        Field51_as_Nat r + Field51_as_Nat d := by
      unfold Field51_as_Nat
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi; rw [r_plus_d_post1 i hi, mul_add]
    rcases lift_bridge_bundle cp_T one s_sq s1 r_plus_one r one_minus_d_sq
        N_s r_plus_d d c_minus_dr d_times_r c D r_minus_one c2
        c_r_minus_one c_r_minus_one_d N_t d_minus_one_sq
        h_cp_T_nat s_sq_post1 one_post1 h_rpo_nat
        one_minus_d_sq_post1 N_s_post1 h_rpd_nat d_post1
        c_minus_dr_post2 d_times_r_post1 c_post1 D_post1
        r_minus_one_post2 c_r_minus_one_post1 c_r_minus_one_d_post1
        N_t_post2 d_minus_one_sq_post1 with
      ⟨h_cp_T_F, h_rpo_F, h_omds_F, h_ns_eq_F, h_rpd_F, h_cmdr_F,
        h_D_eq_F, h_rm1_F, h_cr_F, h_crd_F, h_Nt_add_F, h_Nt_eq_F⟩
    -- Prove cp_T.toField ≠ 0
    have h_cp_T_ne : cp_T.toField ≠ 0 := by
      rw [h_cp_T_F]
      intro h_zero
      have h_s1_sq_eq_m1 : s1.toField ^ 2 = -1 := by linear_combination h_zero
      by_cases hD_mod : Field51_as_Nat D % p = 0
      · -- D ≡ 0 (mod p): s1 must be 0, contradicting s1² = -1
        have h_raw_zero : Field51_as_Nat x.2 % p = 0 := by
          by_cases hN0 : Field51_as_Nat N_s % p = 0
          · grind
          · grind
        have h_sp_mod : Field51_as_Nat s_prime % p = 0 := by
          have : Field51_as_Nat s_prime % p =
              (Field51_as_Nat x.2 * Field51_as_Nat s) % p := s_prime_post1
          rw [Nat.mul_mod, h_raw_zero, zero_mul, Nat.zero_mod] at this; exact this
        have h_spn_mod : Field51_as_Nat s_prime_neg % p = 0 := by
          have h := s_prime_neg_post1
          simp only [Nat.ModEq, Nat.zero_mod] at h
          rwa [Nat.add_mod, h_sp_mod, zero_add, Nat.mod_mod] at h
        have h_sp1_mod : Field51_as_Nat s_prime1 % p = 0 := by
          by_cases hc : s_prime_is_pos.val = 1#u8
          · rw [cond_f51_eq s_prime1_post hc]; exact h_spn_mod
          · rw [cond_f51_eq_neg s_prime1_post hc]; exact h_sp_mod
        have h_s1_mod : Field51_as_Nat s1 % p = 0 := by
          by_cases hc : not_sq.val = 1#u8
          · rw [cond_f51_eq s1_post hc]; exact h_sp1_mod
          · rw [cond_f51_eq_neg s1_post hc]; exact h_raw_zero
        rw [show s1.toField = 0 from toField_of_mod_zero h_s1_mod] at h_s1_sq_eq_m1
        simp at h_s1_sq_eq_m1
      · -- D ≢ 0 (mod p): prove the disjunction and apply the lemma
        have h_disj : s1.toField ^ 2 * D.toField = N_s.toField ∨
            s1.toField ^ 2 * D.toField = r.toField * N_s.toField := by
          by_cases h_sq_flag : x.1.val = 1#u8
          · -- IS a square: not_sq=0, s1 = x.2
            left
            have h_nsq : not_sq.val ≠ 1#u8 := by
              have := not_sq_post.mp h_sq_flag; subst this; decide
            rw [show s1.toField = x.2.toField from by
              unfold toField; rw [cond_f51_eq_neg s1_post h_nsq]]
            have h_eq : (Field51_as_Nat x.2 % p) ^ 2 * (Field51_as_Nat D % p) % p =
                Field51_as_Nat N_s % p := by
              by_cases hN0 : Field51_as_Nat N_s % p = 0
              · rw [(N_post_x hN0).2]; simp only [ne_eq, OfNat.ofNat_ne_zero,
                not_false_eq_true, zero_pow, zero_mul, Nat.zero_mod, hN0]
              · have hSq : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p = Field51_as_Nat N_s % p := by
                  by_contra hNSq
                  have := (N_post3_D ⟨hN0, hD_mod, hNSq⟩).1
                  rw [h_sq_flag] at this; exact absurd this (by decide)
                exact (N_post2_D ⟨hN0, hD_mod, hSq⟩).2
            exact lift_sq_mod h_eq
          · -- NOT a square: not_sq=1, s1 = s_prime1
            right
            have h_nsq : not_sq.val = 1#u8 := by
              rcases not_sq with ⟨val, hv | hv⟩
              · exact absurd (not_sq_post.mpr (by simp only [Choice.zero, hv])) h_sq_flag
              · exact hv
            rw [show s1.toField = s_prime1.toField from by
              unfold toField; rw [cond_f51_eq s1_post h_nsq]]
            have h_sp1_sq : s_prime1.toField ^ 2 = s_prime.toField ^ 2 := by
              by_cases hc : s_prime_is_pos.val = 1#u8
              · rw [show s_prime1.toField = s_prime_neg.toField from by
                  unfold toField; rw [cond_f51_eq s_prime1_post hc]]
                rw [show s_prime_neg.toField = -s_prime.toField from by
                  unfold toField
                  have h := lift_mod_eq _ 0 s_prime_neg_post1
                  push_cast at h; linear_combination h]
                exact neg_sq _
              · rw [show s_prime1.toField = s_prime.toField from by
                  unfold toField; rw [cond_f51_eq_neg s_prime1_post hc]]
            rw [h_sp1_sq]
            have h_sp_F : s_prime.toField = x.2.toField * s.toField := by
              unfold toField; have h := lift_mod_eq _ _ s_prime_post1
              push_cast at h; exact h
            rw [h_sp_F, mul_pow]
            have hN0 : Field51_as_Nat N_s % p ≠ 0 := by
              intro h0; have := (N_post_x h0).1; exact absurd this h_sq_flag
            have hNSq : ¬∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                Field51_as_Nat N_s % p := by
              intro hSq; have := (N_post2_D ⟨hN0, hD_mod, hSq⟩).1
              exact absurd this h_sq_flag
            have h6 := (N_post3_D ⟨hN0, hD_mod, hNSq⟩).2
            have h_disc_D : x.2.toField ^ 2 * D.toField =
                field.FieldElement51.SQRT_M1_val.toField * N_s.toField := by
              unfold toField
              have lhs_me := ((Nat.mod_modEq (Field51_as_Nat x.2) p).symm.pow 2).mul
                (Nat.mod_modEq (Field51_as_Nat D) p).symm
              have rhs_me := (Nat.mod_modEq
                (Field51_as_Nat field.FieldElement51.SQRT_M1_val) p).symm.mul
                (Nat.mod_modEq (Field51_as_Nat N_s) p).symm
              have hme := lhs_me.trans (h6.trans rhs_me.symm)
              have h := lift_mod_eq _ _ hme; push_cast at h; exact h
            have h_r_F : r.toField = i.toField * s.toField ^ 2 := by
              unfold toField
              have hme := r_post1.trans (Nat.ModEq.mul_left
                (Field51_as_Nat i) r_0_sq_post1)
              have h := lift_mod_eq _ _ hme; push_cast at h; exact h
            have h_i_val : i.toField = field.FieldElement51.SQRT_M1_val.toField := by
              rw [i_post1]; rfl
            rw [h_i_val] at h_r_F
            linear_combination s.toField ^ 2 * h_disc_D - N_s.toField * h_r_F
        exact absurd h_s1_sq_eq_m1
          (elligator_s1_sq_ne_neg_one r.toField N_s.toField D.toField s1.toField
            h_ns_eq_F h_D_eq_F h_disj)
    -- Prove cp_Z.toField ≠ 0
    have h_cp_Z_ne : cp_Z.toField ≠ 0 := by
      have h_cpz_F : cp_Z.toField = N_t.toField *
          fe.toField := by
        unfold toField; have h := lift_mod_eq _ _ cp_Z_post1; push_cast at h; exact h
      rw [h_cpz_F]; apply mul_ne_zero
      · -- N_t.toField ≠ 0
        have h_Nt_eq : N_t.toField =
            c2.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 -
            (-1 - Ed25519.d * r.toField) * (r.toField + Ed25519.d) := by
          rw [h_Nt_eq_F, h_D_eq_F]
        intro h0; rw [h_Nt_eq] at h0
        by_cases h_nsq : not_sq.val = 1#u8
        · -- NOT square: c1 = r
          rw [show c2.toField = r.toField from by
            unfold toField; rw [cond_f51_eq c2_post h_nsq]] at h0
          have h_quad : Ed25519.d * (r.toField + 1) ^ 2 +
              ((Ed25519.d - 1) * r.toField) ^ 2 = 0 := by linear_combination h0
          have ⟨hr1, hr2⟩ :=
            non_square_quad_zero Edwards.d_not_square neg_one_is_square h_quad
          rw [show r.toField = -1 from by linear_combination hr1] at hr2
          exact Edwards.d_not_square ⟨1, by
            linear_combination (mul_eq_zero.mp hr2).resolve_right
              (neg_ne_zero.mpr (one_ne_zero (α := CurveField)))⟩
        · -- IS square: c1 = -1
          rw [show c2.toField = (-1 : CurveField) from by
            unfold toField; rw [cond_f51_eq_neg c2_post h_nsq]
            rw [c_post1]
            have h_sum : (p - 1 + 1) % p = 0 % p := by norm_num [p]
            have h := lift_mod_eq _ _ h_sum; push_cast at h; linear_combination h] at h0
          have h_quad : Ed25519.d * (r.toField + 1) ^ 2 +
              (Ed25519.d - 1) ^ 2 = 0 := by linear_combination h0
          have ⟨_, hd1⟩ :=
            non_square_quad_zero Edwards.d_not_square neg_one_is_square h_quad
          exact Edwards.d_not_square ⟨1, by linear_combination hd1⟩
      · -- fe.toField ≠ 0 (SQRT_AD_MINUS_ONE squared ≡ a*d-1 ≢ 0 mod p)
        intro h_zero; unfold toField at h_zero
        have h_fe_mod : Field51_as_Nat fe % p = 0 := by
          rwa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at h_zero
        have h_sq_zero : (↑(Field51_as_Nat fe) : Int) ^ 2 % (↑p : Int) = 0 := by
          have h : (Field51_as_Nat fe) ^ 2 % p = 0 := by rw [Nat.pow_mod, h_fe_mod]; simp
          exact_mod_cast h
        rw [h_sq_zero] at fe_post1
        exact absurd fe_post1.symm (by decide)
    -- Prove on_curve
    have h_cp_curve :
        Ed25519.a * cp_X.toField ^ 2 * cp_T.toField ^ 2 +
          cp_Y.toField ^ 2 * cp_Z.toField ^ 2 =
        cp_Z.toField ^ 2 * cp_T.toField ^ 2 +
          Ed25519.d * cp_X.toField ^ 2 * cp_Y.toField ^ 2 := by
      have h_cp_X_F : cp_X.toField = s_plus_s.toField * D.toField := by
        unfold toField; have h := lift_mod_eq _ _ cp_X_post1; push_cast at h; exact h
      have h_sps_F : s_plus_s.toField = 2 * s1.toField := by
        unfold toField
        have h_nat : Field51_as_Nat s_plus_s = Field51_as_Nat s1 + Field51_as_Nat s1 := by
          unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi; rw [s_plus_s_post1 i hi, mul_add]
        rw [h_nat]; push_cast; ring
      have h_cp_Y_F : cp_Y.toField = 1 - s1.toField ^ 2 := by
        unfold toField
        have h_sub := lift_mod_eq _ _ cp_Y_post2
        have hsq := lift_mod_eq _ _ s_sq_post1
        push_cast at h_sub hsq; rw [one_post1, Nat.cast_one] at h_sub
        linear_combination h_sub - hsq
      have h_cp_Z_F : cp_Z.toField = N_t.toField * fe.toField := by
        unfold toField; have h := lift_mod_eq _ _ cp_Z_post1; push_cast at h; exact h
      rw [h_cp_X_F, h_sps_F, h_cp_Y_F, h_cp_Z_F, h_cp_T_F, show Ed25519.a = -1 from rfl]
      -- Establish ω² = -d - 1
      have h_omega_sq : fe.toField ^ 2 = -Ed25519.d - 1 := by
        unfold toField
        have h := (ZMod.intCast_eq_intCast_iff _ _ p).mpr fe_post1
        push_cast at h; simp only [a] at h; rw [h]
        simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul, Ed25519]
      apply elligator_curve_eq_of_inner h_omega_sq
      -- Case split s1=0 ∨ inner identity
      by_cases hs : s1.toField = 0
      · exact Or.inl hs
      · right
        -- Derive s1²·D constraint with c2 info
        have h_disj' :
            (s1.toField ^ 2 * D.toField = N_s.toField ∧ c2.toField = -1) ∨
            (s1.toField ^ 2 * D.toField = r.toField * N_s.toField ∧
             c2.toField = r.toField) := by
          by_cases h_sq_flag : x.1.val = 1#u8
          · -- IS a square: s1 = x.2, s1²D = N_s, c2 = -1
            left
            have h_nsq : not_sq.val ≠ 1#u8 := by
              have := not_sq_post.mp h_sq_flag; subst this; decide
            constructor
            · rw [show s1.toField = x.2.toField from by
                unfold toField; rw [cond_f51_eq_neg s1_post h_nsq]]
              have h_eq : (Field51_as_Nat x.2 % p) ^ 2 * (Field51_as_Nat D % p) % p =
                  Field51_as_Nat N_s % p := by
                by_cases hN0 : Field51_as_Nat N_s % p = 0
                · rw [(N_post_x hN0).2]; simp only [ne_eq, OfNat.ofNat_ne_zero,
                    not_false_eq_true, zero_pow, zero_mul, Nat.zero_mod, hN0]
                · have hD_mod : Field51_as_Nat D % p ≠ 0 := by
                    intro hD0
                    exact absurd (N_post1_D ⟨hN0, hD0⟩).1 (by rw [h_sq_flag]; decide)
                  have hSq : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                      Field51_as_Nat N_s % p := by
                    by_contra hNSq
                    exact absurd (N_post3_D ⟨hN0, hD_mod, hNSq⟩).1
                      (by rw [h_sq_flag]; decide)
                  exact (N_post2_D ⟨hN0, hD_mod, hSq⟩).2
              exact lift_sq_mod h_eq
            · unfold toField; rw [cond_f51_eq_neg c2_post h_nsq]; rw [c_post1]
              have h_sum : (p - 1 + 1) % p = 0 % p := by norm_num [p]
              have h := lift_mod_eq _ _ h_sum; push_cast at h; linear_combination h
          · -- NOT a square: s1 = s_prime1, s1²D = r·N_s, c2 = r
            right
            have h_nsq : not_sq.val = 1#u8 := by
              rcases not_sq with ⟨val, hv | hv⟩
              · exact absurd (not_sq_post.mpr (by simp only [hv, Choice.zero])) h_sq_flag
              · exact hv
            constructor
            · rw [show s1.toField = s_prime1.toField from by
                unfold toField; rw [cond_f51_eq s1_post h_nsq]]
              have h_sp1_sq : s_prime1.toField ^ 2 = s_prime.toField ^ 2 := by
                by_cases hc : s_prime_is_pos.val = 1#u8
                · rw [show s_prime1.toField = s_prime_neg.toField from by
                    unfold toField; rw [cond_f51_eq s_prime1_post hc]]
                  rw [show s_prime_neg.toField = -s_prime.toField from by
                    unfold toField
                    have h := lift_mod_eq _ 0 s_prime_neg_post1
                    push_cast at h; linear_combination h]
                  exact neg_sq _
                · rw [show s_prime1.toField = s_prime.toField from by
                    unfold toField; rw [cond_f51_eq_neg s_prime1_post hc]]
              rw [h_sp1_sq]
              have h_sp_F : s_prime.toField = x.2.toField * s.toField := by
                unfold toField; have h := lift_mod_eq _ _ s_prime_post1
                push_cast at h; exact h
              rw [h_sp_F, mul_pow]
              have hN0 : Field51_as_Nat N_s % p ≠ 0 := by
                intro h0; exact absurd (N_post_x h0).1 h_sq_flag
              have hD_mod : Field51_as_Nat D % p ≠ 0 := by
                intro hD0; apply hs
                have h_dz := (N_post1_D ⟨hN0, hD0⟩).2
                have h_spz : Field51_as_Nat s_prime % p = 0 := by
                  have h := s_prime_post1
                  simp only [Nat.ModEq] at h
                  rw [Nat.mul_mod, h_dz, zero_mul, Nat.zero_mod] at h; exact h
                have h_snz : Field51_as_Nat s_prime_neg % p = 0 := by
                  have h := s_prime_neg_post1
                  simp only [Nat.ModEq, Nat.zero_mod] at h
                  rwa [Nat.add_mod, h_spz, zero_add, Nat.mod_mod] at h
                have h_s1z : Field51_as_Nat s_prime1 % p = 0 := by
                  by_cases hc : s_prime_is_pos.val = 1#u8
                  · rw [cond_f51_eq s_prime1_post hc]; exact h_snz
                  · rw [cond_f51_eq_neg s_prime1_post hc]; exact h_spz
                exact toField_of_mod_zero (by rw [cond_f51_eq s1_post h_nsq]; exact h_s1z)
              have hNSq : ¬∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                  Field51_as_Nat N_s % p := by
                intro hSq; exact absurd (N_post2_D ⟨hN0, hD_mod, hSq⟩).1 h_sq_flag
              have h6 := (N_post3_D ⟨hN0, hD_mod, hNSq⟩).2
              have h_disc_D : x.2.toField ^ 2 * D.toField =
                  field.FieldElement51.SQRT_M1_val.toField * N_s.toField := by
                unfold toField
                have lhs_me := ((Nat.mod_modEq (Field51_as_Nat x.2) p).symm.pow 2).mul
                  (Nat.mod_modEq (Field51_as_Nat D) p).symm
                have rhs_me := (Nat.mod_modEq
                  (Field51_as_Nat field.FieldElement51.SQRT_M1_val) p).symm.mul
                  (Nat.mod_modEq (Field51_as_Nat N_s) p).symm
                have hme := lhs_me.trans (h6.trans rhs_me.symm)
                have h := lift_mod_eq _ _ hme; push_cast at h; exact h
              have h_r_F : r.toField = i.toField * s.toField ^ 2 := by
                unfold toField
                have hme := r_post1.trans (Nat.ModEq.mul_left
                  (Field51_as_Nat i) r_0_sq_post1)
                have h := lift_mod_eq _ _ hme; push_cast at h; exact h
              have h_i_val : i.toField = field.FieldElement51.SQRT_M1_val.toField := by
                rw [i_post1]; rfl
              rw [h_i_val] at h_r_F
              linear_combination s.toField ^ 2 * h_disc_D - N_s.toField * h_r_F
            · unfold toField; rw [cond_f51_eq c2_post h_nsq]
        -- Case split on square/non-square
        rcases h_disj' with ⟨hA, h_c1⟩ | ⟨hB, h_c1⟩
        · -- Case A: s1²D = N_s, c2 = -1
          have h_nt_A : N_t.toField =
              -(r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
            rw [h_Nt_eq_F, h_c1]; ring
          have step1 : (Ed25519.d + 1) * N_t.toField ^ 2 =
              (D.toField + N_s.toField) ^ 2 +
              Ed25519.d * (D.toField - N_s.toField) ^ 2 := by
            rw [h_nt_A, h_D_eq_F, h_ns_eq_F]; ring
          rw [step1]; exact constr_to_squares hA
        · -- Case B: s1²D = r·N_s, c2 = r
          have h_nt_B : N_t.toField =
              r.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
            rw [h_Nt_eq_F, h_c1];
          have step1 : (Ed25519.d + 1) * N_t.toField ^ 2 =
              (D.toField + r.toField * N_s.toField) ^ 2 +
              Ed25519.d * (D.toField - r.toField * N_s.toField) ^ 2 := by
            rw [h_nt_B, h_D_eq_F, h_ns_eq_F]; ring
          rw [step1]; exact constr_to_squares_r hB
    -- Construct the record
    exact ⟨fun i hi => by dsimp only [Nat.reducePow]; have := cp_X_post2 i hi; omega,
           fun i hi => by dsimp only [Nat.reducePow]; have := cp_Y_post1 i hi; omega,
           fun i hi => by dsimp only [Nat.reducePow]; have := cp_Z_post2 i hi; omega,
           fun i hi => by dsimp only [Nat.reducePow]; have := cp_T_post2 i hi; omega,
           h_cp_Z_ne, h_cp_T_ne, h_cp_curve⟩
  -- Main Goals: ⊢ IsValid ep ∧ toPoint ep = ↑(elligator_ristretto_flavor_pure s.toField)
  -- Step 1: Lift arithmetic postconditions to field equalities
  rename_i x _ x_post1 x_post2 N_post_x N_post1_D N_post2_D N_post3_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hX_F : ep.X.toField = cp_X.toField * cp_T.toField := by
    unfold toField; have h := lift_mod_eq _ _ ep_post1; push_cast at h; exact h
  have hY_F : ep.Y.toField = cp_Y.toField * cp_Z.toField := by
    unfold toField; have h := lift_mod_eq _ _ ep_post2; push_cast at h; exact h
  have hZ_F : ep.Z.toField = cp_Z.toField * cp_T.toField := by
    unfold toField; have h := lift_mod_eq _ _ ep_post3; push_cast at h; exact h
  have hT_F : ep.T.toField = cp_X.toField * cp_Y.toField := by
    unfold toField; have h := lift_mod_eq _ _ ep_post4; push_cast at h; exact h
  have h_cp_T_nat : Field51_as_Nat cp_T = Field51_as_Nat one + Field51_as_Nat s_sq := by
    unfold Field51_as_Nat
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; rw [cp_T_post1 i hi, mul_add]
  have h_rpo_nat : Field51_as_Nat r_plus_one = Field51_as_Nat r + Field51_as_Nat one := by
    unfold Field51_as_Nat
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; rw [r_plus_one_post1 i hi, mul_add]
  have h_rpd_nat : Field51_as_Nat r_plus_d =
      Field51_as_Nat r + Field51_as_Nat d := by
    unfold Field51_as_Nat
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; rw [r_plus_d_post1 i hi, mul_add]
  rcases lift_bridge_bundle cp_T one s_sq s1 r_plus_one r one_minus_d_sq
      N_s r_plus_d d c_minus_dr d_times_r c D r_minus_one c2
      c_r_minus_one c_r_minus_one_d N_t d_minus_one_sq
      h_cp_T_nat s_sq_post1 one_post1 h_rpo_nat
      one_minus_d_sq_post1 N_s_post1 h_rpd_nat d_post1
      c_minus_dr_post2 d_times_r_post1 c_post1 D_post1
      r_minus_one_post2 c_r_minus_one_post1 c_r_minus_one_d_post1
      N_t_post2 d_minus_one_sq_post1 with
    ⟨h_cp_T_F, h_rpo_F, h_omds_F, h_ns_eq_F, h_rpd_F, h_cmdr_F,
      h_D_eq_F, h_rm1_F, h_cr_F, h_crd_F, h_Nt_add_F, h_Nt_eq_F⟩
  have h_r_F : r.toField = i.toField * s.toField ^ 2 := by
    unfold toField
    have hme := r_post1.trans (Nat.ModEq.mul_left
      (Field51_as_Nat i) r_0_sq_post1)
    have h := lift_mod_eq _ _ hme; push_cast at h; exact h
  have h_i_val : i.toField = field.FieldElement51.SQRT_M1_val.toField := by
    rw [i_post1]; rfl
  have h_s1_sq_c2_cases (h_s1_ne : s1.toField ≠ 0) :
      (s1.toField ^ 2 * D.toField = N_s.toField ∧ c2.toField = -1) ∨
      (s1.toField ^ 2 * D.toField = r.toField * N_s.toField ∧
        c2.toField = r.toField) := by
    by_cases h_sq_flag : x.1.val = 1#u8
    · -- IS a square: s1 = x.2, s1²D = N_s, c2 = -1
      left
      have h_nsq : not_sq.val ≠ 1#u8 := by
        have := not_sq_post.mp h_sq_flag; subst this; decide
      constructor
      · rw [show s1.toField = x.2.toField from by
          unfold toField; rw [cond_f51_eq_neg s1_post h_nsq]]
        have h_eq : (Field51_as_Nat x.2 % p) ^ 2 * (Field51_as_Nat D % p) % p =
            Field51_as_Nat N_s % p := by
          by_cases hN0 : Field51_as_Nat N_s % p = 0
          · rw [(N_post_x hN0).2]; simp only [ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow, zero_mul, Nat.zero_mod, hN0]
          · have hD_mod : Field51_as_Nat D % p ≠ 0 := by
              intro hD0
              exact absurd (N_post1_D ⟨hN0, hD0⟩).1 (by rw [h_sq_flag]; decide)
            have hSq : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                Field51_as_Nat N_s % p := by
              by_contra hNSq
              exact absurd (N_post3_D ⟨hN0, hD_mod, hNSq⟩).1
                (by rw [h_sq_flag]; decide)
            exact (N_post2_D ⟨hN0, hD_mod, hSq⟩).2
        exact lift_sq_mod h_eq
      · unfold toField; rw [cond_f51_eq_neg c2_post h_nsq]; rw [c_post1]
        have h_sum : (p - 1 + 1) % p = 0 % p := by norm_num [p]
        have h := lift_mod_eq _ _ h_sum; push_cast at h; linear_combination h
    · -- NOT a square: s1 = s_prime1, s1²D = r·N_s, c2 = r
      right
      have h_nsq : not_sq.val = 1#u8 := by
        rcases not_sq with ⟨val, hv | hv⟩
        · exact absurd (not_sq_post.mpr (by simp only [hv, Choice.zero])) h_sq_flag
        · exact hv
      constructor
      · rw [show s1.toField = s_prime1.toField from by
          unfold toField; rw [cond_f51_eq s1_post h_nsq]]
        have h_sp1_sq : s_prime1.toField ^ 2 = s_prime.toField ^ 2 := by
          by_cases hc : s_prime_is_pos.val = 1#u8
          · rw [show s_prime1.toField = s_prime_neg.toField from by
              unfold toField; rw [cond_f51_eq s_prime1_post hc]]
            rw [show s_prime_neg.toField = -s_prime.toField from by
              unfold toField
              have h := lift_mod_eq _ 0 s_prime_neg_post1
              push_cast at h; linear_combination h]
            exact neg_sq _
          · rw [show s_prime1.toField = s_prime.toField from by
              unfold toField; rw [cond_f51_eq_neg s_prime1_post hc]]
        rw [h_sp1_sq]
        have h_sp_F : s_prime.toField = x.2.toField * s.toField := by
          unfold toField; have h := lift_mod_eq _ _ s_prime_post1
          push_cast at h; exact h
        rw [h_sp_F, mul_pow]
        have hN0 : Field51_as_Nat N_s % p ≠ 0 := by
          intro h0; exact absurd (N_post_x h0).1 h_sq_flag
        have hD_mod : Field51_as_Nat D % p ≠ 0 := by
          intro hD0; apply h_s1_ne
          have h_dz := (N_post1_D ⟨hN0, hD0⟩).2
          have h_spz : Field51_as_Nat s_prime % p = 0 := by
            have h := s_prime_post1
            simp only [Nat.ModEq] at h
            rw [Nat.mul_mod, h_dz, zero_mul, Nat.zero_mod] at h; exact h
          have h_snz : Field51_as_Nat s_prime_neg % p = 0 := by
            have h := s_prime_neg_post1
            simp only [Nat.ModEq, Nat.zero_mod] at h
            rwa [Nat.add_mod, h_spz, zero_add, Nat.mod_mod] at h
          have h_s1z : Field51_as_Nat s_prime1 % p = 0 := by
            by_cases hc : s_prime_is_pos.val = 1#u8
            · rw [cond_f51_eq s_prime1_post hc]; exact h_snz
            · rw [cond_f51_eq_neg s_prime1_post hc]; exact h_spz
          exact toField_of_mod_zero (by rw [cond_f51_eq s1_post h_nsq]; exact h_s1z)
        have hNSq : ¬∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
            Field51_as_Nat N_s % p := by
          intro hSq; exact absurd (N_post2_D ⟨hN0, hD_mod, hSq⟩).1 h_sq_flag
        have h6 := (N_post3_D ⟨hN0, hD_mod, hNSq⟩).2
        have h_disc_D : x.2.toField ^ 2 * D.toField =
            field.FieldElement51.SQRT_M1_val.toField * N_s.toField := by
          unfold toField
          have lhs_me := ((Nat.mod_modEq (Field51_as_Nat x.2) p).symm.pow 2).mul
            (Nat.mod_modEq (Field51_as_Nat D) p).symm
          have rhs_me := (Nat.mod_modEq
            (Field51_as_Nat field.FieldElement51.SQRT_M1_val) p).symm.mul
            (Nat.mod_modEq (Field51_as_Nat N_s) p).symm
          have hme := lhs_me.trans (h6.trans rhs_me.symm)
          have h := lift_mod_eq _ _ hme; push_cast at h; exact h
        rw [h_i_val] at h_r_F
        linear_combination s.toField ^ 2 * h_disc_D - N_s.toField * h_r_F
      · unfold toField; rw [cond_f51_eq c2_post h_nsq]
  -- Step 2: Prove cp_T.toField ≠ 0
  -- Elligator invariant: the denominator 1 + s² is never zero in 𝔽_p
  -- for the specific s produced by the algorithm.
  have h_cp_T_ne : cp_T.toField ≠ 0 := by
    rw [h_cp_T_F]
    intro h_zero
    have h_s1_sq_eq_m1 : s1.toField ^ 2 = -1 := by linear_combination h_zero
    by_cases hD_mod : Field51_as_Nat D % p = 0
    · -- D ≡ 0 (mod p): s1 must be 0, contradicting s1² = -1
      have h_raw_zero : Field51_as_Nat x.2 % p = 0 := by
        by_cases hN0 : Field51_as_Nat N_s % p = 0
        · grind
        · grind
      have h_sp_mod : Field51_as_Nat s_prime % p = 0 := by
        have : Field51_as_Nat s_prime % p =
            (Field51_as_Nat x.2 * Field51_as_Nat s) % p := s_prime_post1
        rw [Nat.mul_mod, h_raw_zero, zero_mul, Nat.zero_mod] at this; exact this
      have h_spn_mod : Field51_as_Nat s_prime_neg % p = 0 := by
        have h := s_prime_neg_post1
        simp only [Nat.ModEq, Nat.zero_mod] at h
        rwa [Nat.add_mod, h_sp_mod, zero_add, Nat.mod_mod] at h
      have h_sp1_mod : Field51_as_Nat s_prime1 % p = 0 := by
        by_cases hc : s_prime_is_pos.val = 1#u8
        · rw [cond_f51_eq s_prime1_post hc]; exact h_spn_mod
        · rw [cond_f51_eq_neg s_prime1_post hc]; exact h_sp_mod
      have h_s1_mod : Field51_as_Nat s1 % p = 0 := by
        by_cases hc : not_sq.val = 1#u8
        · rw [cond_f51_eq s1_post hc]; exact h_sp1_mod
        · rw [cond_f51_eq_neg s1_post hc]; exact h_raw_zero
      rw [show s1.toField = 0 from toField_of_mod_zero h_s1_mod] at h_s1_sq_eq_m1
      simp at h_s1_sq_eq_m1
    · -- D ≢ 0 (mod p): prove the disjunction and apply the lemma
      have h_disj : s1.toField ^ 2 * D.toField = N_s.toField ∨
          s1.toField ^ 2 * D.toField = r.toField * N_s.toField := by
        have h_s1_ne : s1.toField ≠ 0 := by
          intro hs1
          rw [hs1] at h_s1_sq_eq_m1
          simp at h_s1_sq_eq_m1
        rcases h_s1_sq_c2_cases h_s1_ne with hA | hB
        · exact Or.inl hA.1
        · exact Or.inr hB.1
      exact absurd h_s1_sq_eq_m1
        (elligator_s1_sq_ne_neg_one r.toField N_s.toField D.toField s1.toField
          h_ns_eq_F h_D_eq_F h_disj)
  -- Elligator invariant: N_t · √(ad−1) is never zero in 𝔽_p.
  -- √(ad−1) ≠ 0 follows from sqrt_ad_minus_one_ne_zero;
  have h_cp_Z_ne : cp_Z.toField ≠ 0 := by
    have h_cpz_F : cp_Z.toField = N_t.toField *
        fe.toField := by
      unfold toField; have h := lift_mod_eq _ _ cp_Z_post1; push_cast at h; exact h
    rw [h_cpz_F]; apply mul_ne_zero
    · -- N_t.toField ≠ 0
      -- N_t = c1 * (r-1) * (d-1)² - (-1-d * r) * (r+d) (expand D in h_Nt_eq_F)
      have h_Nt_eq : N_t.toField =
          c2.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 -
          (-1 - Ed25519.d * r.toField) * (r.toField + Ed25519.d) := by
        rw [h_Nt_eq_F, h_D_eq_F]
      intro h0; rw [h_Nt_eq] at h0
      by_cases h_nsq : not_sq.val = 1#u8
      · -- NOT square: c1 = r
        rw [show c2.toField = r.toField from by
          unfold toField; rw [cond_f51_eq c2_post h_nsq]] at h0
        have h_quad : Ed25519.d * (r.toField + 1) ^ 2 +
            ((Ed25519.d - 1) * r.toField) ^ 2 = 0 := by linear_combination h0
        have ⟨hr1, hr2⟩ :=
          non_square_quad_zero Edwards.d_not_square neg_one_is_square h_quad
        rw [show r.toField = -1 from by linear_combination hr1] at hr2
        exact Edwards.d_not_square ⟨1, by
          linear_combination (mul_eq_zero.mp hr2).resolve_right
            (neg_ne_zero.mpr (one_ne_zero (α := CurveField)))⟩
      · -- IS square: c1 = -1
        rw [show c2.toField = (-1 : CurveField) from by
          unfold toField; rw [cond_f51_eq_neg c2_post h_nsq]
          rw [c_post1]
          have h_sum : (p - 1 + 1) % p = 0 % p := by norm_num [p]
          have h := lift_mod_eq _ _ h_sum; push_cast at h; linear_combination h] at h0
        have h_quad : Ed25519.d * (r.toField + 1) ^ 2 +
            (Ed25519.d - 1) ^ 2 = 0 := by linear_combination h0
        have ⟨_, hd1⟩ :=
          non_square_quad_zero Edwards.d_not_square neg_one_is_square h_quad
        exact Edwards.d_not_square ⟨1, by linear_combination hd1⟩
    · -- fe.toField ≠ 0 (SQRT_AD_MINUS_ONE squared ≡ a*d-1 ≢ 0 mod p)
      intro h_zero; unfold toField at h_zero
      have h_fe_mod : Field51_as_Nat fe % p = 0 := by
        rwa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at h_zero
      have h_sq_zero : (↑(Field51_as_Nat fe) : Int) ^ 2 % (↑p : Int) = 0 := by
        have h : (Field51_as_Nat fe) ^ 2 % p = 0 := by rw [Nat.pow_mod, h_fe_mod]; simp
        exact_mod_cast h
      rw [h_sq_zero] at fe_post1
      exact absurd fe_post1.symm (by decide)
  have hZ_ne : ep.Z.toField ≠ 0 := by
    rw [hZ_F]
    exact mul_ne_zero h_cp_Z_ne h_cp_T_ne
  -- Step 3: Completed point lies on the twisted Edwards curve.
  -- This is the key Elligator invariant: the map produces a valid curve point.
  have h_cp_curve :
      Ed25519.a * cp_X.toField ^ 2 * cp_T.toField ^ 2 +
        cp_Y.toField ^ 2 * cp_Z.toField ^ 2 =
      cp_Z.toField ^ 2 * cp_T.toField ^ 2 +
        Ed25519.d * cp_X.toField ^ 2 * cp_Y.toField ^ 2 := by
    -- Lift coordinate postconditions to CurveField
    have h_cp_X_F : cp_X.toField = s_plus_s.toField * D.toField := by
      unfold toField; have h := lift_mod_eq _ _ cp_X_post1; push_cast at h; exact h
    have h_sps_F : s_plus_s.toField = 2 * s1.toField := by
      unfold toField
      have h_nat : Field51_as_Nat s_plus_s = Field51_as_Nat s1 + Field51_as_Nat s1 := by
        unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_range] at hi; rw [s_plus_s_post1 i hi, mul_add]
      rw [h_nat]; push_cast; ring
    have h_cp_Y_F : cp_Y.toField = 1 - s1.toField ^ 2 := by
      unfold toField
      have h_sub := lift_mod_eq _ _ cp_Y_post2
      have hsq := lift_mod_eq _ _ s_sq_post1
      push_cast at h_sub hsq; rw [one_post1, Nat.cast_one] at h_sub
      linear_combination h_sub - hsq
    have h_cp_Z_F : cp_Z.toField = N_t.toField * fe.toField := by
      unfold toField; have h := lift_mod_eq _ _ cp_Z_post1; push_cast at h; exact h
    rw [h_cp_X_F, h_sps_F, h_cp_Y_F, h_cp_Z_F, h_cp_T_F, show Ed25519.a = -1 from rfl]
    -- Establish ω² = -d - 1
    have h_omega_sq : fe.toField ^ 2 = -Ed25519.d - 1 := by
      unfold toField
      have h := (ZMod.intCast_eq_intCast_iff _ _ p).mpr fe_post1
      push_cast at h; simp only [a] at h; rw [h]
      simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul, Ed25519]
    apply elligator_curve_eq_of_inner h_omega_sq
    -- Case split s1=0 ∨ inner identity
    by_cases hs : s1.toField = 0
    · exact Or.inl hs
    · right
      -- Derive s1²·D constraint with c2 info
      have h_disj' := h_s1_sq_c2_cases hs
      -- Case split on square/non-square
      rcases h_disj' with ⟨hA, h_c1⟩ | ⟨hB, h_c1⟩
      · -- Case A: s1²D = N_s, c2 = -1
        have h_nt_A : N_t.toField =
            -(r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
          rw [h_Nt_eq_F, h_c1]; ring
        have step1 : (Ed25519.d + 1) * N_t.toField ^ 2 =
            (D.toField + N_s.toField) ^ 2 +
            Ed25519.d * (D.toField - N_s.toField) ^ 2 := by
          rw [h_nt_A, h_D_eq_F, h_ns_eq_F]; ring
        rw [step1]; exact constr_to_squares hA
      · -- Case B: s1²D = r·N_s, c2 = r
        have h_nt_B : N_t.toField =
            r.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
          rw [h_Nt_eq_F, h_c1];
        have step1 : (Ed25519.d + 1) * N_t.toField ^ 2 =
            (D.toField + r.toField * N_s.toField) ^ 2 +
            Ed25519.d * (D.toField - r.toField * N_s.toField) ^ 2 := by
          rw [h_nt_B, h_D_eq_F, h_ns_eq_F]; ring
        rw [step1]; exact constr_to_squares_r hB
  -- Step 4: EdwardsPoint.IsValid from as_extended_spec
  have h_ep_valid : edwards.EdwardsPoint.IsValid ep := ep_post9
  refine ⟨?_, ?_⟩
  · -- RistrettoPoint.IsValid ep = EdwardsPoint.IsValid ∧ IsSquare (Z² - Y²)
    refine ⟨h_ep_valid, ?_⟩
    simp only [hZ_F, hY_F]
    have h_s_sq_F : s_sq.toField = s1.toField ^ 2 := by
      unfold toField
      have h := lift_mod_eq _ _ s_sq_post1
      push_cast at h; exact h
    have h_cp_Y_F' : cp_Y.toField + s_sq.toField = one.toField := by
      unfold toField
      have h := lift_mod_eq _ _ cp_Y_post2
      push_cast at h; exact h
    have h_cp_T_F' : cp_T.toField = one.toField + s_sq.toField := by
      unfold toField
      have h_nat : Field51_as_Nat cp_T = Field51_as_Nat one + Field51_as_Nat s_sq := by
        unfold Field51_as_Nat
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_range] at hi; rw [cp_T_post1 i hi, mul_add]
      rw [h_nat]; push_cast; ring
    have h_one_F : one.toField = (1 : CurveField) := by
      unfold toField; rw [one_post1]; simp only [Nat.cast_one]
    exact ⟨2 * cp_Z.toField * s1.toField, by
      have h_Y : cp_Y.toField = one.toField - s_sq.toField := by
        linear_combination h_cp_Y_F'
      rw [h_cp_T_F', h_Y, h_s_sq_F, h_one_F]; ring⟩
  · -- toPoint ep = (elligator_ristretto_flavor_pure s.toField).val
    have ⟨hx_ep, hy_ep⟩ := edwards.EdwardsPoint.toPoint_of_isValid h_ep_valid
    have h_impl_x : (toPoint ep).x = ep.X.toField / ep.Z.toField := hx_ep
    have h_impl_y : (toPoint ep).y = ep.Y.toField / ep.Z.toField := hy_ep
    -- Derive implementation coordinate formulas in CurveField
    have h_cp_X_F : cp_X.toField = 2 * s1.toField * D.toField := by
      have h_sps : s_plus_s.toField = 2 * s1.toField := by
        unfold toField
        have h_nat : Field51_as_Nat s_plus_s = Field51_as_Nat s1 + Field51_as_Nat s1 := by
          unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi; rw [s_plus_s_post1 i hi, mul_add]
        rw [h_nat]; push_cast; ring
      have h_mul : cp_X.toField = s_plus_s.toField * D.toField := by
        unfold toField; have h := lift_mod_eq _ _ cp_X_post1; push_cast at h; exact h
      rw [h_mul, h_sps];
    have h_cp_Y_F : cp_Y.toField = 1 - s1.toField ^ 2 := by
      unfold toField
      have h_sub := lift_mod_eq _ _ cp_Y_post2
      have hsq := lift_mod_eq _ _ s_sq_post1
      push_cast at h_sub hsq; rw [one_post1, Nat.cast_one] at h_sub
      linear_combination h_sub - hsq
    have h_cp_Z_F : cp_Z.toField = N_t.toField * fe.toField := by
      unfold toField; have h := lift_mod_eq _ _ cp_Z_post1; push_cast at h; exact h
    have h_sm1 : i.toField = sqrt_m1 := by
      unfold toField sqrt_m1; rw [i_post1]
      exact lift_mod_eq _ _ (by unfold SQRT_M1_raw Field51_as_Nat; decide)
    have h_r_bridge : r.toField = elligator_r s.toField := by
      rw [h_r_F, h_sm1]; unfold elligator_r; rfl
    -- Bridge identities: connect implementation variables to spec step functions
    have h_Ns_bridge : N_s.toField = elligator_Ns s.toField := by
      rw [h_ns_eq_F, h_r_bridge]
      unfold elligator_Ns
      rw [show Ed25519.d = (_root_.d : CurveField) from rfl]
    have h_D_bridge : D.toField = elligator_D s.toField := by
      rw [h_D_eq_F, h_r_bridge]
      unfold elligator_D
      rw [show Ed25519.d = (_root_.d : CurveField) from rfl]; ring
    have h_is_square_of_flag (h_sq_flag : x.1.val = 1#u8) :
        elligator_is_square s.toField := by
      change ∃ x : ZMod p, x ^ 2 * elligator_D s.toField = elligator_Ns s.toField
      rw [← h_D_bridge, ← h_Ns_bridge]
      by_cases hN0 : Field51_as_Nat N_s % p = 0
      · exact ⟨0, by rw [show N_s.toField = (0 : CurveField) from
            toField_of_mod_zero hN0]; ring⟩
      · by_cases hD_mod : Field51_as_Nat D % p = 0
        · exact absurd (N_post1_D ⟨hN0, hD_mod⟩).1
            (by rw [h_sq_flag]; decide)
        · have hSq : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
              Field51_as_Nat N_s % p := by
            by_contra hNSq
            exact absurd (N_post3_D ⟨hN0, hD_mod, hNSq⟩).1
              (by rw [h_sq_flag]; decide)
          exact ⟨x.2.toField,
            lift_sq_mod (N_post2_D ⟨hN0, hD_mod, hSq⟩).2⟩
    have h_not_is_square_of_flag (h_sq_flag : x.1.val ≠ 1#u8) :
        ¬ elligator_is_square s.toField := by
      change ¬ ∃ x : ZMod p, x ^ 2 * elligator_D s.toField = elligator_Ns s.toField
      rw [← h_D_bridge, ← h_Ns_bridge]
      by_cases hN0 : Field51_as_Nat N_s % p = 0
      · exact absurd (N_post_x hN0).1 h_sq_flag
      · by_cases hD_mod : Field51_as_Nat D % p = 0
        · intro ⟨x, hx⟩; apply hN0
          rw [toField_of_mod_zero hD_mod, mul_zero] at hx
          unfold toField at hx
          exact Nat.dvd_iff_mod_eq_zero.mp
            ((ZMod.natCast_eq_zero_iff _ _).mp hx.symm)
        · intro ⟨x, hx⟩; apply h_sq_flag
          exact (N_post2_D ⟨hN0, hD_mod, ⟨ZMod.val x, by
            unfold toField at hx
            exact ((Nat.ModEq.mul_left (ZMod.val x ^ 2)
              (Nat.mod_modEq (Field51_as_Nat D) p).symm).symm.trans
              ((ZMod.natCast_eq_natCast_iff _ _ p).mp (by
                push_cast
                simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
                exact hx)))⟩⟩).1
    have h_c2_bridge : c2.toField = elligator_c s.toField := by
      unfold elligator_c
      by_cases h_sq_flag : x.1.val = 1#u8
      · -- Square case: c2 = -1
        have h_nsq : not_sq.val ≠ 1#u8 := by
          have := not_sq_post.mp h_sq_flag; subst this; decide
        have h_is_sq : elligator_is_square s.toField := h_is_square_of_flag h_sq_flag
        rw [if_pos h_is_sq]
        unfold toField; rw [cond_f51_eq_neg c2_post h_nsq]; rw [c_post1]
        have h_sum : (p - 1 + 1) % p = 0 % p := by norm_num [p]
        have h := lift_mod_eq _ _ h_sum; push_cast at h; linear_combination h
      · -- Non-square case: c2 = r
        have h_nsq : not_sq.val = 1#u8 := by
          rcases not_sq with ⟨val, hv | hv⟩
          · exact absurd (not_sq_post.mpr (by simp only [Choice.zero, hv])) h_sq_flag
          · exact hv
        have h_not_sq : ¬ elligator_is_square s.toField := h_not_is_square_of_flag h_sq_flag
        rw [if_neg h_not_sq]
        rw [show c2.toField = r.toField from by
          unfold toField; rw [cond_f51_eq c2_post h_nsq]]
        exact h_r_bridge
    have h_s1_bridge : s1.toField = elligator_s s.toField := by
      unfold elligator_s
      by_cases h_sq_flag : x.1.val = 1#u8
      · -- Square case: s1 = x.2
        have h_nsq : not_sq.val ≠ 1#u8 := by
          have := not_sq_post.mp h_sq_flag; subst this; decide
        have h_is_sq : elligator_is_square s.toField := h_is_square_of_flag h_sq_flag
        rw [if_pos h_is_sq]
        rw [show s1.toField = x.2.toField from by
          unfold toField; rw [cond_f51_eq_neg s1_post h_nsq]]
        -- Goal: x.2.toField = abs_edwards (sqrt (elligator_ratio s.toField))
        apply eq_abs_edwards_of_sq_eq (by decide : p % 2 = 1)
        · -- x.2.toField ^ 2 = (sqrt (elligator_ratio s.toField)) ^ 2
          suffices h_sq_eq : x.2.toField ^ 2 = elligator_ratio s.toField by
            have hIsSq : IsSquare (elligator_ratio s.toField) :=
              ⟨x.2.toField, by rw [← h_sq_eq]; ring⟩
            rw [h_sq_eq, sqrt_sq hIsSq]
          unfold elligator_ratio; rw [← h_Ns_bridge, ← h_D_bridge]
          by_cases hN0 : Field51_as_Nat N_s % p = 0
          · rw [toField_of_mod_zero (N_post_x hN0).2,
                toField_of_mod_zero hN0]; simp
          · by_cases hD_mod : Field51_as_Nat D % p = 0
            · exact absurd (N_post1_D ⟨hN0, hD_mod⟩).1
                (by rw [h_sq_flag]; decide)
            · have hSq : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                  Field51_as_Nat N_s % p := by
                by_contra hNSq
                exact absurd (N_post3_D ⟨hN0, hD_mod, hNSq⟩).1
                  (by rw [h_sq_flag]; decide)
              have h_r_sq := lift_sq_mod (N_post2_D ⟨hN0, hD_mod, hSq⟩).2
              have hD_ne : D.toField ≠ 0 := by
                intro h; apply hD_mod; unfold toField at h
                exact Nat.dvd_iff_mod_eq_zero.mp
                  ((ZMod.natCast_eq_zero_iff _ _).mp h)
              field_simp [hD_ne]; exact h_r_sq
        · -- x.2.toField.val % 2 = 0
          unfold toField; rw [ZMod.val_natCast]; exact x_post2
      · -- Non-square case: s1 = s_prime1
        have h_nsq : not_sq.val = 1#u8 := by
          rcases not_sq with ⟨val, hv | hv⟩
          · exact absurd (not_sq_post.mpr (by simp only [Choice.zero, hv])) h_sq_flag
          · exact hv
        have h_not_sq : ¬ elligator_is_square s.toField := h_not_is_square_of_flag h_sq_flag
        rw [if_neg h_not_sq]
        rw [show s1.toField = s_prime1.toField from by
          unfold toField; rw [cond_f51_eq s1_post h_nsq]]
        -- Step A: s_prime.toField = x.2.toField * s.toField
        have h_sp_F : s_prime.toField = x.2.toField * s.toField := by
          unfold toField; have h := lift_mod_eq _ _ s_prime_post1
          push_cast at h; exact h
        -- Step B: s_prime_neg.toField = -s_prime.toField
        have h_spn_F : s_prime_neg.toField = -s_prime.toField := by
          unfold toField
          have h := lift_mod_eq _ 0 s_prime_neg_post1
          push_cast at h; linear_combination h
        -- Step C: s_prime1 = -(abs_edwards(s_prime))
        have h_sp1_neg_abs : s_prime1.toField = -(abs_edwards s_prime.toField) := by
          unfold abs_edwards is_negative
          by_cases hc : c1.val = 1#u8
          · -- s_prime is negative (odd val): s_prime1 = s_prime, abs = -s_prime
            have h_sip : s_prime_is_pos.val ≠ 1#u8 := by
              have := s_prime_is_pos_post.mp hc; subst this; decide
            rw [show s_prime1.toField = s_prime.toField from by
              unfold toField; rw [cond_f51_eq_neg s_prime1_post h_sip]]
            have h_neg : (s_prime.toField.val % 2 == 1) = true := by
              simp only [beq_iff_eq]; exact c1_post.mp hc
            rw [if_pos h_neg]; ring
          · -- s_prime is non-negative (even val): s_prime1 = -s_prime, abs = s_prime
            have h_sip : s_prime_is_pos.val = 1#u8 := by
              rcases s_prime_is_pos with ⟨val, hv | hv⟩
              · exact absurd (s_prime_is_pos_post.mpr (by simp only [Choice.zero, hv])) hc
              · exact hv
            rw [show s_prime1.toField = s_prime_neg.toField from by
              unfold toField; rw [cond_f51_eq s_prime1_post h_sip]]
            rw [h_spn_F]
            have h_not_neg : ¬(s_prime.toField.val % 2 == 1) = true := by
              simp only [beq_iff_eq]; exact fun h => hc (c1_post.mpr h)
            rw [if_neg h_not_neg]
        -- Step D: abs_edwards(s_prime) = abs_edwards(sqrt(i * ratio) * s)
        rw [h_sp1_neg_abs]; simp only [neg_inj]
        rw [h_sp_F]
        -- Goal: abs_edwards(x.2 * s) = abs_edwards(sqrt(sqrt_m1*ratio) * s)
        apply abs_edwards_eq_of_sq_eq_sq (by decide : p % 2 = 1)
        rw [mul_pow, mul_pow]
        have hN0 : Field51_as_Nat N_s % p ≠ 0 := by
          intro h0; exact absurd (N_post_x h0).1 h_sq_flag
        suffices h_key : x.2.toField ^ 2 =
            sqrt (sqrt_m1 * elligator_ratio s.toField) ^ 2 by rw [h_key]
        by_cases hD_mod : Field51_as_Nat D % p = 0
        · -- D = 0: x.2 = 0, ratio = 0
          rw [toField_of_mod_zero (N_post1_D ⟨hN0, hD_mod⟩).2]
          unfold elligator_ratio; rw [← h_Ns_bridge, ← h_D_bridge,
            toField_of_mod_zero hD_mod]; simp only [ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow, inv_zero, mul_zero]
          exact (sqrt_sq ⟨0, by ring⟩).symm
        · -- D ≠ 0: use N_post3_D
          have hNSq : ¬∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
              Field51_as_Nat N_s % p := by
            intro hSq; exact absurd (N_post2_D ⟨hN0, hD_mod, hSq⟩).1 h_sq_flag
          have h6 := (N_post3_D ⟨hN0, hD_mod, hNSq⟩).2
          have h_disc_D : x.2.toField ^ 2 * D.toField =
              field.FieldElement51.SQRT_M1_val.toField * N_s.toField := by
            unfold toField
            have lhs_me := ((Nat.mod_modEq (Field51_as_Nat x.2) p).symm.pow 2).mul
              (Nat.mod_modEq (Field51_as_Nat D) p).symm
            have rhs_me := (Nat.mod_modEq
              (Field51_as_Nat field.FieldElement51.SQRT_M1_val) p).symm.mul
              (Nat.mod_modEq (Field51_as_Nat N_s) p).symm
            have hme := lhs_me.trans (h6.trans rhs_me.symm)
            have h := lift_mod_eq _ _ hme; push_cast at h; exact h
          have hD_ne : D.toField ≠ 0 := by
            intro h; apply hD_mod; unfold toField at h
            exact Nat.dvd_iff_mod_eq_zero.mp
              ((ZMod.natCast_eq_zero_iff _ _).mp h)
          have h_disc_sq : x.2.toField ^ 2 =
              sqrt_m1 * elligator_ratio s.toField := by
            unfold elligator_ratio; rw [← h_Ns_bridge, ← h_D_bridge]
            rw [← h_i_val, h_sm1] at h_disc_D
            field_simp [hD_ne]; exact h_disc_D
          have hIsSq : IsSquare (sqrt_m1 * elligator_ratio s.toField) :=
            ⟨x.2.toField, by rw [← h_disc_sq]; ring⟩
          rw [h_disc_sq, sqrt_sq hIsSq]
    have h_Nt_bridge : N_t.toField = elligator_Nt s.toField := by
      rw [h_Nt_eq_F, h_r_bridge, h_D_bridge, h_c2_bridge]
      unfold elligator_Nt
      rw [show Ed25519.d = (_root_.d : CurveField) from rfl]
    have h_omega_bridge : fe.toField = sqrt_ad_minus_one := by
      unfold toField; rw [fe_post3, sqrt_ad_minus_one_eq_val]
      exact lift_mod_eq _ _ (by
        unfold SQRT_AD_MINUS_ONE_raw Field51_as_Nat; decide)
    ext
    · -- x coordinate
      rw [h_impl_x, hX_F, hZ_F]
      rw [(IsUnit.mk0 _ h_cp_T_ne).mul_div_mul_right cp_X.toField cp_Z.toField]
      rw [h_cp_X_F, h_cp_Z_F]
      simp only [elligator_pure_val_x]
      unfold elligator_ristretto_flavor_x
      rw [h_s1_bridge, h_D_bridge, h_Nt_bridge, h_omega_bridge]
    · -- y coordinate
      rw [h_impl_y, hY_F, hZ_F]
      rw [show cp_Z.toField * cp_T.toField = cp_T.toField * cp_Z.toField from mul_comm _ _]
      rw [(IsUnit.mk0 _ h_cp_Z_ne).mul_div_mul_right cp_Y.toField cp_T.toField]
      rw [h_cp_Y_F, h_cp_T_F]
      simp only [elligator_pure_val_y]
      unfold elligator_ristretto_flavor_y
      rw [h_s1_bridge]


end curve25519_dalek.ristretto.RistrettoPoint
