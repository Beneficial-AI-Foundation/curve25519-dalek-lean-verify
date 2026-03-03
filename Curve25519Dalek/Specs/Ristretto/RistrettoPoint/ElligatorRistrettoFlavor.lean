/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.FunsExternal
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
open Edwards
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

/-- MINUS_ONE.toField = -1 in CurveField. -/
private lemma MINUS_ONE_toField :
    backend.serial.u64.constants.MINUS_ONE.toField = (-1 : CurveField) := by
  unfold toField; rw [backend.serial.u64.constants.MINUS_ONE_spec]
  have : (p - 1 : ℕ) + 1 = p := by unfold p; omega
  have h := lift_mod_eq _ _
    (show (p - 1 + 1) % p = 0 % p from by rw [this, Nat.mod_self, Nat.zero_mod])
  push_cast at h; linear_combination h

/-- EDWARDS_D.toField = Ed25519.d in CurveField. -/
private lemma EDWARDS_D_toField :
    backend.serial.u64.constants.EDWARDS_D.toField = Ed25519.d := by
  unfold toField; rw [backend.serial.u64.constants.EDWARDS_D_spec]; rfl

/-- ONE_MINUS_EDWARDS_D_SQUARED.toField = 1 - Ed25519.d² in CurveField. -/
private lemma ONE_MINUS_EDWARDS_D_SQUARED_toField :
    backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED.toField =
    1 - Ed25519.d ^ 2 := by
  unfold toField
  have h_sum : (Field51_as_Nat backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED +
      d ^ 2) % p = 1 % p := by
    rw [backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED_spec]; norm_num [d, p]
  have h := lift_mod_eq _ _ h_sum; push_cast at h
  change _ = 1 - (d : CurveField) ^ 2; linear_combination h

/-- EDWARDS_D_MINUS_ONE_SQUARED.toField = (Ed25519.d - 1)² in CurveField. -/
private lemma EDWARDS_D_MINUS_ONE_SQUARED_toField :
    backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED.toField =
    (Ed25519.d - 1) ^ 2 := by
  unfold toField
  rw [backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED_spec]
  have h := lift_mod_eq _ _ (Nat.mod_mod_of_dvd ((d - 1) ^ 2) (dvd_refl p))
  rw [h]; push_cast [Nat.cast_sub (show 1 ≤ d from by unfold d; omega)]
  simp only [Ed25519]

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
  · exact h_s_valid -- 1: s < 2^54 (square precond)
  · intro i hi;
    unfold backend.serial.u64.constants.SQRT_M1
    interval_cases i <;> decide -- 2: SQRT_M1 < 2^54
  · intro i hi; have := r_0_sq_post_2 i hi; omega -- 3: r_0_sq < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 4: r < 2^53
  · intro i hi;
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide -- 5: ONE < 2^53
  · intro i hi;
    unfold backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED
    interval_cases i <;> decide -- 6: ONE_MINUS_EDWARDS_D_SQUARED < 2^54
  · intro i hi;
    unfold backend.serial.u64.constants.EDWARDS_D
    interval_cases i <;> decide -- 7: EDWARDS_D < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 8: r < 2^54
  · intro i hi;
    unfold backend.serial.u64.constants.MINUS_ONE
    interval_cases i <;> decide -- 9: MINUS_ONE < 2^63
  · intro i hi; have := d_times_r_post_2 i hi; omega -- 10: d_times_r < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 11: r < 2^53
  · intro i hi;
    unfold backend.serial.u64.constants.EDWARDS_D
    interval_cases i <;> decide -- 12: EDWARDS_D < 2^53
  · intro i hi; have := c_minus_dr_post_1 i hi; omega -- 13: c_minus_dr < 2^54
  · intro i hi; have := N_s_post_2 i hi; omega -- 14: N_s ≤ 2^52-1
  · intro i hi; have := D_post_2 i hi; omega -- 15: D ≤ 2^52-1
  · intro i hi; have := __discr_post_1 i hi; omega -- 16: __discr.2 < 2^54
  · exact h_s_valid -- 17: s < 2^54 (mul rhs)
  · intro i hi; have := s_prime_post_2 i hi; omega -- 18: s_prime < 2^54
  · intro i hi; have := r_post_2 i hi; omega -- 19: r < 2^63
  · intro i hi;
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide -- 20: ONE < 2^54
  · intro i hi; simp only [c1_post i hi] -- 21: c1 < 2^54 (conditional_assign)
    split
    · have := r_post_2 i hi; omega
    · unfold backend.serial.u64.constants.MINUS_ONE; interval_cases i <;> decide
  · intro i hi; have := r_minus_one_post_1 i hi; omega -- 22: r_minus_one < 2^54
  · intro i hi; have := c_r_minus_one_post_2 i hi; omega -- 23: c_r_minus_one < 2^54
  · intro i hi; -- 24: EDWARDS_D_MINUS_ONE_SQUARED < 2^54
    unfold backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED
    interval_cases i <;> decide
  · intro i hi; have := c_r_minus_one_post_2 i hi;
    grind only [#b83a]
  · intro i hi; have := D_post_2 i hi; omega -- 26: D < 2^54
  · intro i hi; simp only [s1_post i hi] -- 27: s1 < 2^54 (conditional)
    split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post_2 i hi; omega
      · have := s_prime_post_2 i hi; omega
    · have := __discr_post_1 i hi; omega
  · intro i hi; simp only [s1_post i hi] -- 28: s1 < 2^53 (conditional)
    split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post_2 i hi; omega
      · have := s_prime_post_2 i hi; omega
    · have := __discr_post_1 i hi; omega
  · intro i hi; simp only [s1_post i hi] -- 29: s1 < 2^53 (conditional)
    split
    · simp only [s_prime1_post i hi]; split
      · have := s_prime_neg_post_2 i hi; omega
      · have := s_prime_post_2 i hi; omega
    · have := __discr_post_1 i hi; omega
  · intro i hi; have := D_post_2 i hi; omega -- 30: D < 2^54
  · intro i hi; have := N_t_post_1 i hi; omega -- 31: N_t < 2^54
  · intro i hi; -- 32: SQRT_AD_MINUS_ONE < 2^54
    unfold backend.serial.u64.constants.SQRT_AD_MINUS_ONE
    interval_cases i <;> decide
  · intro i hi; -- 33: ONE < 2^63
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide
  · intro i hi; have := s_sq_post_2 i hi; omega -- 34: s_sq < 2^54
  · intro i hi; -- 35: ONE < 2^53
    unfold backend.serial.u64.field.FieldElement51.ONE
    interval_cases i <;> decide
  · intro i hi; have := s_sq_post_2 i hi; omega -- 36: s_sq < 2^53
  · intro i hi; have h := cp_X_post_2 i hi -- 37: cp_X < 2^54
    simp only [Array.getElem!_Nat_eq] at h ⊢; omega
  · intro i hi; have h := cp_Y_post_1 i hi -- 38: cp_Y < 2^54
    simp only [Array.getElem!_Nat_eq] at h ⊢; omega
  · intro i hi; have h := cp_Z_post_2 i hi -- 39: cp_Z < 2^54
    simp only [Array.getElem!_Nat_eq] at h ⊢; omega
  · -- 40: IsValid ∧ toPoint = elligator_ristretto_flavor_pure
    -- Step 1: Lift arithmetic postconditions to field equalities
    have hX_F : ep.X.toField = cp_X.toField * cp_T.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_1
      push_cast at h; exact h
    have hY_F : ep.Y.toField = cp_Y.toField * cp_Z.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_2
      push_cast at h; exact h
    have hZ_F : ep.Z.toField = cp_Z.toField * cp_T.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_3
      push_cast at h; exact h
    have hT_F : ep.T.toField = cp_X.toField * cp_Y.toField := by
      unfold toField
      have h := lift_mod_eq _ _ ep_post_4
      push_cast at h; exact h
    have h_cp_T_F : cp_T.toField = 1 + s1.toField ^ 2 := by
        unfold toField
        have h_nat : Field51_as_Nat cp_T = Field51_as_Nat ONE + Field51_as_Nat s_sq := by
          unfold Field51_as_Nat
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi; rw [cp_T_post_1 i hi, mul_add]
        rw [h_nat]; push_cast
        have hsq := lift_mod_eq _ _ s_sq_post_1
        push_cast at hsq; rw [hsq, ONE_spec]
        simp only [Nat.cast_one]
    -- Shared postcondition lifts (used by h_cp_T_ne, h_cp_Z_ne, h_cp_curve)
    have h_rpo_F : r_plus_one.toField = r.toField + 1 := by
      unfold toField
      have h_nat : Field51_as_Nat r_plus_one = Field51_as_Nat r + Field51_as_Nat ONE := by
        unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_range] at hi; rw [r_plus_one_post_1 i hi, mul_add]
      rw [h_nat]; push_cast; rw [ONE_spec]; simp only [Nat.cast_one]
    have h_ns_eq_F : N_s.toField = (r.toField + 1) * (1 - Ed25519.d ^ 2) := by
      have hN : N_s.toField = r_plus_one.toField *
          backend.serial.u64.constants.ONE_MINUS_EDWARDS_D_SQUARED.toField := by
        unfold toField; have h := lift_mod_eq _ _ N_s_post_1; push_cast at h; exact h
      rw [hN, h_rpo_F, ONE_MINUS_EDWARDS_D_SQUARED_toField]
    have h_rpd_F : r_plus_d.toField = r.toField + Ed25519.d := by
      unfold toField
      have h_nat : Field51_as_Nat r_plus_d =
          Field51_as_Nat r + Field51_as_Nat backend.serial.u64.constants.EDWARDS_D := by
        unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_range] at hi; rw [r_plus_d_post_1 i hi, mul_add]
      rw [h_nat]; push_cast; rw [backend.serial.u64.constants.EDWARDS_D_spec]; rfl
    have h_cmdr_F : c_minus_dr.toField = -1 - Ed25519.d * r.toField := by
      have hD_sub : c_minus_dr.toField + d_times_r.toField =
          backend.serial.u64.constants.MINUS_ONE.toField := by
        unfold toField; have h := lift_mod_eq _ _ c_minus_dr_post_2; push_cast at h; exact h
      have hD_dr : d_times_r.toField =
          backend.serial.u64.constants.EDWARDS_D.toField * r.toField := by
        unfold toField; have h := lift_mod_eq _ _ d_times_r_post_1; push_cast at h; exact h
      rw [MINUS_ONE_toField] at hD_sub; rw [EDWARDS_D_toField] at hD_dr
      linear_combination hD_sub - hD_dr
    have h_D_eq_F : D.toField =
        (-1 - Ed25519.d * r.toField) * (r.toField + Ed25519.d) := by
      have hD : D.toField = c_minus_dr.toField * r_plus_d.toField := by
        unfold toField; have h := lift_mod_eq _ _ D_post_1; push_cast at h; exact h
      rw [hD, h_cmdr_F, h_rpd_F]
    have h_rm1_F : r_minus_one.toField = r.toField - 1 := by
      unfold toField; have h := lift_mod_eq _ _ r_minus_one_post_2
      push_cast at h; rw [ONE_spec, Nat.cast_one] at h; linear_combination h
    have h_cr_F : c_r_minus_one.toField = c1.toField * r_minus_one.toField := by
      unfold toField; have h := lift_mod_eq _ _ c_r_minus_one_post_1
      push_cast at h; exact h
    have h_crd_F : c_r_minus_one_d.toField = c_r_minus_one.toField *
        backend.serial.u64.constants.EDWARDS_D_MINUS_ONE_SQUARED.toField := by
      unfold toField; have h := lift_mod_eq _ _ c_r_minus_one_d_post_1
      push_cast at h; exact h
    have h_Nt_add_F : N_t.toField + D.toField = c_r_minus_one_d.toField := by
      unfold toField; have h := lift_mod_eq _ _ N_t_post_2; push_cast at h; exact h
    have h_Nt_eq_F : N_t.toField =
        c1.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
      have : N_t.toField = c_r_minus_one_d.toField - D.toField := by
        linear_combination h_Nt_add_F
      rw [this, h_crd_F, EDWARDS_D_MINUS_ONE_SQUARED_toField, h_cr_F, h_rm1_F]
    -- Step 2: Prove cp_T.toField ≠ 0
    -- Elligator invariant: the denominator 1 + s² is never zero in 𝔽_p
    -- for the specific s produced by the algorithm.
    have h_cp_T_ne : cp_T.toField ≠ 0 := by
      rw [h_cp_T_F]
      intro h_zero
      have h_s1_sq_eq_m1 : s1.toField ^ 2 = -1 := by linear_combination h_zero
      by_cases hD_mod : Field51_as_Nat D % p = 0
      · -- D ≡ 0 (mod p): s1 must be 0, contradicting s1² = -1
        have h_raw_zero : Field51_as_Nat __discr.2 % p = 0 := by
          by_cases hN0 : Field51_as_Nat N_s % p = 0
          · exact (__discr_post_3 hN0).2
          · exact (__discr_post_4 ⟨hN0, hD_mod⟩).2
        have h_sp_mod : Field51_as_Nat s_prime % p = 0 := by
          have : Field51_as_Nat s_prime % p =
              (Field51_as_Nat __discr.2 * Field51_as_Nat s) % p := s_prime_post_1
          rw [Nat.mul_mod, h_raw_zero, zero_mul, Nat.zero_mod] at this; exact this
        have h_spn_mod : Field51_as_Nat s_prime_neg % p = 0 := by
          have := s_prime_neg_post_1
          rwa [Nat.add_mod, h_sp_mod, zero_add, Nat.mod_mod] at this
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
          by_cases h_sq_flag : __discr.1.val = 1#u8
          · -- IS a square: not_sq=0, s1 = __discr.2
            left
            have h_nsq : not_sq.val ≠ 1#u8 := by
              rw [not_sq_post, if_pos h_sq_flag]; decide
            rw [show s1.toField = __discr.2.toField from by
              unfold toField; rw [cond_f51_eq_neg s1_post h_nsq]]
            have h_eq : (Field51_as_Nat __discr.2 % p) ^ 2 * (Field51_as_Nat D % p) % p =
                Field51_as_Nat N_s % p := by
              by_cases hN0 : Field51_as_Nat N_s % p = 0
              · rw [(__discr_post_3 hN0).2]; simp only [ne_eq, OfNat.ofNat_ne_zero,
                not_false_eq_true, zero_pow, zero_mul, Nat.zero_mod, hN0]
              · have hSq : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p = Field51_as_Nat N_s % p := by
                  by_contra hNSq
                  have := (__discr_post_6 ⟨hN0, hD_mod, hNSq⟩).1
                  rw [h_sq_flag] at this; exact absurd this (by decide)
                exact (__discr_post_5 ⟨hN0, hD_mod, hSq⟩).2
            exact lift_sq_mod h_eq
          · -- NOT a square: not_sq=1, s1 = s_prime1
            right
            have h_nsq : not_sq.val = 1#u8 := by rw [not_sq_post, if_neg h_sq_flag]
            rw [show s1.toField = s_prime1.toField from by
              unfold toField; rw [cond_f51_eq s1_post h_nsq]]
            have h_sp1_sq : s_prime1.toField ^ 2 = s_prime.toField ^ 2 := by
              by_cases hc : s_prime_is_pos.val = 1#u8
              · rw [show s_prime1.toField = s_prime_neg.toField from by
                  unfold toField; rw [cond_f51_eq s_prime1_post hc]]
                rw [show s_prime_neg.toField = -s_prime.toField from by
                  unfold toField
                  have h := lift_mod_eq _ 0
                    (s_prime_neg_post_1.trans (Nat.zero_mod p).symm)
                  push_cast at h; linear_combination h]
                exact neg_sq _
              · rw [show s_prime1.toField = s_prime.toField from by
                  unfold toField; rw [cond_f51_eq_neg s_prime1_post hc]]
            rw [h_sp1_sq]
            have h_sp_F : s_prime.toField = __discr.2.toField * s.toField := by
              unfold toField; have h := lift_mod_eq _ _ s_prime_post_1
              push_cast at h; exact h
            rw [h_sp_F, mul_pow]
            have hN0 : Field51_as_Nat N_s % p ≠ 0 := by
              intro h0; have := (__discr_post_3 h0).1; exact absurd this h_sq_flag
            have hNSq : ¬∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                Field51_as_Nat N_s % p := by
              intro hSq; have := (__discr_post_5 ⟨hN0, hD_mod, hSq⟩).1
              exact absurd this h_sq_flag
            have h6 := (__discr_post_6 ⟨hN0, hD_mod, hNSq⟩).2
            have h_disc_D : __discr.2.toField ^ 2 * D.toField =
                backend.serial.u64.constants.SQRT_M1.toField * N_s.toField := by
              unfold toField
              have lhs_me := ((Nat.mod_modEq (Field51_as_Nat __discr.2) p).symm.pow 2).mul
                (Nat.mod_modEq (Field51_as_Nat D) p).symm
              have rhs_me := (Nat.mod_modEq
                (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) p).symm.mul
                (Nat.mod_modEq (Field51_as_Nat N_s) p).symm
              have hme := lhs_me.trans (h6.trans rhs_me.symm)
              have h := lift_mod_eq _ _ hme; push_cast at h; exact h
            have h_r_F : r.toField =
                backend.serial.u64.constants.SQRT_M1.toField * s.toField ^ 2 := by
              unfold toField
              have hme := r_post_1.trans (Nat.ModEq.mul_left
                (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) r_0_sq_post_1)
              have h := lift_mod_eq _ _ hme; push_cast at h; exact h
            linear_combination s.toField ^ 2 * h_disc_D - N_s.toField * h_r_F
        exact absurd h_s1_sq_eq_m1
          (elligator_s1_sq_ne_neg_one r.toField N_s.toField D.toField s1.toField
            h_ns_eq_F h_D_eq_F h_disj)
    -- Elligator invariant: N_t · √(ad−1) is never zero in 𝔽_p.
    -- √(ad−1) ≠ 0 follows from sqrt_ad_minus_one_ne_zero;
    have h_cp_Z_ne : cp_Z.toField ≠ 0 := by
      have h_cpz_F : cp_Z.toField = N_t.toField *
          backend.serial.u64.constants.SQRT_AD_MINUS_ONE.toField := by
        unfold toField; have h := lift_mod_eq _ _ cp_Z_post_1; push_cast at h; exact h
      rw [h_cpz_F]; apply mul_ne_zero
      · -- N_t.toField ≠ 0
        -- N_t = c1*(r-1)*(d-1)² - (-1-d*r)*(r+d) (expand D in h_Nt_eq_F)
        have h_Nt_eq : N_t.toField =
            c1.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 -
            (-1 - Ed25519.d * r.toField) * (r.toField + Ed25519.d) := by
          rw [h_Nt_eq_F, h_D_eq_F]
        intro h0; rw [h_Nt_eq] at h0
        by_cases h_nsq : not_sq.val = 1#u8
        · -- NOT square: c1 = r
          rw [show c1.toField = r.toField from by
            unfold toField; rw [cond_f51_eq c1_post h_nsq]] at h0
          have h_quad : Ed25519.d * (r.toField + 1) ^ 2 +
              ((Ed25519.d - 1) * r.toField) ^ 2 = 0 := by linear_combination h0
          have ⟨hr1, hr2⟩ :=
            non_square_quad_zero Edwards.d_not_square neg_one_is_square h_quad
          rw [show r.toField = -1 from by linear_combination hr1] at hr2
          exact Edwards.d_not_square ⟨1, by
            linear_combination (mul_eq_zero.mp hr2).resolve_right
              (neg_ne_zero.mpr (one_ne_zero (α := CurveField)))⟩
        · -- IS square: c1 = -1
          rw [show c1.toField = (-1 : CurveField) from by
            unfold toField; rw [cond_f51_eq_neg c1_post h_nsq]
            exact MINUS_ONE_toField] at h0
          have h_quad : Ed25519.d * (r.toField + 1) ^ 2 +
              (Ed25519.d - 1) ^ 2 = 0 := by linear_combination h0
          have ⟨_, hd1⟩ :=
            non_square_quad_zero Edwards.d_not_square neg_one_is_square h_quad
          exact Edwards.d_not_square ⟨1, by linear_combination hd1⟩
      · -- SQRT_AD_MINUS_ONE.toField ≠ 0
        unfold backend.serial.u64.constants.SQRT_AD_MINUS_ONE
        decide
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
        unfold toField; have h := lift_mod_eq _ _ cp_X_post_1; push_cast at h; exact h
      have h_sps_F : s_plus_s.toField = 2 * s1.toField := by
        unfold toField
        have h_nat : Field51_as_Nat s_plus_s = Field51_as_Nat s1 + Field51_as_Nat s1 := by
          unfold Field51_as_Nat; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi; rw [s_plus_s_post_1 i hi, mul_add]
        rw [h_nat]; push_cast; ring
      have h_cp_Y_F : cp_Y.toField = 1 - s1.toField ^ 2 := by
        unfold toField
        have h_sub := lift_mod_eq _ _ cp_Y_post_2
        have hsq := lift_mod_eq _ _ s_sq_post_1
        push_cast at h_sub hsq; rw [ONE_spec, Nat.cast_one] at h_sub
        linear_combination h_sub - hsq
      have h_cp_Z_F : cp_Z.toField = N_t.toField *
          backend.serial.u64.constants.SQRT_AD_MINUS_ONE.toField := by
        unfold toField; have h := lift_mod_eq _ _ cp_Z_post_1; push_cast at h; exact h
      rw [h_cp_X_F, h_sps_F, h_cp_Y_F, h_cp_Z_F, h_cp_T_F, show Ed25519.a = -1 from rfl]
      -- Establish ω² = -d - 1
      have h_omega_sq : backend.serial.u64.constants.SQRT_AD_MINUS_ONE.toField ^ 2 =
          -Ed25519.d - 1 := by
        unfold toField
        have h := (ZMod.intCast_eq_intCast_iff _ _ p).mpr
          backend.serial.u64.constants.SQRT_AD_MINUS_ONE_spec
        push_cast at h; simp only [a] at h; rw [h]; simp only [Int.reduceNeg, Int.cast_neg,
          Int.cast_one, neg_mul, one_mul, Ed25519];
      apply elligator_curve_eq_of_inner h_omega_sq
      -- Case split s1=0 ∨ inner identity
      by_cases hs : s1.toField = 0
      · exact Or.inl hs
      · right
        -- Derive s1²·D constraint with c1 info
        have h_disj' :
            (s1.toField ^ 2 * D.toField = N_s.toField ∧ c1.toField = -1) ∨
            (s1.toField ^ 2 * D.toField = r.toField * N_s.toField ∧
             c1.toField = r.toField) := by
          by_cases h_sq_flag : __discr.1.val = 1#u8
          · -- IS a square: s1 = __discr.2, s1²D = N_s, c1 = -1
            left
            have h_nsq : not_sq.val ≠ 1#u8 := by
              rw [not_sq_post, if_pos h_sq_flag]; decide
            constructor
            · rw [show s1.toField = __discr.2.toField from by
                unfold toField; rw [cond_f51_eq_neg s1_post h_nsq]]
              have h_eq : (Field51_as_Nat __discr.2 % p) ^ 2 * (Field51_as_Nat D % p) % p =
                  Field51_as_Nat N_s % p := by
                by_cases hN0 : Field51_as_Nat N_s % p = 0
                · rw [(__discr_post_3 hN0).2]; simp only [ne_eq, OfNat.ofNat_ne_zero,
                    not_false_eq_true, zero_pow, zero_mul, Nat.zero_mod, hN0]
                · have hD_mod : Field51_as_Nat D % p ≠ 0 := by
                    intro hD0
                    exact absurd (__discr_post_4 ⟨hN0, hD0⟩).1 (by rw [h_sq_flag]; decide)
                  have hSq : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                      Field51_as_Nat N_s % p := by
                    by_contra hNSq
                    exact absurd (__discr_post_6 ⟨hN0, hD_mod, hNSq⟩).1
                      (by rw [h_sq_flag]; decide)
                  exact (__discr_post_5 ⟨hN0, hD_mod, hSq⟩).2
              exact lift_sq_mod h_eq
            · unfold toField; rw [cond_f51_eq_neg c1_post h_nsq]
              exact MINUS_ONE_toField
          · -- NOT a square: s1 = s_prime1, s1²D = r·N_s, c1 = r
            right
            have h_nsq : not_sq.val = 1#u8 := by rw [not_sq_post, if_neg h_sq_flag]
            constructor
            · rw [show s1.toField = s_prime1.toField from by
                unfold toField; rw [cond_f51_eq s1_post h_nsq]]
              have h_sp1_sq : s_prime1.toField ^ 2 = s_prime.toField ^ 2 := by
                by_cases hc : s_prime_is_pos.val = 1#u8
                · rw [show s_prime1.toField = s_prime_neg.toField from by
                    unfold toField; rw [cond_f51_eq s_prime1_post hc]]
                  rw [show s_prime_neg.toField = -s_prime.toField from by
                    unfold toField
                    have h := lift_mod_eq _ 0
                      (s_prime_neg_post_1.trans (Nat.zero_mod p).symm)
                    push_cast at h; linear_combination h]
                  exact neg_sq _
                · rw [show s_prime1.toField = s_prime.toField from by
                    unfold toField; rw [cond_f51_eq_neg s_prime1_post hc]]
              rw [h_sp1_sq]
              have h_sp_F : s_prime.toField = __discr.2.toField * s.toField := by
                unfold toField; have h := lift_mod_eq _ _ s_prime_post_1
                push_cast at h; exact h
              rw [h_sp_F, mul_pow]
              have hN0 : Field51_as_Nat N_s % p ≠ 0 := by
                intro h0; exact absurd (__discr_post_3 h0).1 h_sq_flag
              have hD_mod : Field51_as_Nat D % p ≠ 0 := by
                intro hD0; apply hs
                have h_dz := (__discr_post_4 ⟨hN0, hD0⟩).2
                have h_spz : Field51_as_Nat s_prime % p = 0 := by
                  have : Field51_as_Nat s_prime % p =
                      (Field51_as_Nat __discr.2 * Field51_as_Nat s) % p := s_prime_post_1
                  rw [Nat.mul_mod, h_dz, zero_mul, Nat.zero_mod] at this; exact this
                have h_snz : Field51_as_Nat s_prime_neg % p = 0 := by
                  have := s_prime_neg_post_1
                  rwa [Nat.add_mod, h_spz, zero_add, Nat.mod_mod] at this
                have h_s1z : Field51_as_Nat s_prime1 % p = 0 := by
                  by_cases hc : s_prime_is_pos.val = 1#u8
                  · rw [cond_f51_eq s_prime1_post hc]; exact h_snz
                  · rw [cond_f51_eq_neg s_prime1_post hc]; exact h_spz
                exact toField_of_mod_zero (by rw [cond_f51_eq s1_post h_nsq]; exact h_s1z)
              have hNSq : ¬∃ x, x ^ 2 * (Field51_as_Nat D % p) % p =
                  Field51_as_Nat N_s % p := by
                intro hSq; exact absurd (__discr_post_5 ⟨hN0, hD_mod, hSq⟩).1 h_sq_flag
              have h6 := (__discr_post_6 ⟨hN0, hD_mod, hNSq⟩).2
              have h_disc_D : __discr.2.toField ^ 2 * D.toField =
                  backend.serial.u64.constants.SQRT_M1.toField * N_s.toField := by
                unfold toField
                have lhs_me := ((Nat.mod_modEq (Field51_as_Nat __discr.2) p).symm.pow 2).mul
                  (Nat.mod_modEq (Field51_as_Nat D) p).symm
                have rhs_me := (Nat.mod_modEq
                  (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) p).symm.mul
                  (Nat.mod_modEq (Field51_as_Nat N_s) p).symm
                have hme := lhs_me.trans (h6.trans rhs_me.symm)
                have h := lift_mod_eq _ _ hme; push_cast at h; exact h
              have h_r_F : r.toField =
                  backend.serial.u64.constants.SQRT_M1.toField * s.toField ^ 2 := by
                unfold toField
                have hme := r_post_1.trans (Nat.ModEq.mul_left
                  (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) r_0_sq_post_1)
                have h := lift_mod_eq _ _ hme; push_cast at h; exact h
              linear_combination s.toField ^ 2 * h_disc_D - N_s.toField * h_r_F
            · unfold toField; rw [cond_f51_eq c1_post h_nsq]
        -- Case split on square/non-square
        rcases h_disj' with ⟨hA, h_c1⟩ | ⟨hB, h_c1⟩
        · -- Case A: s1²D = N_s, c1 = -1
          have h_nt_A : N_t.toField =
              -(r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
            rw [h_Nt_eq_F, h_c1]; ring
          have step1 : (Ed25519.d + 1) * N_t.toField ^ 2 =
              (D.toField + N_s.toField) ^ 2 +
              Ed25519.d * (D.toField - N_s.toField) ^ 2 := by
            rw [h_nt_A, h_D_eq_F, h_ns_eq_F]; ring
          rw [step1]; exact constr_to_squares hA
        · -- Case B: s1²D = r·N_s, c1 = r
          have h_nt_B : N_t.toField =
              r.toField * (r.toField - 1) * (Ed25519.d - 1) ^ 2 - D.toField := by
            rw [h_Nt_eq_F, h_c1];
          have step1 : (Ed25519.d + 1) * N_t.toField ^ 2 =
              (D.toField + r.toField * N_s.toField) ^ 2 +
              Ed25519.d * (D.toField - r.toField * N_s.toField) ^ 2 := by
            rw [h_nt_B, h_D_eq_F, h_ns_eq_F]; ring
          rw [step1]; exact constr_to_squares_r hB
    -- Step 4: Assemble EdwardsPoint.IsValid
    have h_ep_valid : edwards.EdwardsPoint.IsValid ep := {
      X_bounds := fun i hi => by have := ep_post_5 i hi; omega
      Y_bounds := fun i hi => by have := ep_post_6 i hi; omega
      Z_bounds := fun i hi => by have := ep_post_7 i hi; omega
      T_bounds := fun i hi => by have := ep_post_8 i hi; omega
      Z_ne_zero := hZ_ne
      T_relation := by rw [hX_F, hY_F, hT_F, hZ_F]; ring
      on_curve := by
        simp only [hX_F, hY_F, hZ_F]
        linear_combination (cp_Z.toField ^ 2 * cp_T.toField ^ 2) * h_cp_curve
    }
    constructor
    · -- RistrettoPoint.IsValid ep = EdwardsPoint.IsValid ∧ IsSquare (Z² - Y²)
      refine ⟨h_ep_valid, ?_⟩
      simp only [hZ_F, hY_F]
      -- Goal: IsSquare ((cpZ*cpT)² - (cpY*cpZ)²)
      -- Factor: cpZ² · (cpT² - cpY²) with cpT = 1+s², cpY = 1-s²
      --   ⟹ cpZ² · 4 · s1² = (2 · cpZ · s1)²
      have h_s_sq_F : s_sq.toField = s1.toField ^ 2 := by
        unfold toField
        have h := lift_mod_eq _ _ s_sq_post_1
        push_cast at h; exact h
      have h_cp_Y_F : cp_Y.toField + s_sq.toField = ONE.toField := by
        unfold toField
        have h := lift_mod_eq _ _ cp_Y_post_2
        push_cast at h; exact h
      have h_cp_T_F : cp_T.toField = ONE.toField + s_sq.toField := by
        unfold toField
        have h_nat : Field51_as_Nat cp_T = Field51_as_Nat ONE + Field51_as_Nat s_sq := by
          unfold Field51_as_Nat
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi; rw [cp_T_post_1 i hi, mul_add]
        rw [h_nat]; push_cast; ring
      have h_ONE_F : ONE.toField = (1 : CurveField) := by
        unfold toField; rw [ONE_spec]; simp only [Nat.cast_one]
      exact ⟨2 * cp_Z.toField * s1.toField, by
        have h_Y : cp_Y.toField = ONE.toField - s_sq.toField := by
          linear_combination h_cp_Y_F
        rw [h_cp_T_F, h_Y, h_s_sq_F, h_ONE_F]; ring⟩
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
            intro i hi; rw [Finset.mem_range] at hi; rw [s_plus_s_post_1 i hi, mul_add]
          rw [h_nat]; push_cast; ring
        have h_mul : cp_X.toField = s_plus_s.toField * D.toField := by
          unfold toField; have h := lift_mod_eq _ _ cp_X_post_1; push_cast at h; exact h
        rw [h_mul, h_sps];
      have h_cp_Y_F : cp_Y.toField = 1 - s1.toField ^ 2 := by
        unfold toField
        have h_sub := lift_mod_eq _ _ cp_Y_post_2
        have hsq := lift_mod_eq _ _ s_sq_post_1
        push_cast at h_sub hsq; rw [ONE_spec, Nat.cast_one] at h_sub
        linear_combination h_sub - hsq
      have h_cp_Z_F : cp_Z.toField = N_t.toField *
          backend.serial.u64.constants.SQRT_AD_MINUS_ONE.toField := by
        unfold toField; have h := lift_mod_eq _ _ cp_Z_post_1; push_cast at h; exact h
      ext
      · -- x coordinate
        rw [h_impl_x, hX_F, hZ_F]
        rw [(IsUnit.mk0 _ h_cp_T_ne).mul_div_mul_right cp_X.toField cp_Z.toField]
        -- Goal: cp_X / cp_Z = pure_x
        rw [h_cp_X_F, h_cp_Z_F]
        sorry
      · -- y coordinate
        rw [h_impl_y, hY_F, hZ_F]
        rw [show cp_Z.toField * cp_T.toField = cp_T.toField * cp_Z.toField from mul_comm _ _]
        rw [(IsUnit.mk0 _ h_cp_Z_ne).mul_div_mul_right cp_Y.toField cp_T.toField]
        -- Goal: cp_Y / cp_T = pure_y
        rw [h_cp_Y_F, h_cp_T_F]
        sorry




end curve25519_dalek.ristretto.RistrettoPoint
