/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Markus Dablander
-/
import Curve25519Dalek.Math.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.LinearCombination

/-!
# Pure Mathematical Foundations for Edwards Curves

This file defines the pure mathematical foundations for Twisted Edwards curves,
independent of any implementation-specific types.

## Contents

1. **Field Definitions**: `CurveField` as `ZMod p` where p = 2^255 - 19
2. **Curve Structure**: Generic `EdwardsCurve` and the specific `Ed25519` instance
3. **Point Structure**: Affine points satisfying the Edwards curve equation
4. **Group Operations**: Addition, negation, scalar multiplication forming an abelian group

## Architecture Note

This file has NO dependencies on `Funs.lean` or `Types.lean`, making it purely mathematical.
Bridge functions that connect to Rust implementation types are in `Edwards/Representation.lean`.

## References

* Bernstein, Birkner, Joye, Lange, Peters: "Twisted Edwards Curves" (2008)
  https://eprint.iacr.org/2008/013.pdf
-/

namespace Edwards

open ZMod

/-! ## Mathematical Foundations: Twisted Edwards Curves -/

instance : NeZero (2 : CurveField) := ⟨by decide⟩

/-- A Twisted Edwards curve structure defined by parameters a and d. -/
structure EdwardsCurve (F : Type) where
  a : F
  d : F

/-- The specific Ed25519 curve parameters lifted to the field. -/
def Ed25519 : EdwardsCurve CurveField := {
  a := -1,
  d := (d : CurveField)
}

/-- Ed25519 curve parameter d is not a square in the field. -/
lemma d_not_square : ¬IsSquare Ed25519.d := by
  apply (legendreSym.eq_neg_one_iff' p).mp
  norm_num [d, p]

/-- An affine point on the Edwards curve. -/
@[ext]
structure Point {F : Type} [Mul F] [Add F] [Pow F ℕ] [One F] (C : EdwardsCurve F) where
  x : F
  y : F
  on_curve : C.a * x^2 + y^2 = 1 + C.d * x^2 * y^2 := by grind
  deriving Repr

instance : DecidableEq (Point Ed25519) := fun p1 p2 =>
  if hx : p1.x = p2.x then
    if hy : p1.y = p2.y then isTrue (Point.ext hx hy)
    else isFalse (fun h => hy (congrArg Point.y h))
  else isFalse (fun h => hx (congrArg Point.x h))

instance : Inhabited (Point Ed25519) := ⟨{ x := 0, y := 1}⟩

/-- -1 is a square in F_p since p ≡ 1 (mod 4). -/
lemma neg_one_is_square : IsSquare (-1 : CurveField) := by
  apply ZMod.exists_sq_eq_neg_one_iff.mpr; decide

/-! ## Completeness of Twisted Edwards Curves -/

variable {F : Type} [Field F]

section Completeness
variable [NeZero (2 : F)]

/-- **Completeness of Twisted Edwards Addition**

For a twisted Edwards curve E_{a,d} over a field k with char(k) ≠ 2,
if a is a square and d is not a square in k, then
for all points (x₁, y₁), (x₂, y₂) on E_{a,d}: 1 + d·x₁x₂y₁y₂ ≠ 0 and 1 - d·x₁x₂y₁y₂ ≠ 0.
This makes the addition law "complete" (no exceptional cases).

Proof is adapted from https://eprint.iacr.org/2007/286 Theorem 3.3 and
https://eprint.iacr.org/2008/013 Section 6. We write it here for completeness

Recall the twisted curve equation: ax² + y² = 1 + dx²y².
We will show that if λ := dx₁y₁x₂y₂ ∈ {-1, 1}, we get a
contradiction

Lemma 1: dx₁²y₁²(ax₂² + y₂²) = ax₁² + y₁²

  Proof:
    dx₁²y₁²(ax₂² + y₂²)
    = dx₁²y₁² + d²x₁²y₁²x₂²y₂² curve eq
    = dx₁²y₁² + λ²             λ def
    = dx₁²y₁² + 1              simp
    = ax₁² + y₁²               by curve eq

Lemma 2: Let a' = sqrt(a) then
    (a'x₁ + λy₁)² = dx₁²y₁²(a'x₂ + y₂)²

  Proof:
    (a'x₁ + λy₁)²
    = ax₁² + λ²y₁² + 2a'λx₁y₁        expan
    = ax₁² + y₁² + 2a'λx₁y₁          simp
    = dx₁²y₁²(ax₂² + y₂²) + 2a'λx₁y₁ lemma 1
    = dx₁²y₁²(ax₂² + y₂²)
      + 2a'dx₁y₁x₂y₂x₁y₁             λ def
    = dx₁²y₁²(a'x₂ + y₂)²            simp

Lemma 3: Let a' = sqrt(a) then
    (a'x₁ - λy₁)² = dx₁²y₁²(a'x₂ - y₂)²
  Proof:
    Proof is identical to Lemma 2

To finish up, consider three cases:
  1. Suppose a'x₂ + y₂ ≠ 0. Since x₁,y₁ ≠ 0 by hypo, we can
     manipulate lemma 2 to get
       d = ((x₁ + λy₁)/x₁y₁(a'x₂ + y₂))²
     and therefore d is a square. Contradiction.
  2. Suppose a'x₂ - y₂ ≠ 0. We can similarly manipulate
     lemma 3 to get
       d = ((x₁ - λy₁)/x₁y₁(a'x₂ - y₂))²
     and therefore d is a square. Contradiction.
  3. Suppose a'x₂ + y₂ = a'x₂ - y₂ = 0. Since a' ≠ 0, we get
     that x₂ = 0. Contradiction.
-/
theorem complete_addition_denominators_ne_zero
    (C : EdwardsCurve F) (ha : IsSquare C.a) (hd : ¬IsSquare C.d) (p1 p2 : Point C) :
    let lamVal := C.d * p1.x * p2.x * p1.y * p2.y
    (1 + lamVal ≠ 0) ∧ (1 - lamVal ≠ 0) := by
  constructor
  intro h
  set lamVal := C.d * p1.x * p2.x * p1.y * p2.y with hlam
  have lemLam : lamVal ^ 2 = 1 := by
    grind
  have lem1 : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) = C.a * p1.x^2 + p1.y^2 := by
    rw [p2.on_curve]
    rw [mul_add]
    simp
    suffices h: C.d * p1.x ^ 2 * p1.y ^ 2 + C.d ^ 2 * p1.x ^ 2 * p1.y ^ 2 * p2.x ^ 2 * p2.y ^ 2 = C.a * p1.x ^ 2 + p1.y ^ 2 by
      grind
    suffices lem3 : C.d * p1.x ^ 2 * p1.y ^ 2 + (C.d * p1.x * p2.x * p1.y * p2.y)^2 = C.a * p1.x ^ 2 + p1.y ^ 2 by
      grind
    rw [<- hlam, lemLam]
    rw [add_comm, p1.on_curve]
  /-  dx₁²y₁²(sqrt(a)*x₂² + y₂²) = (x₁ + εy₁)² -/
  obtain ⟨a', ha'⟩ := ha
  have lem2 : (a' * p1.x + lamVal * p1.y) ^ 2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 := by
    suffices h : a' * a' * p1.x^2 + lamVal^2 * p1.y^2 + 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      linear_combination h
    suffices h : C.a * p1.x^2 + p1.y^2 + 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [lemLam, <- ha']
      simp [h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) + 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [<- lem1, h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) + 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [hlam]
      linear_combination h
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * a' * p2.x^2 + p2.y^2) + 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [ha', h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * p2.x + p2.y)^2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      linear_combination h
    eq_refl
  have lem3 : (a' * p1.x - lamVal * p1.y) ^ 2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 := by
    suffices h : a' * a' * p1.x^2 + lamVal^2 * p1.y^2 - 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      linear_combination h
    suffices h : C.a * p1.x^2 + p1.y^2 - 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [lemLam, <- ha']
      simp [h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) - 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [<- lem1, h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) - 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [hlam]
      linear_combination h
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * a' * p2.x^2 + p2.y^2) - 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [ha', h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * p2.x - p2.y)^2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      linear_combination h
    eq_refl
  have hp1x: p1.x ≠ 0 := by grind
  have hp1y: p1.y ≠ 0 := by grind
  have hp2x: p2.x ≠ 0 := by grind
  have hp2y: p2.y ≠ 0 := by grind
  by_cases hcasePos : a' * p2.x + p2.y = 0
  by_cases hcaseNeg : a' * p2.x - p2.y = 0
  /- Handle the case that a' x1 + λy1 = a' x1 - λy1 = 0 -/
  have hy: p2.y = a' * p2.x := by linear_combination -hcaseNeg
  have hy': p2.y = - a' * p2.x := by linear_combination hcasePos
  have hx0: 2 * a' * p2.x = 0 := by linear_combination (hcasePos + hcaseNeg)
  have han0: a' ≠ 0 := by grind
  have xz: p2.x = 0 := by
    exact (mul_eq_zero.mp hx0).resolve_left (mul_ne_zero two_ne_zero han0)
  exact hp2x xz
  /- Handle the case that a' x1 - λy1 != 0 -/
  have hdenom: (p1.x * p1.y * (a' * p2.x - p2.y))^2 ≠ 0 := by
    have hdenom' : p1.x * p1.y * (a' * p2.x - p2.y) ≠ 0 := by
      grind
    exact pow_ne_zero _ hdenom'
  have hfrac: C.d = (a' * p1.x - lamVal * p1.y) ^ 2 / (p1.x * p1.y * (a' * p2.x - p2.y))^2 := by
    rw [eq_div_iff]
    linear_combination -lem2
    exact hdenom
  have hfrac2: C.d = ((a' * p1.x - lamVal * p1.y)  / (p1.x * p1.y * (a' * p2.x - p2.y)))^2 := by
    rw [div_pow]
    exact hfrac
  have hisq: IsSquare C.d := by
    use (a' * p1.x - lamVal * p1.y) / (p1.x * p1.y * (a' * p2.x - p2.y))
    rw [<- sq]
    exact hfrac2
  exact hd hisq
  /- Now repeat for the case that a' x1 + λy1 != 0 -/
  have hdenom: (p1.x * p1.y * (a' * p2.x + p2.y))^2 ≠ 0 := by
    have hdenom' : p1.x * p1.y * (a' * p2.x + p2.y) ≠ 0 := by
      grind
    exact pow_ne_zero _ hdenom'
  have hfrac: C.d = (a' * p1.x + lamVal * p1.y) ^ 2 / (p1.x * p1.y * (a' * p2.x + p2.y))^2 := by
    rw [eq_div_iff]
    linear_combination -lem2
    exact hdenom
  have hfrac2: C.d = ((a' * p1.x + lamVal * p1.y)  / (p1.x * p1.y * (a' * p2.x + p2.y)))^2 := by
    rw [div_pow]
    exact hfrac
  have hisq: IsSquare C.d := by
    use (a' * p1.x + lamVal * p1.y) / (p1.x * p1.y * (a' * p2.x + p2.y))
    rw [<- sq]
    exact hfrac2
  exact hd hisq

  /- Repeat the entire thing again for the right case -/

  intro h
  set lamVal := C.d * p1.x * p2.x * p1.y * p2.y with hlam
  have lemLam : lamVal ^ 2 = 1 := by
    grind
  have lem1 : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) = C.a * p1.x^2 + p1.y^2 := by
    rw [p2.on_curve]
    rw [mul_add]
    simp
    suffices h: C.d * p1.x ^ 2 * p1.y ^ 2 + C.d ^ 2 * p1.x ^ 2 * p1.y ^ 2 * p2.x ^ 2 * p2.y ^ 2 = C.a * p1.x ^ 2 + p1.y ^ 2 by
      grind
    suffices lem3 : C.d * p1.x ^ 2 * p1.y ^ 2 + (C.d * p1.x * p2.x * p1.y * p2.y)^2 = C.a * p1.x ^ 2 + p1.y ^ 2 by
      grind
    rw [<- hlam, lemLam]
    rw [add_comm, p1.on_curve]
  /-  dx₁²y₁²(sqrt(a)*x₂² + y₂²) = (x₁ + εy₁)² -/
  obtain ⟨a', ha'⟩ := ha
  have lem2 : (a' * p1.x + lamVal * p1.y) ^ 2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 := by
    suffices h : a' * a' * p1.x^2 + lamVal^2 * p1.y^2 + 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      linear_combination h
    suffices h : C.a * p1.x^2 + p1.y^2 + 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [lemLam, <- ha']
      simp [h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) + 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [<- lem1, h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) + 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [hlam]
      linear_combination h
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * a' * p2.x^2 + p2.y^2) + 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      rw [ha', h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * p2.x + p2.y)^2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x + p2.y )^2 by
      linear_combination h
    eq_refl
  have lem3 : (a' * p1.x - lamVal * p1.y) ^ 2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 := by
    suffices h : a' * a' * p1.x^2 + lamVal^2 * p1.y^2 - 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      linear_combination h
    suffices h : C.a * p1.x^2 + p1.y^2 - 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [lemLam, <- ha']
      simp [h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) - 2*a'*p1.x*lamVal*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [<- lem1, h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (C.a * p2.x^2 + p2.y^2) - 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [hlam]
      linear_combination h
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * a' * p2.x^2 + p2.y^2) - 2*a'*p1.x*C.d * p1.x * p2.x * p1.y * p2.y*p1.y = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      rw [ha', h]
    suffices h : C.d * p1.x^2 * p1.y^2 * (a' * p2.x - p2.y)^2 = C.d * p1.x ^ 2 * p1.y ^ 2 * (a' * p2.x - p2.y )^2 by
      linear_combination h
    eq_refl
  have hp1x: p1.x ≠ 0 := by grind
  have hp1y: p1.y ≠ 0 := by grind
  have hp2x: p2.x ≠ 0 := by grind
  have hp2y: p2.y ≠ 0 := by grind
  by_cases hcasePos : a' * p2.x + p2.y = 0
  by_cases hcaseNeg : a' * p2.x - p2.y = 0
  /- Handle the case that a' x1 + λy1 = a' x1 - λy1 = 0 -/
  have hy: p2.y = a' * p2.x := by linear_combination -hcaseNeg
  have hy': p2.y = - a' * p2.x := by linear_combination hcasePos
  have hx0: 2 * a' * p2.x = 0 := by linear_combination (hcasePos + hcaseNeg)
  have han0: a' ≠ 0 := by grind
  have xz: p2.x = 0 := by
    exact (mul_eq_zero.mp hx0).resolve_left (mul_ne_zero two_ne_zero han0)
  exact hp2x xz
  /- Handle the case that a' x1 - λy1 != 0 -/
  have hdenom: (p1.x * p1.y * (a' * p2.x - p2.y))^2 ≠ 0 := by
    have hdenom' : p1.x * p1.y * (a' * p2.x - p2.y) ≠ 0 := by
      grind
    exact pow_ne_zero _ hdenom'
  have hfrac: C.d = (a' * p1.x - lamVal * p1.y) ^ 2 / (p1.x * p1.y * (a' * p2.x - p2.y))^2 := by
    rw [eq_div_iff]
    linear_combination -lem2
    exact hdenom
  have hfrac2: C.d = ((a' * p1.x - lamVal * p1.y)  / (p1.x * p1.y * (a' * p2.x - p2.y)))^2 := by
    rw [div_pow]
    exact hfrac
  have hisq: IsSquare C.d := by
    use (a' * p1.x - lamVal * p1.y) / (p1.x * p1.y * (a' * p2.x - p2.y))
    rw [<- sq]
    exact hfrac2
  exact hd hisq
  /- Now repeat for the case that a' x1 + λy1 != 0 -/
  have hdenom: (p1.x * p1.y * (a' * p2.x + p2.y))^2 ≠ 0 := by
    have hdenom' : p1.x * p1.y * (a' * p2.x + p2.y) ≠ 0 := by
      grind
    exact pow_ne_zero _ hdenom'
  have hfrac: C.d = (a' * p1.x + lamVal * p1.y) ^ 2 / (p1.x * p1.y * (a' * p2.x + p2.y))^2 := by
    rw [eq_div_iff]
    linear_combination -lem2
    exact hdenom
  have hfrac2: C.d = ((a' * p1.x + lamVal * p1.y)  / (p1.x * p1.y * (a' * p2.x + p2.y)))^2 := by
    rw [div_pow]
    exact hfrac
  have hisq: IsSquare C.d := by
    use (a' * p1.x + lamVal * p1.y) / (p1.x * p1.y * (a' * p2.x + p2.y))
    rw [<- sq]
    exact hfrac2
  exact hd hisq

/-- For Ed25519, the addition formula denominators are never zero.
    This follows from the completeness theorem since a = -1 is a square (p ≡ 1 mod 4)
    and d is not a square in F_p. -/
theorem Ed25519.denomsNeZero (p1 p2 : Point Ed25519) :
    let lamVal := Ed25519.d * p1.x * p2.x * p1.y * p2.y
    (1 + lamVal ≠ 0) ∧ (1 - lamVal ≠ 0) :=
  complete_addition_denominators_ne_zero Ed25519 neg_one_is_square d_not_square p1 p2

/-! ## Addition Formulas -/

/-- Implements the unified addition formulas for Twisted Edwards curves. -/
def add_coords (C : EdwardsCurve F) (p1 p2 : F × F) : F × F :=
  let (x₁, y₁) := p1
  let (x₂, y₂) := p2
  let lambda_val := C.d * x₁ * x₂ * y₁ * y₂
  ( (x₁ * y₂ + y₁ * x₂) / (1 + lambda_val), (y₁ * y₂ - C.a * x₁ * x₂) / (1 - lambda_val) )

omit [NeZero (2 : F)] in
/-- **Closure of Twisted Edwards Addition**
The sum of two points on a twisted Edwards curve stays on the curve, provided the denominators in
the addition formula are non-zero. -/
theorem add_closure (C : EdwardsCurve F) (p1 p2 : Point C)
    (h : let lamVal := C.d * p1.x * p2.x * p1.y * p2.y; (1 + lamVal ≠ 0) ∧ (1 - lamVal ≠ 0)) :
    let (x, y) := add_coords C (p1.x, p1.y) (p2.x, p2.y)
    C.a * x^2 + y^2 = 1 + C.d * x^2 * y^2 := by
  set x₁ := p1.x; set y₁ := p1.y
  set x₂ := p2.x; set y₂ := p2.y
  suffices C.a * (x₁ * y₂ + y₁ * x₂)^2 * (1 - x₁ * y₂ * y₁ * x₂ * C.d)^2 +
      (1 + x₁ * y₂ * y₁ * x₂ * C.d)^2 * (y₂ * y₁ - C.a * x₁ * x₂)^2 =
      (1 + x₁ * y₂ * y₁ * x₂ * C.d)^2 * (1 - x₁ * y₂ * y₁ * x₂ * C.d)^2 +
      (x₁ * y₂ + y₁ * x₂)^2 * C.d * (y₂ * y₁ - C.a * x₁ * x₂)^2 by
    have : 1 + x₁ * y₂ * y₁ * x₂ * C.d ≠ 0 := by grind
    have : 1 - x₁ * y₂ * y₁ * x₂ * C.d ≠ 0 := by grind
    unfold add_coords
    field_simp
    assumption
  rw [← sub_eq_zero]
  /- We define polynomials A, B, P, Q such that the LHS of the goal can be written as a linear
  combination of the form P*A + Q*B. A and B are chosen such that p1 and p2 lying on the curve
  implies that A = B = 0 and thus LHS = 0. -/
  let A := C.a * x₁^2 + y₁^2 - (1 + C.d * x₁^2 * y₁^2)
  let B := C.a * x₂^2 + y₂^2 - (1 + C.d * x₂^2 * y₂^2)
  have hA : A = 0 := by linear_combination p1.on_curve
  have hB : B = 0 := by linear_combination p2.on_curve
  let P := (C.a * x₂^2 + y₂^2) + (-C.d * x₂^2 * y₂^2) + (-C.d * x₂^2 * y₁^2 * y₂^2) +
    (-C.a * x₁^2 * x₂^2 * y₂^2 * C.d) + (x₁^2 * y₁^2 * x₂^2 * y₂^4 * C.d^2) +
    (-x₁^2 * y₁^2 * x₂^2 * y₂^2 * C.d^2) + (C.a * x₁^2 * x₂^4 * y₁^2 * y₂^2 * C.d^2)
  let Q := 1 + (-x₁^2 * y₁^2 * y₂^2 * C.d) + (-C.a * x₁^2 * x₂^2 * y₁^2 * C.d) +
    (x₁^4 * x₂^2 * y₁^4 * y₂^2 * C.d^3)
  calc _ = P * A + Q * B := by grind
    _ = P * 0 + Q * 0 := by rw [hA, hB]
    _ = 0 := by ring

end Completeness

/-- The sum of two points on Ed25519 stays on the curve.
    For Ed25519, d is not a square, so the denominators are never zero (complete curve). -/
theorem add_closure_Ed25519 (p1 p2 : Point Ed25519) :
    let (x, y) := add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)
    Ed25519.a * x^2 + y^2 = 1 + Ed25519.d * x^2 * y^2 :=
  add_closure Ed25519 p1 p2 (Ed25519.denomsNeZero p1 p2)

/-! ## Group Structure for Ed25519 -/

instance : Add (Point Ed25519) where
  add p1 p2 :=
  let coords := add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)
  { x := coords.1
    y := coords.2
    on_curve := add_closure_Ed25519 p1 p2 }

instance : Zero (Point Ed25519) where
  zero := { x := 0, y := 1 }

@[simp] theorem zero_x : (0 : Point Ed25519).x = 0 := rfl
@[simp] theorem zero_y : (0 : Point Ed25519).y = 1 := rfl

instance : Neg (Point Ed25519) where
  neg p := {
    x := -p.x
    y := p.y
    on_curve := by simpa [neg_pow_two] using p.on_curve
  }

@[simp] theorem neg_x (p : Point Ed25519) : (-p).x = -p.x := rfl
@[simp] theorem neg_y (p : Point Ed25519) : (-p).y = p.y := rfl

instance : Sub (Point Ed25519) where
  sub p1 p2 := p1 + (-p2)

def nsmul_Ed25519 (n : ℕ) (p : Point Ed25519) : Point Ed25519 :=
  match n with
  | 0 => 0
  | n + 1 => p + (nsmul_Ed25519 n p)

/-- Binary scalar multiplication, O(log n) point operations.
    Equivalent to `nsmul_Ed25519` but computationally feasible for large scalars like L ~ 2^252. -/
def binary_nsmul_Ed25519 (n : ℕ) (p : Point Ed25519) : Point Ed25519 :=
  if n = 0 then 0
  else
    let half := binary_nsmul_Ed25519 (n / 2) p
    let doubled := half + half
    if n % 2 = 1 then doubled + p else doubled
decreasing_by omega

def zsmul_Ed25519 (z : ℤ) (p : Point Ed25519) : Point Ed25519 :=
  match z with
  | (n : ℕ) => nsmul_Ed25519 n p
  | (Int.negSucc n) => -(nsmul_Ed25519 (n + 1) p)

instance : SMul ℕ (Point Ed25519) := ⟨nsmul_Ed25519⟩
instance : SMul ℤ (Point Ed25519) := ⟨zsmul_Ed25519⟩

/-! ### Group Law Lemmas -/

/-- Simplification lemma for add_coords with explicit pairs. -/
theorem add_coords_mk (C : EdwardsCurve F) (x₁ y₁ x₂ y₂ : F) :
    let lamVal := C.d * x₁ * x₂ * y₁ * y₂;
    add_coords C (x₁, y₁) (x₂, y₂) =
      ((x₁ * y₂ + y₁ * x₂) / (1 + lamVal), (y₁ * y₂ - C.a * x₁ * x₂) / (1 - lamVal)) := rfl

/-- The x-coordinate of p + q on Ed25519. Used for unfolding in specific proofs. -/
theorem add_x (p q : Point Ed25519) :
    (p + q).x = (p.x * q.y + p.y * q.x) / (1 + Ed25519.d * p.x * q.x * p.y * q.y) := rfl

/-- The y-coordinate of p + q on Ed25519. Used for unfolding in specific proofs. -/
theorem add_y (p q : Point Ed25519) :
    (p + q).y = (p.y * q.y - Ed25519.a * p.x * q.x) / (1 - Ed25519.d * p.x * q.x * p.y * q.y) := rfl

/-- The identity element (0, 1) is a left identity for addition. -/
theorem zero_add_Ed25519 (p : Point Ed25519) : (0 : Point Ed25519) + p = p := by
  ext
  · rw [add_x]; simp only [Ed25519, zero_x, zero_mul, zero_y, one_mul, zero_add, mul_zero, mul_one,
    add_zero, div_one]
  · rw [add_y]; simp only [Ed25519, zero_y, one_mul, zero_x, mul_zero, zero_mul, sub_zero, mul_one,
    div_one]

/-- The identity element (0, 1) is a right identity for addition. -/
theorem add_zero_Ed25519 (p : Point Ed25519) : p + (0 : Point Ed25519) = p := by
  ext
  · rw [add_x]; simp only [Ed25519, zero_y, mul_one, zero_x, mul_zero, add_zero, zero_mul, div_one]
  · rw [add_y]; simp only [Ed25519, zero_y, mul_one, neg_mul, one_mul, zero_x, mul_zero, sub_zero,
    zero_mul, div_one]

/-- Negation is a left inverse: -p + p = 0. -/
theorem neg_add_cancel_Ed25519 (p : Point Ed25519) : -p + p = (0 : Point Ed25519) := by
  have h : p.y^2 - p.x^2 = 1 + (d : CurveField) * p.x^2 * p.y^2 := by
    have := p.on_curve; simp only [Ed25519, neg_mul, one_mul] at this; linear_combination this
  have : 1 + (d : CurveField) * p.x^2 * p.y^2 ≠ 0 := calc
    1 + d * p.x^2 * p.y^2 = 1 - d * (-p.x) * p.x * p.y * p.y := by ring
    _ ≠ 0 := (Ed25519.denomsNeZero (-p) p).2
  ext
  · rw [add_x, neg_x, neg_y]; ring_nf; rfl
  · have := calc (p.y * p.y - -1 * (-p.x) * p.x) / (1 - d * (-p.x) * p.x * p.y * p.y)
      _ = (p.y^2 - p.x^2) / (1 + d * p.x^2 * p.y^2) := by ring_nf
      _ = 1 := by rw [h]; grind
    rw [add_y]; simp only [Ed25519, zero_y]
    omega

/-- Addition is commutative. -/
theorem add_comm_Ed25519 (p q : Point Ed25519) : p + q = q + p := by
  ext <;> simp only [add_x, add_y] <;> ring

/-- nsmul satisfies the successor property (for AddCommGroup). -/
theorem nsmul_succ_Ed25519 (n : ℕ) (p : Point Ed25519) :
    nsmul_Ed25519 (n + 1) p = nsmul_Ed25519 n p + p := by
  rw [add_comm_Ed25519]; rfl

/-- zsmul satisfies the successor property. -/
theorem zsmul_succ_Ed25519 (n : ℕ) (p : Point Ed25519) :
    zsmul_Ed25519 (Int.ofNat n.succ) p = zsmul_Ed25519 (Int.ofNat n) p + p := by
  simp only [zsmul_Ed25519]
  induction n with
  | zero =>
    simp only [nsmul_Ed25519]
    -- Goal: p + 0 = 0 + p
    rw [add_zero_Ed25519, zero_add_Ed25519]
  | succ k _ih =>
    simp only [nsmul_Ed25519]
    rw [add_comm_Ed25519]

/-- Addition on Ed25519 is associative: (p + q) + r = p + (q + r). -/
theorem add_assoc_Ed25519 (p q r : Point Ed25519) : p + q + r = p + (q + r) := by
  /- **Reference**: Hales, Thomas and Raya, Rodrigo.
  "Formal Proof of the Group Law for Edwards Elliptic Curves".
  Automated Reasoning (IJCAR 2020), pp. 254–269.
  https://doi.org/10.1007/978-3-030-51054-1_15 -/
  sorry

/-- The Ed25519 curve points form an additive abelian group. -/
instance : AddCommGroup (Point Ed25519) where
  add := Add.add
  add_assoc := add_assoc_Ed25519
  zero := 0
  zero_add := zero_add_Ed25519
  add_zero := add_zero_Ed25519
  nsmul := nsmul_Ed25519
  neg := Neg.neg
  zsmul := zsmul_Ed25519
  neg_add_cancel := neg_add_cancel_Ed25519
  add_comm := add_comm_Ed25519
  nsmul_succ := nsmul_succ_Ed25519
  zsmul_succ' := zsmul_succ_Ed25519

/-- Helper lemma to expose the addition formula without unfolding the whole structure. -/
theorem add_def (p1 p2 : Point Ed25519) :
    (p1 + p2).x = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).1 ∧
    (p1 + p2).y = (add_coords Ed25519 (p1.x, p1.y) (p2.x, p2.y)).2 := by
  exact Prod.mk_inj.mp rfl

/-- Binary scalar multiplication equals the standard linear scalar multiplication. -/
theorem binary_nsmul_Ed25519_eq (n : ℕ) (q : Point Ed25519) :
    binary_nsmul_Ed25519 n q = n • q := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold binary_nsmul_Ed25519
    split_ifs
    · simp_all
    · have : n / 2 < n := by omega
      conv_rhs => rw [show n = n / 2 + n / 2 + 1 from by omega]
      simp [ih _ this, add_nsmul]
    · have : n / 2 < n := by omega
      conv_rhs => rw [show n = n / 2 + n / 2 from by omega]
      simp [ih _ this, add_nsmul]

end Edwards
