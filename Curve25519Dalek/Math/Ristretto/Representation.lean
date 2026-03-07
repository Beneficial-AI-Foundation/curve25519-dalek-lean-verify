/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Types
import Curve25519Dalek.Funs

/-!
# Ristretto Point Representations

Bridge infrastructure for Ristretto group elements.
Ristretto defines a prime-order group by quotienting Ed25519 by its cofactor-8 subgroup.

## References

- https://ristretto.group/details/isogenies.html
- https://www.shiftleft.org/papers/decaf/decaf.pdf
-/

namespace curve25519_dalek.math

open Edwards ZMod
open Aeneas.Std Result
/-- INVSQRT_A_MINUS_D: Constant used in compression rotation.
    Value: 544693...17578 -/
def invsqrt_a_minus_d : ZMod p :=
  54469307008909316920995813868745141605393597292927456921205312896311721017578

/-- Edwards a constant (-1) cast to the field. -/
def a_val : ZMod p := -1

section PureIsogeny

/-- Algebraic helper for Ed25519 point decompression.
    Proves that the recovered (x, y) satisfy the Edwards curve equation. -/
lemma decompress_helper {F : Type*} [Field F] (a d s I u1 u2 v : F)
    (ha : a = -1)
    (hu1 : u1 = 1 + a * s ^ 2)
    (hu2 : u2 = 1 - a * s ^ 2)
    (hv : v = a * d * u1 ^ 2 - u2 ^ 2)
    (hI : I ^ 2 * (v * u2 ^ 2) = 1) :
    let x := 2 * s * (I * u2)
    let y := u1 * (I * (I * u2) * v)
    a * x^2 + y^2 = 1 + d * x^2 * y^2 := by
  intro x y
  have h_inv : I^2 = (v * u2^2)⁻¹ := eq_inv_of_mul_eq_one_left hI
  dsimp only [x, y]; simp only [pow_two]; ring_nf
  rw [show I^4 = (I^2)^2 by ring, show I^6 = (I^2)^3 by ring, h_inv]
  have h_denom_nz : (v * u2^2) ≠ 0 := right_ne_zero_of_mul_eq_one hI
  field_simp [h_denom_nz]; rw [div_eq_iff h_denom_nz]
  simp only [add_mul, one_mul, div_mul_cancel₀ _ h_denom_nz]
  rw [hv, hu1, hu2, ha];
  try ring

/-! ### Compress Step Functions

Decomposition of `compress_pure` into individual step functions.
This avoids RAM blowup when unfolding the monolithic definition in proofs.
Each step function computes one intermediate value of the Ristretto ENCODE algorithm.
-/

/-- Phase 1: u1 = (1 + y)(1 - y) -/
def compress_u1 (P : Point Ed25519) : ZMod p :=
  (1 + P.y) * (1 - P.y)

/-- Phase 1: u2 = x * y -/
def compress_u2 (P : Point Ed25519) : ZMod p :=
  P.x * P.y

/-- Phase 2: invsqrt = 1/√(u1 · u2²) -/
noncomputable def compress_invsqrt (P : Point Ed25519) : ZMod p :=
  (inv_sqrt_checked (compress_u1 P * (compress_u2 P) ^ 2)).1

/-- Phase 3: den1 = invsqrt · u1 -/
noncomputable def compress_den1 (P : Point Ed25519) : ZMod p :=
  compress_invsqrt P * compress_u1 P

/-- Phase 3: den2 = invsqrt · u2 -/
noncomputable def compress_den2 (P : Point Ed25519) : ZMod p :=
  compress_invsqrt P * compress_u2 P

/-- Phase 3: z_inv = den1 · den2 · (x · y) -/
noncomputable def compress_z_inv (P : Point Ed25519) : ZMod p :=
  compress_den1 P * compress_den2 P * (P.x * P.y)

/-- Phase 4: rotation flag = is_negative(x · y · z_inv) -/
noncomputable def compress_rotate (P : Point Ed25519) : Bool :=
  is_negative (P.x * P.y * compress_z_inv P)

/-- Phase 5: x' = y · √(-1) if rotate, else x -/
noncomputable def compress_x_prime (P : Point Ed25519) : ZMod p :=
  if compress_rotate P then P.y * sqrt_m1 else P.x

/-- Phase 5: y' = x · √(-1) if rotate, else y -/
noncomputable def compress_y_prime (P : Point Ed25519) : ZMod p :=
  if compress_rotate P then P.x * sqrt_m1 else P.y

/-- Phase 5: den_inv = den1 · invsqrt_a_minus_d if rotate, else den2 -/
noncomputable def compress_den_inv (P : Point Ed25519) : ZMod p :=
  if compress_rotate P then compress_den1 P * invsqrt_a_minus_d else compress_den2 P

/-- Phase 6: y_final with sign adjustment -/
noncomputable def compress_y_final (P : Point Ed25519) : ZMod p :=
  if is_negative (compress_x_prime P * compress_z_inv P)
  then -(compress_y_prime P)
  else compress_y_prime P

/-- Phase 7: s = |den_inv · (1 - y_final)| -/
noncomputable def compress_s (P : Point Ed25519) : ZMod p :=
  abs_edwards (compress_den_inv P * (1 - compress_y_final P))

/--
**Pure Mathematical Compression**
Encodes a Point P into a scalar s (https://ristretto.group/formulas/encoding.html).
Used to define the Canonical property.

Defined via step functions (`compress_u1`, `compress_u2`, ..., `compress_s`)
to enable incremental unfolding in proofs.
-/
noncomputable def compress_pure (P : Point Ed25519) : Nat :=
  (compress_s P).val

private lemma p_sub_one_lt : p - 1 < p := by decide

lemma p_sub_one_cast : (↑(p - 1) : ZMod p) = -1 := by
  rw [Nat.cast_sub (by decide : 1 ≤ p), ZMod.natCast_self, zero_sub, Nat.cast_one]

private lemma sqrt_m1_sq_nat :
    19681161376707505956807079304988542015446066515923890162744021073123829784752 ^ 2 % p = p - 1 := by
  decide

/-- √(-1) squared equals -1 in F_p. -/
lemma sqrt_m1_sq : (sqrt_m1 : ZMod p) ^ 2 = -1 := by
  unfold sqrt_m1
  have h := lift_mod_eq _ (p - 1) (by rw [Nat.mod_eq_of_lt p_sub_one_lt])
  push_cast at h; rwa [p_sub_one_cast] at h

private lemma iad_sq_nat :
    54469307008909316920995813868745141605393597292927456921205312896311721017578 ^ 2 *
    (57896044618658097711785492504343953926634992332820282019728792003956564819948 -
     37095705934669439343138083508754565189542113879843219016388785533085940283555) % p = 1 := by
  decide

/-- invsqrt_a_minus_d² · (a - d) = 1. -/
lemma iad_sq : (invsqrt_a_minus_d : ZMod p) ^ 2 * (a_val - (↑d : ZMod p)) = 1 := by
  unfold invsqrt_a_minus_d a_val d
  have h := iad_sq_nat
  unfold p at h
  have : (((54469307008909316920995813868745141605393597292927456921205312896311721017578 : ℕ) ^ 2 *
    (57896044618658097711785492504343953926634992332820282019728792003956564819948 -
     37095705934669439343138083508754565189542113879843219016388785533085940283555) : ℤ) : ZMod p) = 1 := by
    rw [← ZMod.intCast_mod _ p]
    decide
  push_cast at this; exact this

end PureIsogeny

end curve25519_dalek.math

/-! ## RistrettoPoint Validity -/

namespace curve25519_dalek.ristretto
open curve25519_dalek.edwards Edwards
open curve25519_dalek.math

/--
**IsEven Predicate for Edwards Points**

A point $P(x,y)$ on the Edwards curve is "even" if it lies in the image of the doubling map
(i.e., $P \in 2\mathcal{E}$). For Curve25519, this subgroup has index 2.

**Theorem**: An Edwards point $P(x,y)$ is even if and only if $(1 - y^2)$ is a quadratic residue.

**Proof Sketch & Derivation**:
1. **Montgomery Map**: Ed25519 is birationally equivalent to the Montgomery curve
   $M: v^2 = u^3 + Au^2 + u$ via the map $u = \frac{1+y}{1-y}$.

2. **Montgomery Group Structure**: On a Montgomery curve, a point $(u,v)$ is a "double"
   (in $2\mathcal{M}$) if and only if the coordinate $u$ is a square in $\mathbb{F}_p$.
   *(Reference: See 'KEY Theorem' below)*.

3. **Substitution**: Substituting the Edwards map, $P$ is even iff $\frac{1+y}{1-y}$ is a square.

4. **Simplification**:
   Observe that $\frac{1+y}{1-y} = \frac{(1+y)^2}{1-y^2}$.
   Since $(1+y)^2$ is always a square (for any field element), the squareness of the
   fraction depends entirely on the denominator $(1-y^2)$.
   Therefore: $P \in 2\mathcal{E} \iff \text{IsSquare}(1 - y^2)$.

**Edge Cases**:
- **Identity (0, 1)**: $y=1 \implies 1-y^2 = 0$. Since $0 = 0^2$, it is square.
  (Correct: Identity is $2 \cdot \mathcal{O}$).
- **2-Torsion (0, -1)**: $y=-1 \implies 1-y^2 = 0$. Square.
  (Correct: $(0,-1) = 2 \cdot (i, 0)$).
- **Other 2-Torsion $(\pm 1, 0)$**: $y=0 \implies 1-y^2 = 1$. Square.
  (Correct: These are doubles of 4-torsion points).

**KEY Theorem: Characterization of Even Points On Montgomery via Quadratic Residues**

Let $K$ be a field of char $\ne 2$ where $A^2-4$ is not a square (e.g., $K=\mathbb{F}_p$ for Curve25519).
Let $E$ be the Montgomery curve $y^2 = x^3 + Ax^2 + x$.
Then $P \in 2E(K) \iff x(P) \in (K^\times)^2 \cup \{0\}$.

**Proof Details:**

1. **Definitions & Tools:**
   Let $r(R) := y(R)/x(R)$ be a rational function on $E$.
   Let $T = (0,0)$ be the unique non-trivial rational 2-torsion point.

   *Lemma 1 (Translation by T):* For any $R$, $R+T = (1/x(R), -y(R)/x(R)^2)$.
   **Proof:**

    We use the standard chord formula for Weierstrass equations (with $a_1=a_3=0$).

    1. **Slope ($\lambda$):**
      The slope of the line through $R=(x,y)$ and $T=(0,0)$ is:
      $$ \lambda = \frac{y-0}{x-0} = \frac{y}{x} $$

    2. **x-coordinate:**
      The formula for the new x-coordinate is $x(R+T) = \lambda^2 - A - x - 0$.
      $$ x(R+T) = \frac{y^2}{x^2} - A - x $$
      Using the curve equation $y^2 = x^3 + Ax^2 + x$, we expand the term $y^2/x^2$:
      $$ \frac{y^2}{x^2} = \frac{x^3+Ax^2+x}{x^2} = x + A + \frac{1}{x} $$
      Substituting this back:
      $$ x(R+T) = \left(x + A + \frac{1}{x}\right) - A - x = \frac{1}{x} $$

    3. **y-coordinate:**
      The formula is $y(R+T) = -y + \lambda(x - x(R+T))$.
      $$ y(R+T) = -y + \frac{y}{x}\left(x - \frac{1}{x}\right) $$
      $$ y(R+T) = -y + y\left(1 - \frac{1}{x^2}\right) $$
      $$ y(R+T) = -y + y - \frac{y}{x^2} = -\frac{y}{x^2} $$

                                                                        QED

   *Lemma 2 (Sign Flip):* It follows that $r(R+T) = -r(R)$.
   *Lemma 3 (Doubling):* The Montgomery doubling formula for $P=2Q$ can be rewritten as:
   $$x(P) = \frac{(x(Q) - 1/x(Q))^2}{4 \cdot r(Q)^2}$$
    **Proof:**
      The standard Montgomery doubling formula (for $B=1$) is:
      $$ x(2Q) = \frac{(x^2 - 1)^2}{4x(x^2 + Ax + 1)} $$

      Divide numerator and denominator by $x^2$:
      $$ x(2Q) = \frac{(x - \frac{1}{x})^2}{4(x + A + \frac{1}{x})} $$

      Recall the definition of $r(Q) = y/x$. Squaring it gives:
      $$ r(Q)^2 = \frac{y^2}{x^2} $$
      Using the curve equation $y^2 = x^3 + Ax^2 + x$, we substitute $y^2$:
      $$ r(Q)^2 = \frac{x^3 + Ax^2 + x}{x^2} = x + A + \frac{1}{x} $$

      Substituting $r(Q)^2$ into the denominator of the doubling formula yields:
      $$ x(2Q) = \frac{(x - \frac{1}{x})^2}{4 r(Q)^2} $$. QED

2. **Forward Implication ($\Rightarrow$):**
   If $P=2Q$ for $Q \in E(K)$, the doubling formula shows $x(P)$ is a ratio of squares in $K$.
   Thus $x(P)$ is a square.

3. **Reverse Implication ($\Leftarrow$):**
   Assume $x(P) = u^2 \in K$. Let $Q \in E(\bar K)$ be a point such that $2Q = P$.
   We must show $Q \in E(K)$ (i.e., $Q$ is rational).

   **Proof:**

    1.  **Setup:**
      Assume $x(P) = u \in K$ is a square (allowing $u=0$).
      Pick some $Q \in E(\bar K)$ with $2Q = P$ (exists because $[2]$ is surjective on the algebraic closure).
      Let $x = x(Q)$ and define $\alpha := r(Q) = y/x \in \bar K$.
      By Lemma 3, we have the equation:
      $$ (\star) \quad u = x(P) = \frac{(x - 1/x)^2}{4\alpha^2} $$

    2.  **Galois Action:**
      Since $P \in E(K)$, for any $\sigma \in \text{Gal}(\bar K/K)$:
      $$ 2(\sigma Q) = \sigma(2Q) = \sigma(P) = P = 2Q $$
      Thus $\sigma Q - Q \in E[2](\bar K) = \{O, T\}$.
      This implies one of two cases for the action of $\sigma$:
      $$ (\dagger) \quad \sigma Q = Q \quad \text{or} \quad \sigma Q = Q + T $$

    3.  **Action on $\alpha$:**
      Apply Lemma 2 to $\alpha = r(Q)$:
      - If $\sigma Q = Q$, then $\sigma(\alpha) = \alpha$.
      - If $\sigma Q = Q + T$, then $\sigma(\alpha) = r(Q+T) = -r(Q) = -\alpha$.

      So for every $\sigma$:
      $$ (\ddagger) \quad \sigma(\alpha) = \pm \alpha $$
      In particular, $\sigma(\alpha^2) = (\pm \alpha)^2 = \alpha^2$, so $\alpha^2 \in K$.

      Also by Lemma 1, if $\sigma Q = Q+T$ then $x \mapsto 1/x$, hence $(x - 1/x) \mapsto -(x - 1/x)$.
      Therefore $(x - 1/x)^2 \in K$ as well.
      (Note: The right-hand side of $(\star)$ is a quotient of two elements of $K$, consistent with $u \in K$).

    4.  **Deduction of Rationality:**
      Rearranging $(\star)$:
      $$ \alpha^2 = \frac{(x - 1/x)^2}{4u} $$
      The numerator $(x - 1/x)^2 \in K$, and $u \in K$ is a square.
      This implies $\alpha^2$ is a square in $K$.
      Let $\beta \in K$ with $\beta^2 = \alpha^2$.
      In an algebraic closure, the solutions to $z^2 = \beta^2$ are $z = \pm \beta$.
      Thus $\alpha = \pm \beta$, which implies $\alpha \in K$.

    5.  **Conclusion:**
      Return to $(\ddagger)$: since $\alpha \in K$, we have $\sigma(\alpha) = \alpha$ for all $\sigma$.
      Therefore the "$-\alpha$" case cannot happen (unless $\alpha=0$, which implies $y=0 \implies P=O$, a trivial case).

      So necessarily $\sigma Q = Q$ for all $\sigma$, which means $Q \in E(K)$.
      Thus $P = 2Q$ with $Q \in E(K)$, so $P \in 2E(K)$.
                                                                        QED

**Application to Ed25519:**
The map $u = (1+y)/(1-y)$ sends Ed25519 to Montgomery.
$u = \frac{(1+y)^2}{1-y^2}$. Since $(1+y)^2$ is always square, $u \in (K^\times)^2 \iff 1-y^2 \in (K^\times)^2$.

Note: In the implementation below, we use `EdwardsPoint.toPoint` which computes `Y/Z`.
For the raw `EdwardsPoint` fields, the check is `IsSquare(Z^2 - Y^2)`.
-/
def IsEven (P : Point Ed25519) : Prop :=
  IsSquare (1 - P.y^2)

/-- If a point is even, then it lies in the image of the doubling map. -/
theorem IsEven_iff_in_doubling_image_right (P : Point Ed25519) :
    IsEven P → ∃ Q : Point Ed25519, P = Q + Q := by
  sorry

/-- If a point lies in the image of the doubling map, then it is even. -/
theorem IsEven_iff_in_doubling_image_left (P : Point Ed25519) :
    (∃ Q : Point Ed25519, P = Q + Q) → IsEven P := by
  intro ⟨Q, hP⟩
  rw [hP]
  unfold IsEven
  have h_double_y : (Q + Q).y = (Q.y * Q.y - Ed25519.a * Q.x * Q.x) / (1 - Ed25519.d * Q.x * Q.x * Q.y * Q.y) :=
    add_y Q Q
  have ha : Ed25519.a = -1 := rfl
  rw [ha] at h_double_y
  simp only [neg_mul, one_mul] at h_double_y
  have h_double_y' : (Q + Q).y = (Q.y^2 + Q.x^2) / (1 - Ed25519.d * Q.x * Q.x * Q.y * Q.y) := by
    convert h_double_y using 2
    ring
  rw [h_double_y']
  set x := Q.x
  set y := Q.y
  set lam := Ed25519.d * x * x * y * y with hlam
  have hcurve : Ed25519.a * x^2 + y^2 = 1 + Ed25519.d * x^2 * y^2 := Q.on_curve
  rw [ha] at hcurve
  simp only [neg_mul, one_mul] at hcurve
  have h_yx : y^2 - x^2 = 1 + lam := by linear_combination hcurve
  have h_denom_ne : 1 - lam ≠ 0 := by
    have := Ed25519.denomsNeZero Q Q
    convert this.2
  have : 1 - ((y^2 + x^2) / (1 - lam))^2 = ((1 - lam)^2 - (y^2 + x^2)^2) / (1 - lam)^2 := by
    field_simp [h_denom_ne]
  rw [this]
  have h_factor : (1 - lam)^2 - (y^2 + x^2)^2 = (1 - lam - y^2 - x^2) * (1 - lam + y^2 + x^2) := by
    ring
  have h_lam_eq : lam = y^2 - x^2 - 1 := by
    have h : y^2 - x^2 - 1 - lam = 0 := by linear_combination h_yx
    linear_combination -h
  have h1mlam : 1 - lam = 2 + x^2 - y^2 := by
    rw [h_lam_eq]
    ring
  have h_A : 1 - lam - y^2 - x^2 = 2 - 2*y^2 := by linear_combination h1mlam
  have h_B : 1 - lam + y^2 + x^2 = 2 + 2*x^2 := by linear_combination h1mlam
  rw [h_factor, h_A, h_B]
  have h_factor_simp : (2 - 2*y^2) * (2 + 2*x^2) = 4 * (1 - y^2) * (1 + x^2) := by ring
  rw [h_factor_simp]
  have h_1my : 1 - y^2 = -lam - x^2 := by linear_combination -h_yx
  rw [h_1my]
  have h_sign : 4 * (-lam - x^2) * (1 + x^2) = -4 * (lam + x^2) * (1 + x^2) := by ring
  rw [h_sign]
  have h_neg1_sq : IsSquare (-1 : CurveField) := neg_one_is_square
  have h_4_sq : IsSquare (4 : CurveField) := ⟨2, by ring⟩
  have h_neg4_sq : IsSquare (-4 : CurveField) := IsSquare.mul h_neg1_sq h_4_sq
  have h_lam_factor : lam + x^2 = x^2 * (Ed25519.d * y^2 + 1) := by
    rw [hlam]
    ring
  rw [h_lam_factor]
  have h_lam_x : lam + x^2 = y^2 - 1 := by linear_combination h_lam_eq
  have h_x2_dy : x^2 * (Ed25519.d * y^2 + 1) = y^2 - 1 := by
    calc x^2 * (Ed25519.d * y^2 + 1) = lam + x^2 := by rw [← h_lam_factor]
         _ = y^2 - 1 := h_lam_x
  rw [h_x2_dy]
  rw [h1mlam]
  have h_rw : (2 + x ^ 2 - y ^ 2) ^ 2 = (1 - lam) ^ 2 := by
    congr 1
    exact h1mlam.symm
  rw [h_rw]
  have h_num_sq : IsSquare (-4 * (y ^ 2 - 1) * (1 + x ^ 2)) := by
    rw [← h_lam_x]
    rw [h_lam_factor]
    have h_rearrange : -4 * (x ^ 2 * (Ed25519.d * y ^ 2 + 1)) * (1 + x ^ 2) =
                       -4 * (x ^ 2 * ((Ed25519.d * y ^ 2 + 1) * (1 + x ^ 2))) := by ring
    rw [h_rearrange]
    apply IsSquare.mul h_neg4_sq
    apply IsSquare.mul
    · exact ⟨x, pow_two x⟩
    · have h_expand : (Ed25519.d * y^2 + 1) * (1 + x^2) = y^2 * (1 + Ed25519.d) := by
        have h_dxy : Ed25519.d * x^2 * y^2 = y^2 - x^2 - 1 := by
          calc Ed25519.d * x^2 * y^2 = (1 + Ed25519.d * x^2 * y^2) - 1 := by ring
            _ = (-x^2 + y^2) - 1 := by rw [← hcurve]
            _ = y^2 - x^2 - 1 := by ring
        calc (Ed25519.d * y^2 + 1) * (1 + x^2)
            = Ed25519.d * y^2 + Ed25519.d * y^2 * x^2 + 1 + x^2 := by ring
          _ = Ed25519.d * y^2 + Ed25519.d * x^2 * y^2 + 1 + x^2 := by ring
          _ = Ed25519.d * y^2 + (y^2 - x^2 - 1) + 1 + x^2 := by rw [h_dxy]
          _ = Ed25519.d * y^2 + y^2 := by ring
          _ = y^2 * (Ed25519.d + 1) := by ring
          _ = y^2 * (1 + Ed25519.d) := by ring
      rw [h_expand]
      have h_one_add_d_sq : IsSquare (1 + Ed25519.d) := by
        change IsSquare ((1 + d : ℕ) : CurveField)
        have h_ne : ((1 + d : ℕ) : CurveField) ≠ 0 := by decide
        rw [← legendreSym.eq_one_iff' p h_ne]
        norm_num [d, p]
      apply IsSquare.mul
      · exact ⟨y, pow_two y⟩
      · exact h_one_add_d_sq
  obtain ⟨c, hc⟩ := h_num_sq
  use c / (1 - lam)
  field_simp [h_denom_ne, pow_ne_zero 2 h_denom_ne]
  convert hc using 1
  · ring
  · exact pow_two c

/-- A point is even if and only if it lies in the image of the doubling map. -/
theorem IsEven_iff_in_doubling_image (P : Point Ed25519) :
    IsEven P ↔ ∃ Q : Point Ed25519, P = Q + Q := by
  constructor
  · exact IsEven_iff_in_doubling_image_right P
  · exact IsEven_iff_in_doubling_image_left P

/-- The set of even points is closed under addition. -/
theorem even_add_closure_Ed25519 (P Q : Point Ed25519) (hP : IsEven P) (hQ : IsEven Q) :
    IsEven (P + Q) := by
  rw [IsEven_iff_in_doubling_image] at *
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  exact ⟨P' + Q', by abel⟩

/-- For a valid Edwards point in projective coordinates, `Z² - Y²` is a square
if and only if the corresponding affine point is even. -/
theorem EdwardsPoint_IsSquare_iff_IsEven (e : EdwardsPoint) (h : e.IsValid) :
    IsSquare (e.Z.toField^2 - e.Y.toField^2) ↔ IsEven (e.toPoint) := by
  unfold IsEven
  obtain ⟨_, hy⟩ := EdwardsPoint.toPoint_of_isValid h
  rw [hy]
  have hz : e.Z.toField ≠ 0 := h.Z_ne_zero
  have hz2 : e.Z.toField^2 ≠ 0 := pow_ne_zero 2 hz
  have : 1 - (e.Y.toField / e.Z.toField)^2 = (e.Z.toField^2 - e.Y.toField^2) / e.Z.toField^2 := by
    field_simp [hz2]
  rw [this]
  constructor
  · intro ⟨w, hw⟩
    use w / e.Z.toField
    field_simp [hz2] at hw ⊢
    convert hw using 1
  · intro ⟨w, hw⟩
    use w * e.Z.toField
    field_simp [hz2] at hw ⊢
    convert hw using 1

/-- Validity for RistrettoPoint is delegated to EdwardsPoint. -/
def RistrettoPoint.IsValid (r : RistrettoPoint) : Prop :=
  -- 1. Must be a valid curve point (satisfy -x² + y² = 1 + dx²y²)
  EdwardsPoint.IsValid r ∧
  -- 2. Must be an "Even" point (IsSquare (1 - y²))
  -- Equation: 1 - (Y/Z)² = (Z² - Y²) / Z². Since Z² is square, we check Z² - Y².
  let Y := r.Y.toField
  let Z := r.Z.toField
  IsSquare (Z^2 - Y^2)

/-- Conversion to mathematical Point.
    Returns the internal Edwards point representative. -/
def RistrettoPoint.toPoint (r : RistrettoPoint) : Point Ed25519 :=
  EdwardsPoint.toPoint r

/--
**Pure Decompression**
Deduces (x, y) from s using the isogeny inversion formulas:
  - https://ristretto.group/details/isogenies.html
  - https://ristretto.group/formulas/decoding.html
In particular, the function below is an inverse of θ_a₂,d₂ and using the formula:
t^2 = a_2^2 s^4 + 2(-a_2 \frac{a_2+d_2}{a_2-d_2}) s^2 + 1 (Eq ⋆)
Indeed:
  - x := abs(2 * s * Dx) = abs(\frac{2s}{√ v}) = frac{1}{√ad-1} · \frac{2s}{t}
  - y := u1 * Dy = \frac{1+as²}{1-as²}
Equation (⋆) is obtained from the Jacobi quadric `J`: t² = e * s⁴ + 2 * A * s² + 1
where `e = a₁²` and `A = a₁ - 2d₁`. Ristretto uses parameters `a₂, d₂` (where `a₂ = -1` and `d₂ = d`
for Ed25519). The relation to `J` parameters is:
  - `a₁ = -a₂`
  - `d₁ = (a₂ * d₂) / (a₂ - d₂)`
Notice that `t²` is proportional to the discriminant `v = (a₂*d₂ - 1) * t²`.
Namely the whole decompress is made of two steps:
**Step 1**: Canonical Encoding & Parity Check
Isolates the integer-level validation logic.
Corresponds to the `if` block in the original `decompress_pure`.
**Step 2**: Algebraic Lifting
Isolates the field arithmetic and curve geometry.
Corresponds to the `else` block (arithmetic) in the original `decompress_pure`.
-/
def decompress_step1 (c : CompressedRistretto) : Option (ZMod p) :=
  let s_int := U8x32_as_Nat c
  -- Check 1: Canonical encoding (s_int < p)
  -- Check 2: Parity (least significant bit is 0)
  if s_int >= p || s_int % 2 != 0 then
    none
  else
    some (s_int : ZMod p)

noncomputable def decompress_step2 (s : ZMod p) : Option (Point Ed25519) :=
  -- 1. Algebraic setup
  let u1 := 1 + a_val * s^2
  let u2 := 1 - a_val * s^2
  let v := a_val * d * u1^2 - u2^2
  -- 2. Inverse Square Root (Elligator)
  let arg := v * u2^2
  match h_call : inv_sqrt_checked arg with
  | (I, was_square) =>
    -- 3. Recover denominators
    let Dx := I * u2
    let Dy := I * Dx * v
    -- 4. Recover coordinates
    let x := abs_edwards (2 * s * Dx)
    let y := u1 * Dy
    -- 5. Validation Checks
    let t := x * y
    if h_invalid : !was_square || is_negative t || (y == 0) then
      none
    else
      -- 6. Construct Point with Proof
      some { x := x, y := y, on_curve := by
              -- Re-using your exact proof script
              replace h_invalid := Bool.eq_false_iff.mpr h_invalid
              rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h_invalid
              obtain ⟨⟨h_sq_not, h_neg_false⟩, h_y_eq_false⟩ := h_invalid
              simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_sq_not
              have h_I_sq_mul : I^2 * (v * u2^2) = 1 := by
                apply inv_sqrt_checked_spec arg
                · exact h_call
                · exact h_sq_not
                · -- arg ≠ 0: follows from was_square = true + inv_sqrt_checked's zero guard
                  intro h_zero
                  rw [h_zero] at h_call
                  rw [inv_sqrt_checked_zero] at h_call; simp only [Prod.mk.injEq,
                    Bool.false_eq] at h_call
                  exact absurd h_call.2 (by rw [h_sq_not]; decide)
              let x_raw := 2 * s * Dx
              have h_curve_raw : a_val * x_raw^2 + y^2 = 1 + d * x_raw^2 * y^2 := by
                dsimp only [y, Dy, Dx, x_raw]
                apply decompress_helper a_val d s I u1 u2 v
                <;> try rw [a_val];
                <;> try rfl
                exact h_I_sq_mul
              have h_x_sq : x^2 = x_raw^2 := by
                dsimp only [x]
                exact abs_edwards_sq (2 * s * Dx)
              rw [h_x_sq]
              exact h_curve_raw
           }

/-- Forward characterization: if decompress_step2 returns some point, then
    the arg is a nonzero square, validation passes, and coordinates are determined
    by inv_sqrt_checked. -/
lemma decompress_step2_1 (s : ZMod p) (pt : Point Ed25519)
    (h : decompress_step2 s = some pt) :
    let u1 := 1 + a_val * s ^ 2
    let u2 := 1 - a_val * s ^ 2
    let v := a_val * (d : CurveField) * u1 ^ 2 - u2 ^ 2
    let W := v * u2 ^ 2
    let I := (inv_sqrt_checked W).1
    IsSquare W ∧ W ≠ 0 ∧
    is_negative (abs_edwards (2 * s * (I * u2)) * (u1 * (I * (I * u2) * v))) = false ∧
    u1 * (I * (I * u2) * v) ≠ 0 ∧
    pt.x = abs_edwards (2 * s * (I * u2)) ∧
    pt.y = u1 * (I * (I * u2) * v) := by
  unfold decompress_step2 at h
  dsimp only at h
  split_ifs at h with h_invalid
  -- some branch: h_invalid is ¬(...), h : some {...} = some pt
  -- Extract point equality
  have h_pt := Option.some.inj h
  -- Introduce goal let bindings
  intro u1 u2 v W I
  -- Decompose the three validation conditions (mirrors on_curve proof pattern)
  replace h_invalid := Bool.eq_false_iff.mpr h_invalid
  rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h_invalid
  obtain ⟨⟨h_ws, h_neg⟩, h_y_eq⟩ := h_invalid
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_ws
  -- Lift expanded hypotheses to compact let-binding types (definitional equality)
  have h_ws' : (inv_sqrt_checked W).2 = true := h_ws
  have h_neg' : is_negative (abs_edwards (2 * s * (I * u2)) *
    (u1 * (I * (I * u2) * v))) = false := h_neg
  have h_y_eq' : (u1 * (I * (I * u2) * v) == (0 : ZMod p)) = false := h_y_eq
  -- W ≠ 0 from was_square = true + inv_sqrt_checked's zero guard
  have h_W_ne : W ≠ 0 := by
    intro h_zero
    have : (inv_sqrt_checked W).2 = false := by
      rw [show W = (0 : ZMod p) from h_zero, inv_sqrt_checked_zero]
    rw [h_ws'] at this; exact absurd this (by decide)
  -- IsSquare W via sqrt_checked_iff_isSquare (b = true ↔ IsSquare u)
  have h_sq_W : IsSquare W := by
    have h_sc : (sqrt_checked W).2 = true := by rw [← inv_sqrt_checked_snd W h_W_ne]; exact h_ws'
    exact (sqrt_checked_iff_isSquare W (Prod.mk.eta (p := sqrt_checked W)).symm).mp h_sc
  -- y ≠ 0 from BEq
  have h_y_ne : u1 * (I * (I * u2) * v) ≠ 0 := by
    exact beq_eq_false_iff_ne.mp h_y_eq'
  -- Coordinate equalities from h_pt
  have hx : pt.x = abs_edwards (2 * s * (I * u2)) := by rw [← h_pt]
  have hy : pt.y = u1 * (I * (I * u2) * v) := by rw [← h_pt]
  exact ⟨h_sq_W, h_W_ne, h_neg', h_y_ne, hx, hy⟩

/-- Backward characterization: given ANY I with I² * W = 1, if the point
    coordinates match those computed from I, validation passes, and y ≠ 0,
    then decompress_step2 returns that point.
    Key insight: the output only depends on I² = W⁻¹ (not on I's sign),
    because y uses I² and x uses abs_edwards (sign-independent). -/
lemma decompress_step2_2 (s : ZMod p) (pt : Point Ed25519) (I : ZMod p)
    (hI : I ^ 2 * ((a_val * (d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
      (1 - a_val * s ^ 2) ^ 2) * (1 - a_val * s ^ 2) ^ 2) = 1)
    (h_neg : is_negative (pt.x * pt.y) = false)
    (h_y_ne : pt.y ≠ 0)
    (hx : pt.x = abs_edwards (2 * s * (I * (1 - a_val * s ^ 2))))
    (hy : pt.y = (1 + a_val * s ^ 2) *
      (I * (I * (1 - a_val * s ^ 2)) *
        (a_val * (d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
          (1 - a_val * s ^ 2) ^ 2))) :
    decompress_step2 s = some pt := by
  -- Abbreviation for W (the arg to inv_sqrt_checked in decompress_step2)
  set W := (a_val * (d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
    (1 - a_val * s ^ 2) ^ 2) * (1 - a_val * s ^ 2) ^ 2
  -- 1. Key algebraic facts (established BEFORE unfolding)
  have h_W_ne : W ≠ 0 := right_ne_zero_of_mul_eq_one hI
  have h_I_ne : I ≠ 0 := by intro h; simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul, zero_ne_one] at hI
  have h_sq_W : IsSquare W := ⟨I⁻¹, by
    have : W = (I ^ 2)⁻¹ := by rw [eq_inv_of_mul_eq_one_left hI, inv_inv]
    rw [this, ← inv_pow, sq]⟩
  -- 2. inv_sqrt_checked W returns true (was_square = true)
  have h_ws : (inv_sqrt_checked W).2 = true := by
    rw [inv_sqrt_checked_snd W h_W_ne]
    exact (sqrt_checked_iff_isSquare W (Prod.mk.eta (p := sqrt_checked W)).symm).mpr h_sq_W
  -- 3. I² = I'² (both equal W⁻¹)
  have h_I'_sq : (inv_sqrt_checked W).1 ^ 2 * W = 1 :=
    inv_sqrt_checked_sq_mul W h_sq_W h_W_ne
  have h_sq_eq : I ^ 2 = (inv_sqrt_checked W).1 ^ 2 :=
    mul_right_cancel₀ h_W_ne (by rw [hI, h_I'_sq])
  -- 4. y coordinate: u1 * I' * (I' * u2) * v = u1 * I * (I * u2) * v (uses I² = I'²)
  have h_y_match : (1 + a_val * s ^ 2) *
      ((inv_sqrt_checked W).1 * ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2)) *
        (a_val * (d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
          (1 - a_val * s ^ 2) ^ 2)) = pt.y := by
    rw [hy]; congr 1
    have h1 : (inv_sqrt_checked W).1 * ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2)) *
      (a_val * ↑d * (1 + a_val * s ^ 2) ^ 2 - (1 - a_val * s ^ 2) ^ 2) =
      (inv_sqrt_checked W).1 ^ 2 * (1 - a_val * s ^ 2) *
      (a_val * ↑d * (1 + a_val * s ^ 2) ^ 2 - (1 - a_val * s ^ 2) ^ 2) := by ring
    have h2 : I * (I * (1 - a_val * s ^ 2)) *
      (a_val * ↑d * (1 + a_val * s ^ 2) ^ 2 - (1 - a_val * s ^ 2) ^ 2) =
      I ^ 2 * (1 - a_val * s ^ 2) *
      (a_val * ↑d * (1 + a_val * s ^ 2) ^ 2 - (1 - a_val * s ^ 2) ^ 2) := by ring
    rw [h1, h2, h_sq_eq]
  -- 5. x coordinate: abs_edwards(2s * I' * u2) = abs_edwards(2s * I * u2) (I' = ±I)
  have h_x_match : abs_edwards (2 * s * ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2))) =
      pt.x := by
    rw [hx]
    have h_sq_x : (2 * s * ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2))) ^ 2 =
        (2 * s * (I * (1 - a_val * s ^ 2))) ^ 2 := by
      have h1 : (2 * s * ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2))) ^ 2 =
        4 * s ^ 2 * (inv_sqrt_checked W).1 ^ 2 * (1 - a_val * s ^ 2) ^ 2 := by ring
      have h2 : (2 * s * (I * (1 - a_val * s ^ 2))) ^ 2 =
        4 * s ^ 2 * I ^ 2 * (1 - a_val * s ^ 2) ^ 2 := by ring
      rw [h1, h2, h_sq_eq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h_sq_x with h_eq | h_neg_eq
    · rw [h_eq]
    · rw [h_neg_eq]; exact abs_edwards_neg _
  -- 6. Validation condition is false (ws=true, is_neg=false, y≠0)
  -- is_negative(x_internal * y_internal) = is_negative(pt.x * pt.y) = false
  have h_neg_match : is_negative (abs_edwards (2 * s *
      ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2))) *
    ((1 + a_val * s ^ 2) * ((inv_sqrt_checked W).1 *
      ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2)) *
      (a_val * (d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
        (1 - a_val * s ^ 2) ^ 2)))) = false := by
    rw [h_x_match, h_y_match]; exact h_neg
  have h_y_ne_match : ((1 + a_val * s ^ 2) * ((inv_sqrt_checked W).1 *
      ((inv_sqrt_checked W).1 * (1 - a_val * s ^ 2)) *
      (a_val * (d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
        (1 - a_val * s ^ 2) ^ 2)) == (0 : ZMod p)) = false := by
    rw [h_y_match]; exact beq_eq_false_iff_ne.mpr h_y_ne
  -- 7. Unfold decompress_step2 and close
  unfold decompress_step2; dsimp only
  split_ifs with h_cond
  · -- none branch: contradiction (validation should pass)
    -- h_cond uses full expansion but h_ws/h_neg_match/h_y_ne_match use W (set abbrev);
    simp_all only [ne_eq, mul_eq_zero, false_or, not_or, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      or_self, mul_eq_mul_left_iff, mul_eq_mul_right_iff, or_false, beq_eq_false_iff_ne, Bool.not_true, Bool.or_self,
      Bool.false_or, beq_iff_eq, W]
  · -- some branch: show point equality
    congr 1; ext
    · exact h_x_match
    · exact h_y_match

set_option maxHeartbeats 400000 in -- maxHeartbeats increased:
/-- Decode-of-encode: decompressing the scalar produced by compression succeeds.
    This is the pure math core of the Ristretto roundtrip property. -/
lemma decompress_step2_compress_s (P : Point Ed25519) (heven : IsEven P) :
    ∃ pt, decompress_step2 (compress_s P) = some pt := by
  by_cases h_degen : compress_u1 P * compress_u2 P ^ 2 = 0
  · -- DEGENERATE CASE: invsqrt argument is 0, so compress_s P = 0
    have h_I_zero : compress_invsqrt P = 0 := by
      unfold compress_invsqrt; rw [h_degen, inv_sqrt_checked_zero]
    have h_den1_zero : compress_den1 P = 0 := by unfold compress_den1; rw [h_I_zero, zero_mul]
    have h_den2_zero : compress_den2 P = 0 := by unfold compress_den2; rw [h_I_zero, zero_mul]
    have h_zinv_zero : compress_z_inv P = 0 := by
      unfold compress_z_inv; rw [h_den1_zero, zero_mul, zero_mul]
    have h_no_rotate : compress_rotate P = false := by
      unfold compress_rotate; rw [h_zinv_zero, mul_zero]; rfl
    have h_deninv_zero : compress_den_inv P = 0 := by
      unfold compress_den_inv; rw [h_no_rotate, if_neg (by decide)]; exact h_den2_zero
    have h_s_zero : compress_s P = 0 := by
      unfold compress_s; rw [h_deninv_zero, zero_mul]
      unfold abs_edwards is_negative; simp
    rw [h_s_zero]
    -- decompress_step2 0 = some (0, 1) via decompress_step2_2
    have h_on_curve : Ed25519.a * (0 : ZMod p) ^ 2 + 1 ^ 2 =
        1 + Ed25519.d * 0 ^ 2 * 1 ^ 2 := by ring
    let pt : Point Ed25519 := ⟨0, 1, h_on_curve⟩
    have h_W_simp : (a_val * (↑d : CurveField) * (1 + a_val * (0 : ZMod p) ^ 2) ^ 2 -
        (1 - a_val * (0 : ZMod p) ^ 2) ^ 2) * (1 - a_val * (0 : ZMod p) ^ 2) ^ 2 =
        a_val - (↑d : ZMod p) := by unfold a_val; ring
    have h_hy : pt.y = (1 + a_val * (0 : ZMod p) ^ 2) *
        (invsqrt_a_minus_d * (invsqrt_a_minus_d * (1 - a_val * (0 : ZMod p) ^ 2)) *
          (a_val * (↑d : CurveField) * (1 + a_val * (0 : ZMod p) ^ 2) ^ 2 -
            (1 - a_val * (0 : ZMod p) ^ 2) ^ 2)) := by
      change (1 : ZMod p) = _
      have h := iad_sq
      have h_ring : (1 + a_val * (0 : ZMod p) ^ 2) *
          (invsqrt_a_minus_d * (invsqrt_a_minus_d * (1 - a_val * (0 : ZMod p) ^ 2)) *
            (a_val * (↑d : CurveField) * (1 + a_val * (0 : ZMod p) ^ 2) ^ 2 -
              (1 - a_val * (0 : ZMod p) ^ 2) ^ 2)) =
          invsqrt_a_minus_d ^ 2 * (a_val - ↑d) := by unfold a_val; ring
      rw [h_ring]; exact h.symm
    exact ⟨pt, decompress_step2_2 0 pt invsqrt_a_minus_d
      (by rw [h_W_simp]; exact iad_sq)
      (by change is_negative (0 * 1 : ZMod p) = false; simp [is_negative])
      one_ne_zero
      (by change (0 : ZMod p) = abs_edwards (2 * 0 * (invsqrt_a_minus_d * (1 - a_val * 0 ^ 2)))
          simp [abs_edwards, is_negative])
      h_hy⟩
  · -- NON-DEGENERATE CASE: compress_u1 P * compress_u2 P ^ 2 ≠ 0
    -- Setup: extract non-zero conditions
    have h_u1_ne : compress_u1 P ≠ 0 := left_ne_zero_of_mul h_degen
    have h_u2_ne : compress_u2 P ≠ 0 := by
      intro h; exact h_degen (by rw [h, sq, mul_zero, mul_zero])
    -- IsSquare for compression argument
    have h_u1_sq : IsSquare (compress_u1 P) := by
      have : compress_u1 P = 1 - P.y ^ 2 := by unfold compress_u1; ring
      rw [this]; exact heven
    have h_arg_sq : IsSquare (compress_u1 P * compress_u2 P ^ 2) :=
      h_u1_sq.mul ⟨compress_u2 P, (sq _)⟩
    -- Compression invsqrt: I² * (u1 * u2²) = 1
    have h_I_sq : compress_invsqrt P ^ 2 * (compress_u1 P * compress_u2 P ^ 2) = 1 := by
      unfold compress_invsqrt; exact inv_sqrt_checked_sq_mul _ h_arg_sq h_degen
    -- On-curve relation (rewritten with a = -1)
    have h_curve : P.y ^ 2 - P.x ^ 2 = 1 + (↑d : ZMod p) * P.x ^ 2 * P.y ^ 2 := by
      have := P.on_curve; simp only [Ed25519, neg_mul, one_mul] at this; linear_combination (this)
    -- KEY IDENTITY: D² · (1 - y_f²) = 1
    have h_den_cancel : compress_den_inv P ^ 2 * (1 - compress_y_final P ^ 2) = 1 := by
      by_cases h_rot : compress_rotate P
      · -- Rotate case: D = I · u1 · iad, y_f² = -P.x²
        have hD : compress_den_inv P = compress_invsqrt P * compress_u1 P * invsqrt_a_minus_d := by
          unfold compress_den_inv compress_den1; rw [if_pos h_rot]
        have h_yprime : compress_y_prime P = P.x * sqrt_m1 := by
          unfold compress_y_prime; rw [if_pos h_rot]
        have h_yf_sq : compress_y_final P ^ 2 = -(P.x ^ 2) := by
          unfold compress_y_final; rw [h_yprime]
          split_ifs <;> (try rw [neg_sq]) <;>
            rw [show (P.x * sqrt_m1) ^ 2 = P.x ^ 2 * sqrt_m1 ^ 2 from by ring, sqrt_m1_sq] <;> ring
        -- From curve: u1 · (1 + P.x²) = u2² · (a - d)
        have h_factor : compress_u1 P * (1 + P.x ^ 2) =
            compress_u2 P ^ 2 * (a_val - (↑d : ZMod p)) := by
          unfold compress_u1 compress_u2 a_val
          linear_combination -h_curve
        calc compress_den_inv P ^ 2 * (1 - compress_y_final P ^ 2)
            = (compress_invsqrt P * compress_u1 P * invsqrt_a_minus_d) ^ 2 * (1 + P.x ^ 2) := by
              rw [hD, h_yf_sq]; ring
          _ = compress_invsqrt P ^ 2 * compress_u1 P *
              (compress_u1 P * (1 + P.x ^ 2)) * invsqrt_a_minus_d ^ 2 := by ring
          _ = compress_invsqrt P ^ 2 * compress_u1 P *
              (compress_u2 P ^ 2 * (a_val - ↑d)) * invsqrt_a_minus_d ^ 2 := by rw [h_factor]
          _ = (compress_invsqrt P ^ 2 * (compress_u1 P * compress_u2 P ^ 2)) *
              (invsqrt_a_minus_d ^ 2 * (a_val - ↑d)) := by ring
          _ = 1 * 1 := by rw [h_I_sq, iad_sq]
          _ = 1 := one_mul 1
      · -- No-rotate case: D = I · u2, y_f² = P.y²
        have h_rot_false : compress_rotate P = false := by
          revert h_rot; cases compress_rotate P <;> simp
        have hD : compress_den_inv P = compress_invsqrt P * compress_u2 P := by
          unfold compress_den_inv compress_den2; rw [h_rot_false, if_neg (by decide)]
        have h_yprime : compress_y_prime P = P.y := by
          unfold compress_y_prime; rw [h_rot_false, if_neg (by decide)]
        have h_yf_sq : compress_y_final P ^ 2 = P.y ^ 2 := by
          unfold compress_y_final; rw [h_yprime]; split_ifs <;> ring
        have h_u1_eq : 1 - compress_y_final P ^ 2 = compress_u1 P := by
          rw [h_yf_sq]; unfold compress_u1; ring
        calc compress_den_inv P ^ 2 * (1 - compress_y_final P ^ 2)
            = (compress_invsqrt P * compress_u2 P) ^ 2 * compress_u1 P := by
              rw [hD, h_u1_eq]
          _ = compress_invsqrt P ^ 2 * (compress_u1 P * compress_u2 P ^ 2) := by ring
          _ = 1 := h_I_sq
    -- From h_den_cancel, derive the Mobius identity
    have h_sigma_sq : compress_s P ^ 2 = compress_den_inv P ^ 2 * (1 - compress_y_final P) ^ 2 := by
      unfold compress_s; rw [abs_edwards_sq]; ring
    have h_mobius : compress_s P ^ 2 * (1 + compress_y_final P) = 1 - compress_y_final P := by
      rw [h_sigma_sq]
      have : compress_den_inv P ^ 2 * (1 - compress_y_final P) ^ 2 * (1 + compress_y_final P) =
          compress_den_inv P ^ 2 * (1 - compress_y_final P ^ 2) * (1 - compress_y_final P) := by ring
      rw [this, h_den_cancel]; ring
    -- === Use h_mobius + h_den_cancel to show decompress_step2 succeeds ===
    set σ := compress_s P with hσ_def
    set y_f := compress_y_final P with hyf_def
    set D := compress_den_inv P with hD_def
    set x' := compress_x_prime P with hx'_def
    -- Non-zero conditions from h_den_cancel
    have h_1_sub_yf_sq_ne : (1 : ZMod p) - y_f ^ 2 ≠ 0 :=
      right_ne_zero_of_mul_eq_one h_den_cancel
    have h_1_plus_yf_ne : (1 : ZMod p) + y_f ≠ 0 := by
      intro h; apply h_1_sub_yf_sq_ne
      have : (1 : ZMod p) - y_f ^ 2 = (1 - y_f) * (1 + y_f) := by ring
      rw [this, h, mul_zero]
    have h_1_sub_yf_ne : (1 : ZMod p) - y_f ≠ 0 := by
      intro h; apply h_1_sub_yf_sq_ne
      have : (1 : ZMod p) - y_f ^ 2 = (1 - y_f) * (1 + y_f) := by ring
      rw [this, h, zero_mul]
    have h_D_ne : D ≠ 0 := by
      intro h; rw [h, zero_pow (by omega : 2 ≠ 0), zero_mul] at h_den_cancel
      exact zero_ne_one h_den_cancel
    have h_sigma_ne : σ ≠ 0 := by
      intro h; rw [h, zero_pow (by omega : 2 ≠ 0)] at h_sigma_sq
      exact (mul_ne_zero (pow_ne_zero 2 h_D_ne) (pow_ne_zero 2 h_1_sub_yf_ne)) h_sigma_sq.symm
    have h_px_ne : P.x ≠ 0 := by
      intro h; exact h_u2_ne (by unfold compress_u2; rw [h, zero_mul])
    have h_py_ne : P.y ≠ 0 := by
      intro h; exact h_u2_ne (by unfold compress_u2; rw [h, mul_zero])
    have h_sqrt_m1_ne : (sqrt_m1 : ZMod p) ≠ 0 := by
      intro h; have hsm := sqrt_m1_sq; rw [h, zero_pow (by omega : 2 ≠ 0)] at hsm
      exact (neg_ne_zero.mpr one_ne_zero) hsm.symm
    have h_xprime_ne : x' ≠ 0 := by
      simp only [hx'_def]; unfold compress_x_prime
      split_ifs <;> [exact mul_ne_zero h_py_ne h_sqrt_m1_ne; exact h_px_ne]
    -- compress_z_inv P = 1
    have h_z_inv_one : compress_z_inv P = 1 := by
      unfold compress_z_inv compress_den1 compress_den2
      have : compress_invsqrt P * compress_u1 P * (compress_invsqrt P * compress_u2 P) *
          (P.x * P.y) = compress_invsqrt P ^ 2 * (compress_u1 P * compress_u2 P ^ 2) := by
        unfold compress_u2; ring
      rw [this]; exact h_I_sq
    -- Squared values: x'^2 and y_f^2 in terms of P.x^2 and P.y^2
    have h_xprime_sq : x' ^ 2 = if compress_rotate P then -(P.y ^ 2) else P.x ^ 2 := by
      simp only [hx'_def]; unfold compress_x_prime; split_ifs with h
      · rw [show (P.y * sqrt_m1) ^ 2 = P.y ^ 2 * sqrt_m1 ^ 2 from by ring, sqrt_m1_sq]; ring
      · rfl
    have h_yfinal_sq : y_f ^ 2 = if compress_rotate P then -(P.x ^ 2) else P.y ^ 2 := by
      simp only [hyf_def]; unfold compress_y_final compress_y_prime
      split_ifs <;> ring_nf <;> rw [sqrt_m1_sq] <;> ring
    -- On-curve identity for canonical coordinates
    have h_can : x' ^ 2 * (1 + ↑d * y_f ^ 2) = y_f ^ 2 - 1 := by
      rw [h_xprime_sq, h_yfinal_sq]; split_ifs <;> linear_combination -h_curve
    -- y_f ≠ 0
    have h_yf_ne : y_f ≠ 0 := by
      simp only [hyf_def]; unfold compress_y_final compress_y_prime
      split_ifs <;>
        [exact neg_ne_zero.mpr (mul_ne_zero h_px_ne h_sqrt_m1_ne);
         exact neg_ne_zero.mpr h_py_ne;
         exact mul_ne_zero h_px_ne h_sqrt_m1_ne;
         exact h_py_ne]
    -- Mobius reformulation: y_f * u2_dec = u1_dec
    have h_yf_u2 : y_f * (1 - a_val * σ ^ 2) = 1 + a_val * σ ^ 2 := by
      unfold a_val; linear_combination h_mobius
    -- Key identity: x'^2 * v_dec = 4 * σ^2
    -- (proved by clearing (1+y_f)^2 denominator using h_mobius + h_can)
    have h_xsq_v : x' ^ 2 * (a_val * ↑d * (1 + a_val * σ ^ 2) ^ 2 -
        (1 - a_val * σ ^ 2) ^ 2) = 4 * σ ^ 2 := by
      apply mul_right_cancel₀ (pow_ne_zero 2 h_1_plus_yf_ne)
      have h1 : (1 + a_val * σ ^ 2) * (1 + y_f) = 2 * y_f := by
        unfold a_val; linear_combination -h_mobius
      have h2 : (1 - a_val * σ ^ 2) * (1 + y_f) = 2 := by
        unfold a_val; linear_combination h_mobius
      have h_lhs : x' ^ 2 * (a_val * ↑d * (1 + a_val * σ ^ 2) ^ 2 -
          (1 - a_val * σ ^ 2) ^ 2) * (1 + y_f) ^ 2 =
          x' ^ 2 * (a_val * ↑d * ((1 + a_val * σ ^ 2) * (1 + y_f)) ^ 2 -
          ((1 - a_val * σ ^ 2) * (1 + y_f)) ^ 2) := by ring
      rw [h_lhs, h1, h2]
      have h_rhs : 4 * σ ^ 2 * (1 + y_f) ^ 2 = 4 * (1 - y_f) * (1 + y_f) := by
        linear_combination 4 * (1 + y_f) * h_mobius
      rw [h_rhs]; unfold a_val
      linear_combination -4 * h_can
    -- W_dec and IsSquare/nonzero
    set v_dec := a_val * ↑d * (1 + a_val * σ ^ 2) ^ 2 - (1 - a_val * σ ^ 2) ^ 2
    set W_dec := v_dec * (1 - a_val * σ ^ 2) ^ 2
    have h2_ne : (2 : ZMod p) ≠ 0 :=
      haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
      ZMod.prime_ne_zero p 2 (by unfold p; norm_num)
    have h_v_ne : v_dec ≠ 0 := by
      intro h; rw [h, mul_zero] at h_xsq_v
      have : (2 * σ) ^ 2 = 0 := by linear_combination -h_xsq_v
      exact mul_ne_zero h2_ne h_sigma_ne (sq_eq_zero_iff.mp this)
    have h_u2_dec_ne : (1 - a_val * σ ^ 2 : ZMod p) ≠ 0 := by
      intro h
      have : (1 - a_val * σ ^ 2) * (1 + y_f) = 2 := by
        unfold a_val; linear_combination h_mobius
      rw [h, zero_mul] at this; exact h2_ne this.symm
    have h_W_ne : W_dec ≠ 0 :=
      mul_ne_zero h_v_ne (pow_ne_zero 2 h_u2_dec_ne)
    have h_xsq_W : x' ^ 2 * W_dec = (2 * σ * (1 - a_val * σ ^ 2)) ^ 2 := by
      have : x' ^ 2 * W_dec = (x' ^ 2 * v_dec) * (1 - a_val * σ ^ 2) ^ 2 := by ring
      rw [this, h_xsq_v]; ring
    have h_sq_W : IsSquare W_dec := ⟨2 * σ * (1 - a_val * σ ^ 2) * x'⁻¹, by
      have hx_inv_sq : x' ^ 2 * x'⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ h_xprime_ne, one_pow]
      apply mul_left_cancel₀ (pow_ne_zero 2 h_xprime_ne)
      have : x' ^ 2 * (2 * σ * (1 - a_val * σ ^ 2) * x'⁻¹ *
          (2 * σ * (1 - a_val * σ ^ 2) * x'⁻¹)) =
          (2 * σ * (1 - a_val * σ ^ 2)) ^ 2 * (x' ^ 2 * x'⁻¹ ^ 2) := by ring
      rw [this, hx_inv_sq, mul_one, ← h_xsq_W]⟩
    -- I_dec = x' / (2 * σ * u2_dec) satisfies I^2 * W = 1
    set I_dec := x' * (2 * σ * (1 - a_val * σ ^ 2))⁻¹
    have h_denom_ne : (2 : ZMod p) * σ * (1 - a_val * σ ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2_ne h_sigma_ne) h_u2_dec_ne
    have h_I_W : I_dec ^ 2 * W_dec = 1 := by
      have hden := show I_dec = x' * (2 * σ * (1 - a_val * σ ^ 2))⁻¹ from rfl
      have hden_inv_sq : (2 * σ * (1 - a_val * σ ^ 2))⁻¹ ^ 2 *
          (2 * σ * (1 - a_val * σ ^ 2)) ^ 2 = 1 := by
        rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 h_denom_ne)]
      rw [hden, mul_pow]
      -- goal: x'^2 * den⁻¹^2 * W_dec = 1
      -- rearrange to den⁻¹^2 * (x'^2 * W_dec) = 1
      rw [show x' ^ 2 * (2 * σ * (1 - a_val * σ ^ 2))⁻¹ ^ 2 * W_dec =
          (2 * σ * (1 - a_val * σ ^ 2))⁻¹ ^ 2 * (x' ^ 2 * W_dec) from by ring]
      rw [h_xsq_W, hden_inv_sq]
    -- hx: abs_edwards x' = abs_edwards(2*σ*(I*u2))
    have hx_eq : abs_edwards x' =
        abs_edwards (2 * σ * (I_dec * (1 - a_val * σ ^ 2))) := by
      apply abs_edwards_eq_of_sq_eq
      apply mul_right_cancel₀ h_v_ne
      have : (2 * σ * (I_dec * (1 - a_val * σ ^ 2))) ^ 2 * v_dec =
          4 * σ ^ 2 * (I_dec ^ 2 * W_dec) := by ring
      rw [this, h_I_W, mul_one, h_xsq_v]
    -- hy: y_f = u1 * (I*(I*u2)*v)
    have hy_eq : y_f = (1 + a_val * σ ^ 2) *
        (I_dec * (I_dec * (1 - a_val * σ ^ 2)) * v_dec) := by
      apply mul_right_cancel₀ h_u2_dec_ne
      rw [h_yf_u2]
      have : (1 + a_val * σ ^ 2) * (I_dec * (I_dec * (1 - a_val * σ ^ 2)) * v_dec) *
          (1 - a_val * σ ^ 2) =
          (1 + a_val * σ ^ 2) * (I_dec ^ 2 * W_dec) := by ring
      rw [this, h_I_W, mul_one]
    -- is_negative check: abs_edwards(x') * y_f = x' * y' in both sign cases
    have h_neg_ok : is_negative (abs_edwards x' * y_f) = false := by
      have h_t_eq : abs_edwards x' * y_f = x' * compress_y_prime P := by
        simp only [hyf_def, hx'_def]; unfold compress_y_final abs_edwards
        simp only [h_z_inv_one, mul_one]; split_ifs <;> ring
      rw [h_t_eq]
      by_cases h_rot : compress_rotate P
      · -- Rotate: x'*y' = -(P.x*P.y) → is_negative = false (since is_negative(xy)=true)
        have h_t : x' * compress_y_prime P = -(P.x * P.y * compress_z_inv P) := by
          simp only [hx'_def]; unfold compress_x_prime compress_y_prime
          rw [if_pos h_rot, if_pos h_rot, h_z_inv_one]
          rw [show P.y * sqrt_m1 * (P.x * sqrt_m1) = P.x * P.y * sqrt_m1 ^ 2 from by ring,
              sqrt_m1_sq]; ring
        rw [h_t]
        have h_neg_pos : is_negative (P.x * P.y * compress_z_inv P) = true := by
          unfold compress_rotate at h_rot; exact h_rot
        have h_xy_ne : P.x * P.y * compress_z_inv P ≠ 0 := by
          rw [h_z_inv_one, mul_one]; exact mul_ne_zero h_px_ne h_py_ne
        unfold is_negative at h_neg_pos ⊢
        rw [ZMod.neg_val, if_neg h_xy_ne]
        have := ZMod.val_lt (P.x * P.y * compress_z_inv P)
        simp only [beq_iff_eq] at h_neg_pos ⊢; simp only [beq_eq_false_iff_ne, ne_eq,
          Nat.mod_two_not_eq_one]
        have hp_odd : p % 2 = 1 := by unfold p; norm_num
        omega
      · -- No-rotate: x'*y' = P.x*P.y → is_negative = false (since rotate=false)
        have h_rot_false : compress_rotate P = false := by
          revert h_rot; cases compress_rotate P <;> simp
        have h_t : x' * compress_y_prime P = P.x * P.y * compress_z_inv P := by
          simp only [hx'_def]; unfold compress_x_prime compress_y_prime
          rw [if_neg (by rw [h_rot_false]; decide), if_neg (by rw [h_rot_false]; decide),
              h_z_inv_one, mul_one]
        rw [h_t]
        have : is_negative (P.x * P.y * compress_z_inv P) = false := by
          unfold compress_rotate at h_rot
          revert h_rot; cases is_negative (P.x * P.y * compress_z_inv P) <;> simp
        exact this
    -- On-curve proof for the canonical point
    have h_on_curve : Ed25519.a * (abs_edwards x') ^ 2 + y_f ^ 2 =
        1 + Ed25519.d * (abs_edwards x') ^ 2 * y_f ^ 2 := by
      rw [abs_edwards_sq]; change a_val * x' ^ 2 + y_f ^ 2 = 1 + ↑d * x' ^ 2 * y_f ^ 2
      rw [h_xprime_sq, h_yfinal_sq]; dsimp only [a_val]; split_ifs <;> linear_combination h_curve
    let pt_can : Point Ed25519 := ⟨abs_edwards x', y_f, h_on_curve⟩
    exact ⟨pt_can, decompress_step2_2 σ pt_can I_dec h_I_W h_neg_ok h_yf_ne hx_eq hy_eq⟩

noncomputable def decompress_pure (c : CompressedRistretto) : Option (Point Ed25519) :=
  (decompress_step1 c).bind decompress_step2

/--
A CompressedRistretto is valid if and only if the pure mathematical decompression
succeeds (returning `some`). This implicitly checks (via decompress_pure):
1. bytes < p
2. sign bit = 0
3. isogeny square root exists
4. t >= 0
5. y != 0
-/
def CompressedRistretto.IsValid (c : CompressedRistretto) : Prop :=
  ∃ (pt : Point Ed25519),
    decompress_pure c = some pt

/--
If valid, return the decompressed point.
If invalid, return the neutral element (0).
-/
noncomputable def CompressedRistretto.toPoint (c : CompressedRistretto) : Point Ed25519 :=
  match decompress_pure c with
  | some P => P
  | none   => 0  -- Returns neutral element on failure

end curve25519_dalek.ristretto

namespace curve25519_dalek.math

open Edwards ZMod ristretto

section ElligatorMap

/-! ### Elligator Step Functions

Step-by-step decomposition of the Elligator Ristretto map.
Each step corresponds to a block of the Rust implementation
(`ristretto.rs` L676–727) and can be individually unfolded
without the RAM blowup caused by nested `let`-inlining.
-/

/-- r = SQRT_M1 * r₀² (Rust L685–686) -/
def elligator_r (r0 : ZMod p) : ZMod p :=
  sqrt_m1 * r0 ^ 2

/-- N_s = (r + 1) * (1 - d²) (Rust L687–688) -/
def elligator_Ns (r0 : ZMod p) : ZMod p :=
  (elligator_r r0 + 1) * (1 - d ^ 2)

/-- D = -(1 + d · r) * (r + d) (Rust L689–692) -/
def elligator_D (r0 : ZMod p) : ZMod p :=
  -(1 + d * elligator_r r0) * (elligator_r r0 + d)

/-- ratio = N_s / D (argument to `sqrt_ratio_i`, Rust L694) -/
def elligator_ratio (r0 : ZMod p) : ZMod p :=
  elligator_Ns r0 * (elligator_D r0)⁻¹

/-- Squareness predicate matching `sqrt_ratio_i` semantics:
    ∃ x, x² · D = N_s.  Agrees with `IsSquare (N_s/D)` when D ≠ 0,
    but correctly returns False when D = 0 and N_s ≠ 0. -/
def elligator_is_square (r0 : ZMod p) : Prop :=
  ∃ x : ZMod p, x ^ 2 * elligator_D r0 = elligator_Ns r0

instance instDecidableElligatorIsSquare (r0 : ZMod p) :
    Decidable (elligator_is_square r0) :=
  show Decidable (∃ x : ZMod p, x ^ 2 * elligator_D r0 = elligator_Ns r0) from inferInstance

/-- s after conditional selection (Rust L694–701):
    Square case:     s = abs_edwards(sqrt(ratio))
    Non-square case: s = -(abs_edwards(sqrt(i · ratio) · r₀)) -/
noncomputable def elligator_s (r0 : ZMod p) : ZMod p :=
  if elligator_is_square r0 then
    abs_edwards (sqrt (elligator_ratio r0))
  else
    -(abs_edwards ((sqrt (sqrt_m1 * elligator_ratio r0)) * r0))

/-- c after conditional selection (Rust L681, L700–702):
    Square case:     c = −1
    Non-square case: c = r -/
def elligator_c (r0 : ZMod p) : ZMod p :=
  if elligator_is_square r0 then -(1 : ZMod p)
  else elligator_r r0

/-- N_t = c · (r − 1) · (d − 1)² − D (Rust L704–707) -/
noncomputable def elligator_Nt (r0 : ZMod p) : ZMod p :=
  elligator_c r0 * (elligator_r r0 - 1) * (d - 1) ^ 2 - elligator_D r0

/-- x-coordinate of Elligator output: 2sD / (N_t · sqrt_ad_minus_one) (Rust L712–714) -/
noncomputable def elligator_ristretto_flavor_x (r0 : ZMod p) : ZMod p :=
  (2 * elligator_s r0 * elligator_D r0) / (elligator_Nt r0 * sqrt_ad_minus_one)

/-- y-coordinate of Elligator output: (1 − s²) / (1 + s²) (Rust L715–716) -/
noncomputable def elligator_ristretto_flavor_y (r0 : ZMod p) : ZMod p :=
  (1 - elligator_s r0 ^ 2) / (1 + elligator_s r0 ^ 2)

/--
**Elligator Ristretto Map (Pure Spec)**
Maps a field element `r0` to an Affine Point on the Ed25519 curve.
Comes with a proof that the output point is even (i.e., in the image of the doubling map).
Logic corresponds to [RFC 9496 Section 4.3.4].

Defined via step functions (`elligator_r`, `elligator_s`, …) to avoid
RAM blowup from nested `let`-inlining during unfold/delta.
Use `elligator_pure_val_x` / `elligator_pure_val_y` to project coordinates.
-/
noncomputable def elligator_ristretto_flavor_pure (r0 : ZMod p)
    : {P : Point Ed25519 // IsEven P} :=
  ⟨{ x := elligator_ristretto_flavor_x r0
     y := elligator_ristretto_flavor_y r0
     on_curve := by sorry },
    by
    unfold IsEven
    unfold elligator_ristretto_flavor_y
    by_cases hdenom : (1 : ZMod p) + elligator_s r0 ^ 2 = 0
    · have hzero : (1 - elligator_s r0 ^ 2) / (1 + elligator_s r0 ^ 2) = 0 := by
        rw [hdenom]; exact div_zero _
      rw [hzero]
      exact ⟨1, by ring⟩
    · exact ⟨2 * elligator_s r0 / (1 + elligator_s r0 ^ 2),
        by field_simp [hdenom]; ring⟩⟩

/-- Projection: x-coordinate of the pure spec equals the step function. -/
@[simp]
lemma elligator_pure_val_x (r0 : ZMod p) :
    (elligator_ristretto_flavor_pure r0).val.x =
      elligator_ristretto_flavor_x r0 := rfl

/-- Projection: y-coordinate of the pure spec equals the step function. -/
@[simp]
lemma elligator_pure_val_y (r0 : ZMod p) :
    (elligator_ristretto_flavor_pure r0).val.y =
      elligator_ristretto_flavor_y r0 := rfl

end ElligatorMap

end curve25519_dalek.math

/-!
## Canonical Representation
-/

namespace Edwards

open curve25519_dalek.math

/--
**Canonical Ristretto Representation**
A Point P is the canonical representative of its Ristretto coset if
decompress ∘ compress = Id on the point.
The predicate 'IsCanonicalRistrettoRep' characterizes exactly the set of points fixed by the Ristretto
compression-decompression cycle, i.e. `IsCanonicalRistrettoRep P ↔ decompress (compress P) = P`.

**Proof Sketch:**

1. **Necessity (Image of Decompression):** (Resources: (RFC 9496 §4.3.1 or https://ristretto.group/ §5.2)
   For any valid encoding `s`, the `decompress` function constructs a point `P`
   enforcing these specific invariants:
   - `x`: computed as `abs(2s * Dx)`, forcing `is_negative x = false`.
   - `t`: computed as `x * y`; decoding fails if `is_negative t`, forcing `is_negative t = false`.
   - `y`: decoding fails if `y = 0`.
   Thus, the image of decompression is strictly contained in this set.

2. **Sufficiency (Fundamental Domain of Compression):** (Resources: https://ristretto.group/ §5.3)
   The `compress` function projects a coset of size 8 to a single representative by conditionally
   applying geometric transformations:
   - **Torque:** Maps `P → P + Q₄` if `is_negative (x * y)`.
   - **Involution:** Maps `P → -P` if `is_negative x`.
   If `IsCanonicalRistrettoRep P` holds, both conditions are false. The compression logic
   skips these transformations, acting purely as the inverse of the isogeny map restricted
   to this domain. Therefore, `decompress (compress P) = P`.

**Geometric Interpretation:**
This predicate defines a section (fundamental domain) of the quotient bundle `E → E/E[8]`:
- `is_negative (x * y) = false`: Selects the unique coset representative modulo `E[4]` (fixes Torque).
- `is_negative x = false`: Selects the unique representative modulo the remaining involution (fixes Sign).
- `y ≠ 0`: Excludes singular points where the map is undefined.
-/
def IsCanonicalRistrettoRep (P : Point Ed25519) : Prop :=
  let x := P.x
  let y := P.y
  let t := x * y
  -- 1. x must be even (non-negative)
  (is_negative x = false) ∧
  -- 2. t must be even (non-negative)
  (is_negative t = false) ∧
  -- 3. y must be non-zero
  (y ≠ 0)

end Edwards
