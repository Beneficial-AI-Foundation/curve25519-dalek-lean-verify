/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
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

/--
**Pure Mathematical Compression**
Encodes a Point P into a scalar s (https://ristretto.group/formulas/encoding.html).
Used to define the Canonical property.
-/
noncomputable def compress_pure (P : Point Ed25519) : Nat :=
  let x := P.x
  let y := P.y
  let z := (1 : ZMod p)
  let t := x * y
  -- 1. Setup
  let u1 := (z + y) * (z - y)
  let u2 := x * y
  -- 2. Inverse Sqrt
  let (invsqrt, _was_square) := inv_sqrt_checked (u1 * u2^2)
  let den1 := invsqrt * u1
  let den2 := invsqrt * u2
  let z_inv := den1 * den2 * t
  -- 3. Rotation Decision
  let rotate := is_negative (t * z_inv)
  -- 4. Apply Rotation
  let x_prime := if rotate then y * sqrt_m1 else x
  let y_prime := if rotate then x * sqrt_m1 else y
  let den_inv := if rotate then den1 * invsqrt_a_minus_d else den2
  -- 5. Sign Adjustment
  let y_final := if is_negative (x_prime * z_inv) then -y_prime else y_prime
  -- 6. Final Calculation
  let s := abs_edwards (den_inv * (z - y_final))
  s.val

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
  have h_I_ne : I ≠ 0 := by intro h; simp [h] at hI
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
  have abs_edwards_neg : ∀ (x : ZMod p), abs_edwards (-x) = abs_edwards x := by
    intro x; by_cases hx : x = 0
    · simp [hx]
    · unfold abs_edwards is_negative
      have h_neg_val : (-x : ZMod p).val = p - x.val := by
        rw [ZMod.neg_val]; exact if_neg hx
      rw [h_neg_val]
      have hxlt : x.val < p := x.val_lt
      have hxv : x.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
      have hxpos : 0 < x.val := Nat.pos_of_ne_zero hxv
      have hp_odd : p % 2 = 1 := by decide
      have h_par : (p - x.val) % 2 ≠ x.val % 2 := by omega
      by_cases hpx : x.val % 2 = 1
      · have : (p - x.val) % 2 = 0 := by omega
        simp only [beq_iff_eq] at *; simp [hpx, this]
      · have hpx0 : x.val % 2 = 0 := by omega
        have : (p - x.val) % 2 = 1 := by omega
        simp only [beq_iff_eq] at *; simp [hpx0, this]
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

/--
**Elligator Ristretto Map (Pure Spec)**
Maps a field element `r0` to an Affine Point on the Ed25519 curve.
Logic corresponds to [RFC 9496 Section 4.3.4].
-/
noncomputable def elligator_ristretto_flavor_pure (r0 : ZMod p) : Point Ed25519 :=
  -- 1. Constants
  let i := sqrt_m1
  let d_val := d
  let one := (1 : ZMod p)

  -- 2. Compute r = i * r0^2
  let r := i * r0^2

  -- 3. Compute Elligator numerator and denominator
  let N_s := (r + 1) * (1 - d_val^2)
  let D_initial := -(1 + d_val * r) * (r + d_val)

  -- 4. Check if N_s / D is a square
  let ratio := N_s * D_initial⁻¹
  let is_sq := IsSquare ratio

  -- 5. Selection Logic
  let (s, c, D_final) := if is_sq then
      (sqrt ratio, -one, D_initial)
    else
      let s_prime := (sqrt (i * ratio)) * r0
      (-abs_edwards s_prime, r, D_initial)

  -- 6. Compute N_t
  let N_t := c * (r - 1) * (d_val - 1)^2 - D_final

  -- 7. Construct Affine Coordinates directly
  --    We use the simplification:
  --    x = X_ext / Z_ext = (2sD) / (Nt * sqrt_ad_minus_one)
  --    y = Y_ext / Z_ext = (1 - s^2) / (1 + s^2)
  let s_sq := s^2
  {
    x := (2 * s * D_final) / (N_t * sqrt_ad_minus_one)
    y := (1 - s_sq) / (1 + s_sq)
    on_curve := by
       -- The proof that this point satisfies the curve equation
       -- is much easier in Affine coordinates.
       sorry
  }

/--
**Validity Theorem**
The Elligator map always produces a point that is "Even" (in the 2-torsion subgroup).
This is the key Ristretto property.
-/
theorem elligator_pure_is_even (r0 : ZMod p) :
  IsEven (elligator_ristretto_flavor_pure r0) := by
  sorry

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
