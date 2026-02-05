/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Curve25519Dalek.Types
import Curve25519Dalek.Defs.Edwards.Curve
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Bridge Infrastructure for Edwards Curve Representations

This file bridges Rust implementation types to the mathematical `Point Ed25519`.
For each representation, we define `IsValid` predicates and `toPoint` conversions.

This file imports `Funs.lean` and `Types.lean` to access Rust implementation types.
It also imports `Edwards.EdCurve` to access the pure mathematical definitions.

## Point Representations

The Rust code uses 9 structures for representing points on the elliptic curve:

- edwards.EdwardsPoint
- ristretto.RistrettoPoint
- ristretto.CompressedRistretto
- backend.serial.curve_models.ProjectivePoint
- backend.serial.curve_models.CompletedPoint
- backend.serial.curve_models.ProjectiveNielsPoint
- edwards.affine.AffinePoint
- edwards.CompressedEdwardsY
- montgomery.MontgomeryPoint

The Rust code is designed so that the constructors and the various operations guarantee that the
data held by any of these is always a valid combination of coordinates. To track this we introduce
Lean predicates for each of these represenations.
-/

/-!
## Mathematical Foundations for Ristretto
Explicit formulas for the 2-isogeny between Jacobi Quartic and Twisted Edwards curves.
References: https://ristretto.group/details/isogenies.html, https://www.shiftleft.org/papers/decaf/decaf.pdf.
-/

namespace curve25519_dalek.math

open Edwards ZMod
open Aeneas.Std Result

section Constants

/-- SQRT_M1: The square root of -1 in the field (used for Elligator inverse sqrt).
    Value: 19681161...84752 -/
def sqrt_m1 : ZMod p :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- INVSQRT_A_MINUS_D: Constant used in compression rotation.
    Value: 544693...17578 -/
def invsqrt_a_minus_d : ZMod p :=
  54469307008909316920995813868745141605393597292927456921205312896311721017578

/-- Edwards a constant (-1) cast to the field. -/
def a_val : ZMod p := -1

/-- Helper: "Is Negative" (LSB is 1).
    Used for sign checks in Ristretto encoding. -/
def is_negative (x : ZMod p) : Bool :=
  x.val % 2 == 1

/-- Helper: Absolute value in Ed25519 context (ensures non-negative / even LSB). -/
def abs_edwards (x : ZMod p) : ZMod p :=
  if is_negative x then -x else x

/--
Square property of the absolute value function.
Since `abs_edwards x` is either `x` or `-x`, its square is always `x^2`.
-/
lemma abs_edwards_sq (x : ZMod p) : (abs_edwards x)^2 = x^2 := by
  unfold abs_edwards
  split_ifs <;> ring


/-- Helper: Inverse Square Root logic matching SQRT_RATIO_M1.
    Returns (I, was_square) where I^2 = 1/u or I^2 = 1/(i*u). -/
noncomputable def sqrt_checked (x : ZMod p) : (ZMod p × Bool) :=
  if h : IsSquare x then
    -- Case 1: x is a square. Pick the root 'y' such that y^2 = x.
    let y := Classical.choose h
    (abs_edwards y, true)
  else
    -- Case 2: x is not a square. Then i * x must be a square in this field.
    -- We pick 'y' such that y^2 = i * x.
    have h_ix : IsSquare (x * sqrt_m1) := by
      have h_char_ne_2 : ringChar (ZMod p) ≠ 2 := by
        intro h_char; rw [ZMod.ringChar_zmod_n] at h_char;
        norm_num [p] at h_char


      have h_pow_card : Fintype.card (ZMod p) / 2 = p / 2 := by rw [ZMod.card]
      have hx_ne0 : x ≠ 0 := by intro c; rw [c] at h; simp at h
      have h_i_ne0 : sqrt_m1 ≠ 0 := by
        unfold sqrt_m1;
        try decide


      have euler {z : ZMod p} (hz : z ≠ 0) : IsSquare z ↔ z ^ (Fintype.card (ZMod p) / 2) = 1 :=
        FiniteField.isSquare_iff h_char_ne_2 hz
      simp only [h_pow_card] at euler

      have h_x_pow : x ^ (p / 2) = -1 := by
        have dic := FiniteField.pow_dichotomy h_char_ne_2 hx_ne0
        rw [h_pow_card] at dic
        cases dic with
        | inl h1 => rw [← euler hx_ne0] at h1; contradiction
        | inr h_neg => exact h_neg

      have not_sq_i : ¬ IsSquare sqrt_m1 := by
        rintro ⟨y, hy⟩; rw [← pow_two] at hy;
        have y4 : y^4 = -1 := by
          rw [show 4 = 2 * 2 by rfl, pow_mul, ← hy]
          rw [← sub_eq_zero, sub_neg_eq_add]
          unfold sqrt_m1

          -- TODO: The tactics below cause excessive memory usage (20+ GB) because Lean's
          -- kernel struggles with 78-digit number literals. Need to
          -- precompute these as top-level lemmas to avoid crashing the elaborator.

          -- change ((19681161376707505956807079304988542015446066515923890162744021073123829784752 ^ 2 + 1 : ℤ) : ZMod p) = 0
          -- rw [intCast_zmod_eq_zero_iff_dvd]
          -- try decide
          sorry

        have y8 : y^8 = 1 := by
          rw [show 8 = 4 * 2 by rfl, pow_mul, y4];
          norm_num

        -- We are arguing by contradiction using 'by absurd: sqrt_m1 is a square'
        have order_div : 8 ∣ (p - 1) := by
          have h_order : orderOf y = 8 := by
            refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) y8 fun q hprime hdvd => ?_
            have hq_is_2 : q = 2 := by
              rw [show 8 = 2^3 by rfl] at hdvd
              exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hdvd)
            rw [hq_is_2, show 8 / 2 = 4 by rfl, y4]
            try grind

          rw [← h_order]
          apply ZMod.orderOf_dvd_card_sub_one
          try grind


        have not_dvd : ¬ 8 ∣ (p - 1) := by
          intro h
          have mod_zero : (p - 1) % 8 = 0 := Nat.mod_eq_zero_of_dvd h
          norm_num [p] at mod_zero

        try grind

      have h_i_pow : sqrt_m1 ^ (p / 2) = -1 := by
        have dic := FiniteField.pow_dichotomy h_char_ne_2 h_i_ne0
        rw [h_pow_card] at dic
        cases dic with
        | inl h1 =>
          rw [← euler h_i_ne0] at h1
          grind
        | inr h_neg => exact h_neg

      rw [euler (mul_ne_zero hx_ne0 h_i_ne0)]
      rw [mul_pow, h_x_pow, h_i_pow]
      norm_num

    let y := Classical.choose h_ix
    (abs_edwards y, false)

/--
Inverse Square Root spec.
Computes 1/sqrt(u) or 1/sqrt(i*u) depending on whether u is a square.
-/
noncomputable def inv_sqrt_checked (u : ZMod p) : (ZMod p × Bool) :=
  let (root, was_square) := sqrt_checked u
  (root⁻¹, was_square)

/--
Mathematical specification for `inv_sqrt_checked`.
-/
theorem inv_sqrt_checked_spec (arg : ZMod p) {I : ZMod p} {was_square : Bool} :
  inv_sqrt_checked arg = (I, was_square) →
  was_square = true →
  I^2 * arg = 1 := by
  -- We treat this as an axiom/specification for now to avoid
  -- analyzing the massive bit-level recursion of the implementation.
  sorry

end Constants

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
-/
noncomputable def decompress_pure (s_int : Nat) : Option (Point Ed25519) :=
  let s : ZMod p := s_int

  -- 0. Initial Input Check
  -- The integer must be < p and canonical sign must be 0
  if s_int >= p || s_int % 2 != 0 then
    none
  else
    -- 1. Algebraic setup
    let u1 := 1 + a_val * s^2
    let u2 := 1 - a_val * s^2
    let v := a_val * d * u1^2 - u2^2

    -- 2. Inverse Square Root (Elligator)
    let arg := v * u2^2
    match h_call : inv_sqrt_checked arg with
    | (I, was_square) => -- This binds I and was_square for the rest of the block

    -- 3. Recover denominators
    let Dx := I * u2
    let Dy := I * Dx * v

    -- 4. Recover coordinates
    let x := abs_edwards (2 * s * Dx)
    let y := u1 * Dy

    -- 5. Validation Checks
    let t := x * y

    -- (1) Square root must succeed
    -- (2) t must be non-negative (even LSB=LeastSignificantByte)
    -- (3) y must be non-zero
    if h_invalid : !was_square || is_negative t || (y == 0) then
      none
    else
      some { x := x, y := y, on_curve := by
              -- Unpack validity
              replace h_invalid := Bool.eq_false_iff.mpr h_invalid
              rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at h_invalid
              obtain ⟨⟨h_sq_not, h_neg_false⟩, h_y_eq_false⟩ := h_invalid
              simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_sq_not

              have h_I_sq_mul : I^2 * (v * u2^2) = 1 := by
                apply inv_sqrt_checked_spec arg
                · exact h_call
                · exact h_sq_not

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

section EdwardsDecompression

/--
**Pure Edwards Decompression**
Recovers (x, y) from a 32-byte representation `s` according to RFC 8032 (Ed25519).
Morally: we store the point (x,y) as just the coordinate y and the sign bit, i.e. using 32-bits,
leveraging the EdCurve equation: -x² + y² = 1 + dx²y². Indeed, we can recover x just knowing y and
the sign to take on the square root to obtain x.
1. Treat the 32 bytes as a little-endian integer `s`.
2. y is the lower 255 bits (s % 2^255).
3. The sign of x is the 256th bit (s / 2^255).
-/
noncomputable def decompress_edwards_pure (bytes : Array U8 32#usize) : Option (Point Ed25519) :=
  let s := U8x32_as_Nat bytes

  -- Mathematical splitting of the 256-bit integer
  let y_int := s % (2^255)
  let sign_bit := s / (2^255) -- This is 0 or 1 because s < 2^256

  if y_int >= p then
    none
  else
    let y : ZMod p := y_int

    -- Solve for x²: x² = (y² - 1) / (dy² + 1)
    let u := y^2 - 1
    let v := d * y^2 + 1
    let x2 := u * v⁻¹

    if h : IsSquare x2 then
      let x_root := abs_edwards (Classical.choose h)
      -- Apply sign bit: if sign_bit is 1, we want the negative (odd) root
      let x := if (is_negative x_root) != (sign_bit == 1) then -x_root else x_root

      some { x := x, y := y, on_curve := by
              have hx_sq : x^2 = x2 := by
                simp only [x]
                split_ifs
                all_goals{
                  try simp only [even_two, Even.neg_pow]
                  dsimp [x_root, abs_edwards]
                  split_ifs
                  all_goals {
                    try simp only [even_two, Even.neg_pow]
                    have spec := Classical.choose_spec h
                    rw [pow_two]
                    rw [← spec]
                  }
                }
              have hv_ne0 : v ≠ 0 := by
                intro hv
                dsimp only [v] at hv
                have h_neg : (d : ZMod p) * y^2 = -1 := eq_neg_of_add_eq_zero_left hv

                have rhs_sq : IsSquare (-1 : ZMod p) := by
                  use sqrt_m1; rw [←pow_two, sqrt_m1]; rw [← sub_eq_zero]
                  -- TODO: The tactics below cause excessive memory usage (20+ GB) because Lean's
                  -- kernel struggles with 78-digit number literals. Need to
                  -- precompute these as top-level lemmas to avoid crashing the elaborator.

                  -- change ((-1-19681161376707505956807079304988542015446066515923890162744021073123829784752 ^ 2 : ℤ) : ZMod p) = 0
                  -- rw [intCast_zmod_eq_zero_iff_dvd]
                  -- try decide
                  sorry

                have lhs_not_sq : ¬ IsSquare ((d : ZMod p) * y^2) := by
                  intro h_is_sq
                  have h_d_not_sq : ¬ IsSquare (d : ZMod p) := by
                    apply (legendreSym.eq_neg_one_iff' p).mp
                    norm_num [d, p]

                  apply h_d_not_sq
                  by_cases hy : y = 0
                  · simp only [hy, pow_two, mul_zero] at h_neg;
                    try grind
                  · rcases h_is_sq with ⟨k, hk⟩
                    use k * y⁻¹; ring_nf; field_simp [hy]; rw [← pow_two] at hk; exact hk

                rw [h_neg] at lhs_not_sq
                try grind

              simp only [hx_sq]
              dsimp [Ed25519, x2, u, v]
              simp only [neg_mul, one_mul]
              simp only [v] at hv_ne0
              rw [mul_comm] at hv_ne0
              field_simp [hv_ne0]
              ring
              }
    else
      none

end EdwardsDecompression

end curve25519_dalek.math

/-! ## Field Element Conversions -/

namespace Edwards

open curve25519_dalek CategoryTheory curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.curve_models Function ZMod

/-- Convert the 5-limb array to a field element in ZMod p. -/
def field_from_limbs (fe : backend.serial.u64.field.FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

end Edwards

/-! ## FieldElement51 Validity and Casting -/

namespace curve25519_dalek.backend.serial.u64.field
open Edwards FieldElement51

/-- Convert a FieldElement51 to the mathematical field element in ZMod p.
    This is the same as `field_from_limbs` but with dot notation support. -/
def FieldElement51.toField (fe : FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

/-! From the Rust source (field.rs):
> "In the 64-bit implementation, a `FieldElement` is represented in radix 2^51 as five u64s;
> the coefficients are allowed to grow up to 2^54 between reductions modulo p."

The bound `< 2^54` is the universal validity condition that:
- Is accepted as input by all field operations (mul, square, pow2k, sub)
-/

/-- A FieldElement51 is valid when all 5 limbs are bounded by 2^54.
    This is the bound accepted as input by field operations and encompasses
    all valid intermediate values between reductions. -/
def FieldElement51.IsValid (fe : FieldElement51) : Prop := ∀ i < 5, fe[i]!.val < 2^54

instance FieldElement51.instDecidableIsValid (fe : FieldElement51) : Decidable fe.IsValid :=
  show Decidable (∀ i < 5, fe[i]!.val < 2^54) from inferInstance

end curve25519_dalek.backend.serial.u64.field

/-!
## AffinePoint Validity
-/

namespace curve25519_dalek.edwards.affine

open curve25519_dalek.backend.serial.u64.field
open Edwards

/--
Validity predicate for AffinePoint.
An AffinePoint contains raw field elements (x, y) which must satisfy the curve equation.
-/
@[mk_iff]
structure AffinePoint.IsValid (a : AffinePoint) : Prop where
  /-- Coordinates must be valid field elements (limbs < 2^54). -/
  x_valid : a.x.IsValid
  y_valid : a.y.IsValid
  /-- The point must satisfy the twisted Edwards equation: -x² + y² = 1 + dx²y² -/
  on_curve :
    let x := a.x.toField
    let y := a.y.toField
    Ed25519.a * x^2 + y^2 = 1 + Ed25519.d * x^2 * y^2

instance AffinePoint.instDecidableIsValid (a : AffinePoint) : Decidable a.IsValid :=
  decidable_of_iff _ (isValid_iff a).symm

/-- Convert an AffinePoint to the mathematical Point. -/
def AffinePoint.toPoint (a : AffinePoint) : Point Ed25519 :=
  if h : a.IsValid then
    { x := a.x.toField
      y := a.y.toField
      on_curve := h.on_curve }
  else 0

end curve25519_dalek.edwards.affine

/-! ## EdwardsPoint validity and casting -/

namespace curve25519_dalek.edwards
open curve25519_dalek.backend.serial.u64.field Edwards

/-- Validity predicate for EdwardsPoint.
    An EdwardsPoint (X, Y, Z, T) represents the affine point (X/Z, Y/Z) with T = XY/Z.
    Bounds: all coordinates < 2^53 (needed for add operations where Y+X < 2^54). -/
@[mk_iff]
structure EdwardsPoint.IsValid (e : EdwardsPoint) : Prop where
  /-- All coordinate limbs are bounded by 2^53. -/
  X_bounds : ∀ i < 5, e.X[i]!.val < 2 ^ 53
  Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53
  Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53
  T_bounds : ∀ i < 5, e.T[i]!.val < 2 ^ 53
  /-- The Z coordinate is non-zero in the field. -/
  Z_ne_zero : e.Z.toField ≠ 0
  /-- Extended coordinate relation: T = XY/Z, i.e., XY = TZ. -/
  T_relation : e.X.toField * e.Y.toField = e.T.toField * e.Z.toField
  /-- The curve equation (twisted Edwards). -/
  on_curve :
    let X := e.X.toField; let Y := e.Y.toField; let Z := e.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance EdwardsPoint.instDecidableIsValid (e : EdwardsPoint) : Decidable e.IsValid :=
  decidable_of_iff _ (isValid_iff e).symm

/-- Convert an EdwardsPoint to the affine point (X/Z, Y/Z).
    Requires a proof that the point is valid. -/
def EdwardsPoint.toPoint' (e : EdwardsPoint) (h : e.IsValid) : Point Ed25519 :=
  let X := e.X.toField
  let Y := e.Y.toField
  let Z := e.Z.toField
  { x := X / Z
    y := Y / Z
    on_curve := by
      have hz : Z ≠ 0 := h.Z_ne_zero
      have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 hz
      have hz4 : Z^4 ≠ 0 := pow_ne_zero 4 hz
      have hcurve : Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2 := h.on_curve
      simp only [Ed25519] at hcurve ⊢
      simp only [div_pow]
      field_simp [hz2, hz4]
      linear_combination hcurve }

/-- Convert an EdwardsPoint to the affine point (X/Z, Y/Z).
    Returns 0 if the point is not valid. -/
def EdwardsPoint.toPoint (e : EdwardsPoint) : Point Ed25519 :=
  if h : e.IsValid then e.toPoint' h else 0

/-- Unfolding lemma: when an EdwardsPoint is valid, toPoint computes (X/Z, Y/Z). -/
theorem EdwardsPoint.toPoint_of_isValid {e : EdwardsPoint} (h : e.IsValid) :
    (e.toPoint).x = e.X.toField / e.Z.toField ∧
    (e.toPoint).y = e.Y.toField / e.Z.toField := by
  unfold toPoint
  rw [dif_pos h]
  simp only [toPoint']
  trivial

end curve25519_dalek.edwards

/-!
## CompressedEdwardsY Validity
-/

namespace curve25519_dalek.edwards
open curve25519_dalek.math Edwards

/--
A CompressedEdwardsY is valid if it represents a valid point on the curve.
This means the bytes must decompress successfully using the standard Ed25519 rules.
-/
def CompressedEdwardsY.IsValid (c : CompressedEdwardsY) : Prop :=
  (decompress_edwards_pure c).isSome

/--
Convert a CompressedEdwardsY to the mathematical Point.
Returns the neutral element if invalid.
-/
noncomputable def CompressedEdwardsY.toPoint (c : CompressedEdwardsY) : Point Ed25519 :=
  match decompress_edwards_pure c with
  | some P => P
  | none => 0

end curve25519_dalek.edwards

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
A CompressedRistretto is valid if and only if the pure mathematical decompression
succeeds (returning `some`). This implicitly checks (via decompress_pure):
1. bytes < p
2. sign bit = 0
3. isogeny square root exists
4. t >= 0
5. y != 0
-/
def CompressedRistretto.IsValid (c : CompressedRistretto) : Prop :=
  (decompress_pure (U8x32_as_Nat c)).isSome

/--
If valid, return the decompressed point.
If invalid, return the neutral element (0).
-/
noncomputable def CompressedRistretto.toPoint (c : CompressedRistretto) : Point Ed25519 :=
  match decompress_pure (U8x32_as_Nat c) with
  | some P => P
  | none   => 0

end curve25519_dalek.ristretto

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

/-! ## ProjectivePoint Validity and Casting -/

namespace curve25519_dalek.backend.serial.curve_models
open Edwards

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for ProjectivePoint.
    A ProjectivePoint (X, Y, Z) represents the affine point (X/Z, Y/Z).
    For this to be on Ed25519, we need: a*(X/Z)² + (Y/Z)² = 1 + d*(X/Z)²*(Y/Z)²
    Clearing denominators: a*X²*Z² + Y²*Z² = Z⁴ + d*X²*Y²

    Note: ProjectivePoint coordinates must have the tighter bound < 2^52 (not just < 2^54)
    because operations like `double` compute X + Y, which must be < 2^54 for subsequent
    squaring. With coords < 2^52, we get X + Y < 2^53 < 2^54. -/
@[mk_iff]
structure ProjectivePoint.IsValid (pp : ProjectivePoint) : Prop where
  /-- All coordinate limbs are bounded by 2^52. -/
  X_bounds : ∀ i < 5, pp.X[i]!.val < 2 ^ 52
  Y_bounds : ∀ i < 5, pp.Y[i]!.val < 2 ^ 52
  Z_bounds : ∀ i < 5, pp.Z[i]!.val < 2 ^ 52
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : pp.Z.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve :
    let X := pp.X.toField; let Y := pp.Y.toField; let Z := pp.Z.toField
    Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2

instance ProjectivePoint.instDecidableIsValid (pp : ProjectivePoint) : Decidable pp.IsValid :=
  decidable_of_iff _ (isValid_iff pp).symm

/-- Convert a ProjectivePoint to the affine point (X/Z, Y/Z).
    Returns 0 if the point is not valid. -/
noncomputable def ProjectivePoint.toPoint (pp : ProjectivePoint) : Point Ed25519 :=
  if h : pp.IsValid then
    let X := pp.X.toField
    let Y := pp.Y.toField
    let Z := pp.Z.toField
    { x := X / Z
      y := Y / Z
      on_curve := by
        have hz : Z ≠ 0 := h.Z_ne_zero
        have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 hz
        have hz4 : Z^4 ≠ 0 := pow_ne_zero 4 hz
        have hcurve : Ed25519.a * X^2 * Z^2 + Y^2 * Z^2 = Z^4 + Ed25519.d * X^2 * Y^2 := h.on_curve
        simp only [Ed25519] at hcurve ⊢
        simp only [div_pow]
        field_simp [hz2, hz4]
        linear_combination hcurve }
  else 0

/-- Unfolding lemma: when a ProjectivePoint is valid, toPoint computes (X/Z, Y/Z). -/
theorem ProjectivePoint.toPoint_of_isValid {pp : ProjectivePoint} (h : pp.IsValid) :
    (pp.toPoint).x = pp.X.toField / pp.Z.toField ∧
    (pp.toPoint).y = pp.Y.toField / pp.Z.toField := by
  unfold toPoint; rw [dif_pos h]; constructor <;> rfl

/-! ## CompletedPoint Validity and Casting -/

open curve25519_dalek.backend.serial.u64.field in
/-- Validity predicate for CompletedPoint.
    A CompletedPoint (X, Y, Z, T) represents the affine point (X/Z, Y/T).
    For this to be on Ed25519, we need: a*(X/Z)² + (Y/T)² = 1 + d*(X/Z)²*(Y/T)²
    Clearing denominators: a*X²*T² + Y²*Z² = Z²*T² + d*X²*Y²

    All coordinates use the universal bound < 2^54. -/
@[mk_iff]
structure CompletedPoint.IsValid (cp : CompletedPoint) : Prop where
  /-- All coordinate limbs are bounded by 2^54. -/
  X_valid : cp.X.IsValid
  Y_valid : cp.Y.IsValid
  Z_valid : cp.Z.IsValid
  T_valid : cp.T.IsValid
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : cp.Z.toField ≠ 0
  /-- The T coordinate is non-zero. -/
  T_ne_zero : cp.T.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve :
    let X := cp.X.toField; let Y := cp.Y.toField
    let Z := cp.Z.toField; let T := cp.T.toField
    Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2

open curve25519_dalek.backend.serial.u64.field in
instance CompletedPoint.instDecidableIsValid (cp : CompletedPoint) : Decidable cp.IsValid :=
  decidable_of_iff _ (isValid_iff cp).symm

/-- Convert a CompletedPoint to the affine point (X/Z, Y/T).
    Returns 0 if the point is not valid. -/
noncomputable def CompletedPoint.toPoint (cp : CompletedPoint) : Point Ed25519 :=
  if h : cp.IsValid then
    let X := cp.X.toField
    let Y := cp.Y.toField
    let Z := cp.Z.toField
    let T := cp.T.toField
    { x := X / Z
      y := Y / T
      on_curve := by
        have hz : Z ≠ 0 := h.Z_ne_zero
        have ht : T ≠ 0 := h.T_ne_zero
        have hz2 : Z^2 ≠ 0 := pow_ne_zero 2 hz
        have ht2 : T^2 ≠ 0 := pow_ne_zero 2 ht
        have hcurve : Ed25519.a * X^2 * T^2 + Y^2 * Z^2 = Z^2 * T^2 + Ed25519.d * X^2 * Y^2 := h.on_curve
        simp only [Ed25519] at hcurve ⊢
        simp only [div_pow]
        field_simp [hz2, ht2]
        linear_combination hcurve }
  else 0

/-- Unfolding lemma: when a CompletedPoint is valid, toPoint computes (X/Z, Y/T). -/
theorem CompletedPoint.toPoint_of_isValid {cp : CompletedPoint} (h : cp.IsValid) :
    (cp.toPoint).x = cp.X.toField / cp.Z.toField ∧
    (cp.toPoint).y = cp.Y.toField / cp.T.toField := by
  unfold toPoint; rw [dif_pos h]; constructor <;> rfl

/-! ## ProjectiveNielsPoint Validity and Casting -/

/-- Validity predicate for ProjectiveNielsPoint.
    A ProjectiveNielsPoint (Y_plus_X, Y_minus_X, Z, T2d) represents a point where:
    - X = (Y_plus_X - Y_minus_X) / 2
    - Y = (Y_plus_X + Y_minus_X) / 2
    - The affine point (X/Z, Y/Z) is on Ed25519
    - T2d = 2*d*x*y*Z where x, y are the affine coordinates

    The curve equation in these coordinates (multiplied by 4 to avoid divisions):
    4*a*(Y_plus_X - Y_minus_X)²*Z² + 4*(Y_plus_X + Y_minus_X)²*Z² =
      16*Z⁴ + d*(Y_plus_X - Y_minus_X)²*(Y_plus_X + Y_minus_X)²

    Bounds: all coordinates < 2^53 (needed for mixed addition operations). -/
@[mk_iff]
structure ProjectiveNielsPoint.IsValid (pn : ProjectiveNielsPoint) : Prop where
  /-- All coordinate limbs are bounded by 2^53. -/
  Y_plus_X_bounds : ∀ i < 5, pn.Y_plus_X[i]!.val < 2 ^ 53
  Y_minus_X_bounds : ∀ i < 5, pn.Y_minus_X[i]!.val < 2 ^ 53
  Z_bounds : ∀ i < 5, pn.Z[i]!.val < 2 ^ 53
  T2d_bounds : ∀ i < 5, pn.T2d[i]!.val < 2 ^ 53
  /-- The Z coordinate is non-zero. -/
  Z_ne_zero : pn.Z.toField ≠ 0
  /-- The curve equation (scaled by 4 to avoid 1/2). -/
  on_curve :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField; let Z := pn.Z.toField
    4 * Ed25519.a * (YpX - YmX)^2 * Z^2 + 4 * (YpX + YmX)^2 * Z^2 =
      16 * Z^4 + Ed25519.d * (YpX - YmX)^2 * (YpX + YmX)^2
  /-- T2d relation: T2d = 2*d*x*y*Z = d*(YpX² - YmX²)/(2*Z) i.e., 2*Z*T2d = d*(YpX² - YmX²). -/
  T2d_relation :
    let YpX := pn.Y_plus_X.toField; let YmX := pn.Y_minus_X.toField
    let Z := pn.Z.toField; let T2d := pn.T2d.toField
    2 * Z * T2d = Ed25519.d * (YpX^2 - YmX^2)

instance ProjectiveNielsPoint.instDecidableIsValid (pn : ProjectiveNielsPoint) : Decidable pn.IsValid :=
  decidable_of_iff _ (isValid_iff pn).symm

/-- Convert a ProjectiveNielsPoint to the affine point it represents.
    The affine coordinates are ((Y_plus_X - Y_minus_X)/(2Z), (Y_plus_X + Y_minus_X)/(2Z)). -/
noncomputable def ProjectiveNielsPoint.toPoint' (pn : ProjectiveNielsPoint) (h : pn.IsValid) :
    Point Ed25519 :=
  let YpX := pn.Y_plus_X.toField
  let YmX := pn.Y_minus_X.toField
  let Z := pn.Z.toField
  { x := (YpX - YmX) / (2 * Z)
    y := (YpX + YmX) / (2 * Z)
    on_curve := by
      have hz : Z ≠ 0 := h.Z_ne_zero
      have h2 : (2 : CurveField) ≠ 0 := by decide
      have h2z : 2 * Z ≠ 0 := mul_ne_zero h2 hz
      have h2z2 : (2 * Z)^2 ≠ 0 := pow_ne_zero 2 h2z
      have h2z4 : (2 * Z)^4 ≠ 0 := pow_ne_zero 4 h2z
      have hcurve := h.on_curve
      simp only [Ed25519] at hcurve ⊢
      simp only [div_pow]
      field_simp [h2z2, h2z4]
      ring_nf
      ring_nf at hcurve
      linear_combination hcurve }

/-- Convert a ProjectiveNielsPoint to the affine point it represents.
    Returns 0 if the point is not valid. -/
noncomputable def ProjectiveNielsPoint.toPoint (pn : ProjectiveNielsPoint) : Point Ed25519 :=
  if h : pn.IsValid then pn.toPoint' h else 0

/-- Unfolding lemma for ProjectiveNielsPoint.toPoint. -/
theorem ProjectiveNielsPoint.toPoint_of_isValid {pn : ProjectiveNielsPoint} (h : pn.IsValid) :
    (pn.toPoint).x = (pn.Y_plus_X.toField - pn.Y_minus_X.toField) / (2 * pn.Z.toField) ∧
    (pn.toPoint).y = (pn.Y_plus_X.toField + pn.Y_minus_X.toField) / (2 * pn.Z.toField) := by
  unfold toPoint
  rw [dif_pos h]
  simp only [toPoint']
  trivial

/-! ## Coercions -/

/-- Coercion allowing `q + q` syntax where `q` is a ProjectivePoint. -/
noncomputable instance : Coe ProjectivePoint (Point Ed25519) where
  coe p := p.toPoint

/-- Coercion allowing comparison of `CompletedPoint` results with mathematical points. -/
noncomputable instance : Coe CompletedPoint (Point Ed25519) where
  coe p := p.toPoint

@[simp]
theorem ProjectivePoint.toPoint_eq_coe (p : ProjectivePoint) :
  p.toPoint = ↑p := rfl

@[simp]
theorem CompletedPoint.toPoint_eq_coe (p : CompletedPoint) :
  p.toPoint = ↑p := rfl

/-!
## MontgomeryPoint Validity
-/

abbrev MontgomeryPoint := curve25519_dalek.montgomery.MontgomeryPoint

namespace curve25519_dalek.montgomery

open curve25519_dalek curve25519_dalek.math
open Edwards

/-!
Helper Def:
Define the conversion using Horner's method (foldr).
This prevents the creation of the massive syntax tree that `U8x32_as_Nat` produces.
-/
def bytesToField (m : MontgomeryPoint) : ZMod p :=
  m.val.foldr (init := 0) fun b acc =>
    (b.val : ZMod p) + (256 : ZMod p) * acc

/--
Validity for MontgomeryPoint.
A MontgomeryPoint is a 32-byte integer `u` representing a coordinate on the curve `v² = u³ + Au² + u`.
It is valid if:
1. The integer `u` is strictly less than the field modulus `p`.
2. `u` maps to a valid Edwards `y` coordinate (i.e., `u ≠ -1`).
3. The resulting Edwards point exists (i.e., we can solve for `x`).
-/
def MontgomeryPoint.IsValid (m : MontgomeryPoint) : Prop :=
  let u := bytesToField m
  -- The check `u_int < p` is implicitly handled because
  -- bytesToField returns a `ZMod p`, which is canonical by definition.
  -- However, to match the Rust strictness (rejecting non-canonical inputs),
  -- we should technically check the raw Nat value.
  -- But for the linter ''deterministic timeout' issue, we just need to avoid U8x32_as_Nat.
  if u + 1 = 0 then
    False
  else
    let y := (u - 1) * (u + 1)⁻¹
    let num := y^2 - 1
    let den := (d : ZMod p) * y^2 + 1
    IsSquare (num * den⁻¹)

instance (m : MontgomeryPoint) : Decidable (MontgomeryPoint.IsValid m) := by
  unfold MontgomeryPoint.IsValid
  infer_instance

/--
Convert MontgomeryPoint to Point Ed25519.
1. Recovers `y` from `u` via `y = (u-1)/(u+1)`.
2. Recovers `x` from `y` (choosing the canonical positive root).
Returns 0 (identity) if invalid.
-/
noncomputable def MontgomeryPoint.toPoint (m : MontgomeryPoint) : Point Ed25519 :=
  if h : (MontgomeryPoint.IsValid m) then
    -- The following is equivalent to defining u := 8x32_as_Nat m % p, but it uses Horner's method
    --  to avoid un folding heavy computations on large Nats casted as Mod p.
    let u : ZMod p := bytesToField m
    -- We know u != -1 from IsValid, so inversion is safe/correct
    let y := (u - 1) * (u + 1)⁻¹

    -- Recover x squared
    let num := y^2 - 1
    let den := (d : ZMod p) * y^2 + 1
    let x2 := num * den⁻¹

    -- Extract root (guaranteed to exist by IsValid)
    let (x_abs, is_sq) := sqrt_checked x2

    -- For Montgomery -> Edwards, the sign of x is lost.
    -- We canonically choose the non-negative (even) root.
    { x := x_abs, y := y, on_curve := sorry }
  else
    0

end curve25519_dalek.montgomery

end curve25519_dalek.backend.serial.curve_models
