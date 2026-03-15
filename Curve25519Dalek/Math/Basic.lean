/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Types
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import PrimeCert.PrimeList

/-! # Common Definitions

Common definitions used across spec theorems: field constants, conversion functions,
field element bridge (FieldElement51), and field utility functions (sqrt, is_negative).
-/

open Aeneas.Std Result

/-! ## Constants -/

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/-- The group order L for Scalar52 arithmetic -/
def L : Nat := 2^252 + 27742317777372353535851937790883648493

/-- The Montgomery constant R = 2^260 used for Scalar52 Montgomery form conversions -/
def R : Nat := 2^260

/-- The cofactor of Curve25519 -/
def h : Nat := 8

/-- The constant d in the defining equation for the twisted Edwards curve: ax^2 + y^2 = 1 + dx^2y^2 -/
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The constant a in the defining equation for the twisted Edwards curve: ax^2 + y^2 = 1 + dx^2y^2 -/
def a : Int := -1

/-! ## Auxiliary definitions for interpreting arrays as natural numbers -/

/-- Interpret a Field51 (five u64 limbs used to represent 51 bits each) as a natural number -/
def Field51_as_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).val

/-- Interpret a Scalar52 (five u64 limbs used to represent 52 bits each) as a natural number -/
def Scalar52_as_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(52 * i) * (limbs[i]!).val

/-- Interpret a 9-element u128 array (each limb representing 52 bits) as a natural number -/
def Scalar52_wide_as_Nat (limbs : Array U128 9#usize) : Nat :=
  ∑ i ∈ Finset.range 9, 2^(52 * i) * (limbs[i]!).val

/-- Interpret a 32-element byte array as a natural number. -/
def U8x32_as_Nat (bytes : Array U8 32#usize) : Nat :=
  ∑ i ∈ Finset.range 32, 2^(8 * i) * (bytes[i]!).val

/-- Interpret a 32-element byte array as a field element in ZMod p via Horner's method.
    This avoids the massive syntax tree that casting `U8x32_as_Nat` to `ZMod p` produces
    (which causes deterministic timeouts when the 32-term Finset.sum gets Nat.cast distributed
    through it). See `U8x32_as_Field_eq_cast` in Aux.lean for the equivalence proof. -/
def U8x32_as_Field (bytes : Array U8 32#usize) : ZMod (2^255 - 19) :=
  bytes.val.foldr (init := (0 : ZMod (2^255 - 19))) fun b acc =>
    (b.val : ZMod (2^255 - 19)) + (256 : ZMod (2^255 - 19)) * acc

/-- Interpret a 64-element byte array as a natural number. -/
def U8x64_as_Nat (bytes : Array U8 64#usize) : Nat :=
  ∑ i ∈ Finset.range 64, 2^(8 * i) * (bytes[i]!).val

/-! ## Primality and CurveField -/

instance : Fact (Nat.Prime p) := ⟨PrimeCert.prime_25519''⟩

namespace Edwards

/-- The finite field F_p where p = 2^255 - 19. -/
abbrev CurveField : Type := ZMod p

end Edwards

/-! ## Field Element Conversions -/

namespace Edwards

open curve25519_dalek.backend.serial.u64.field ZMod

/-- Convert the 5-limb array to a field element in ZMod p. -/
def field_from_limbs (fe : FieldElement51) : CurveField :=
  (Field51_as_Nat fe : CurveField)

end Edwards

/-! ## FieldElement51 Validity and Casting -/

namespace curve25519_dalek.backend.serial.u64.field
open Edwards

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
@[grind unfold]
def FieldElement51.IsValid (fe : FieldElement51) : Prop := ∀ i < 5, fe[i]!.val < 2^54

instance FieldElement51.instDecidableIsValid (fe : FieldElement51) : Decidable fe.IsValid :=
  show Decidable (∀ i < 5, fe[i]!.val < 2^54) from inferInstance

end curve25519_dalek.backend.serial.u64.field

/-! ## Field Utility Functions -/

namespace curve25519_dalek.math

open Edwards ZMod

/-- SQRT_M1: The square root of -1 in the field (used for Elligator inverse sqrt).
    Value: 19681161...84752 -/
def sqrt_m1 : ZMod p :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

/-! ## Isogeny Constants
    We use `@[irreducible]` to prevent the simplifier from unfolding
    these massive literals, which crashes the server.
-/

/--
Raw value for sqrt(ad - 1). Kept private so it's not accidentally used.
-/
private def sqrt_ad_minus_one_val : Nat :=
  25063068953384623474111414158702152701244531502492656460079210482610430750235

/--
Square root of (a * d - 1). Used in the Ristretto isogeny map (Step 7 of elligator_ristretto_flavor).
Since a = -1, this is sqrt(-d - 1).
-/
def sqrt_ad_minus_one : ZMod p := sqrt_ad_minus_one_val

/-- Unfold `sqrt_ad_minus_one` to the raw Nat cast. Proved before `@[irreducible]` takes effect. -/
lemma sqrt_ad_minus_one_eq_val : sqrt_ad_minus_one = (sqrt_ad_minus_one_val : ZMod p) := rfl

/-- Key Property: `sqrt_ad_minus_one` is actually the square root of `-d - 1`. -/
lemma sqrt_ad_minus_one_sq : sqrt_ad_minus_one^2 = -d - 1 := by decide

attribute [irreducible] sqrt_ad_minus_one

/--
Helper: The constant is non-zero.
-/
lemma sqrt_ad_minus_one_ne_zero : sqrt_ad_minus_one ≠ 0 := by
  intro h
  have h_sq : sqrt_ad_minus_one^2 = 0 := by rw [h]; ring
  rw [sqrt_ad_minus_one_sq] at h_sq
  dsimp [d] at h_sq
  norm_num at h_sq
  contradiction

/--
Mathematical square root for ZMod p.
Returns a root if one exists, otherwise 0.
-/
noncomputable def sqrt (x : ZMod p) : ZMod p :=
  if h : IsSquare x then Classical.choose h else 0

/--
Correctness Lemma:
If x is a square, then (math_sqrt x)^2 = x.
-/
lemma sqrt_sq {x : ZMod p} (h : IsSquare x) : (sqrt x)^2 = x := by
  dsimp [sqrt]
  rw [dif_pos h]
  rw [pow_two]
  symm
  exact Classical.choose_spec h

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

/-- `abs_edwards` always produces a non-negative (even parity) value. -/
lemma is_negative_abs_edwards (x : ZMod p) : is_negative (abs_edwards x) = false := by
  unfold abs_edwards
  split_ifs with h
  · -- x is negative (odd parity): result is -x
    unfold is_negative at h ⊢
    by_cases hx : x = 0
    · simp [hx] at h
    · have h_neg_val : (-x : ZMod p).val = p - x.val := by
        rw [ZMod.neg_val]; exact if_neg hx
      rw [h_neg_val]
      have hxlt : x.val < p := x.val_lt
      have hxpos : 0 < x.val := Nat.pos_of_ne_zero (by rwa [ne_eq, ZMod.val_eq_zero])
      have hp_odd : p % 2 = 1 := by decide
      simp only [beq_iff_eq] at h
      rw [beq_eq_false_iff_ne]
      omega
  · -- x is non-negative: result is x, already non-negative
    exact Bool.eq_false_iff.mpr h

/-- `abs_edwards x` has even parity: `(abs_edwards x).val % 2 = 0`. -/
lemma abs_edwards_val_even' (x : ZMod p) : (abs_edwards x).val % 2 = 0 := by
  have h := is_negative_abs_edwards x
  unfold is_negative at h
  rw [beq_eq_false_iff_ne] at h
  omega

/-- abs_edwards always produces a non-negative (even val) result. -/
lemma abs_edwards_val_even (hp_odd : p % 2 = 1) (b : ZMod p) :
    (abs_edwards b).val % 2 = 0 :=
  abs_edwards_val_even' b

/-- If a² = b² and a has even val, then a = abs_edwards b.
    In ZMod p for odd p, the non-negative square root is unique. -/
lemma eq_abs_edwards_of_sq_eq (hp_odd : p % 2 = 1) {a b : ZMod p}
    (h_sq : a ^ 2 = b ^ 2) (ha : a.val % 2 = 0) :
    a = abs_edwards b := by
  have h_sq' : a ^ 2 = (abs_edwards b) ^ 2 := by rw [h_sq, abs_edwards_sq]
  have hab : (abs_edwards b).val % 2 = 0 := abs_edwards_val_even hp_odd b
  have h_factor : (a - abs_edwards b) * (a + abs_edwards b) = 0 := by
    linear_combination h_sq'
  rcases mul_eq_zero.mp h_factor with h | h
  · exact sub_eq_zero.mp h
  · have heq : a = -(abs_edwards b) := by linear_combination h
    by_cases h0 : abs_edwards b = 0
    · rw [h0, neg_zero] at heq; rw [heq, h0]
    · exfalso
      rw [heq, ZMod.neg_val, if_neg h0] at ha
      have := Nat.add_sub_cancel' (le_of_lt (ZMod.val_lt (abs_edwards b)))
      omega

/-- abs_edwards is invariant under sign: if a² = b² then abs_edwards a = abs_edwards b. -/
lemma abs_edwards_eq_of_sq_eq_sq (hp_odd : p % 2 = 1) {a b : ZMod p}
    (h : a ^ 2 = b ^ 2) : abs_edwards a = abs_edwards b :=
  eq_abs_edwards_of_sq_eq hp_odd (by rw [abs_edwards_sq, h]) (abs_edwards_val_even hp_odd a)

/-- `abs_edwards` is invariant under negation: `abs_edwards (-x) = abs_edwards x`. -/
lemma abs_edwards_neg (x : ZMod p) : abs_edwards (-x) = abs_edwards x := by
  by_cases hx : x = 0
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

/-- If `x^2 = y^2` then `abs_edwards x = abs_edwards y`. -/
lemma abs_edwards_eq_of_sq_eq {x y : ZMod p} (h : x ^ 2 = y ^ 2) :
    abs_edwards x = abs_edwards y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h_eq | h_neg
  · rw [h_eq]
  · rw [h_neg, abs_edwards_neg]

/-- Square root with quadratic residue check, matching Rust's sqrt_ratio_i(x, 1).
    Returns (sqrt(x), true) when x is a square, (sqrt(i*x), false) otherwise.
    Note: sqrt_checked 0 = (0, true) since 0 is a square (0² = 0). -/
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

/-- Spec: If `sqrt_checked` returns true, the result is a valid square root. -/
theorem sqrt_checked_spec (u : ZMod p) {r : ZMod p} {b : Bool} :
  sqrt_checked u = (r, b) → b = true → r^2 = u := by
  intro h_call h_true
  sorry -- Proof deferred

/-- Spec: `sqrt_checked` returns true iff the input is a square. -/
theorem sqrt_checked_iff_isSquare (u : ZMod p) {r : ZMod p} {b : Bool} :
  sqrt_checked u = (r, b) → (b = true ↔ IsSquare u) := by
  intro h_call
  sorry -- Proof deferred

/--
Inverse Square Root, matching Rust's sqrt_ratio_i(1, u).
Computes 1/sqrt(u) or 1/sqrt(i*u) depending on whether u is a square.
Guard: inv_sqrt_checked 0 = (0, false) since 1/sqrt(0) is undefined.
This matches Rust's sqrt_ratio_i(1, 0) returning (Choice(0), 0).
-/
noncomputable def inv_sqrt_checked (u : ZMod p) : (ZMod p × Bool) :=
  if u = 0 then (0, false)
  else
    let (root, was_square) := sqrt_checked u
    (root⁻¹, was_square)

/--
Mathematical specification for `inv_sqrt_checked`.
-/
theorem inv_sqrt_checked_spec (arg : ZMod p) {I : ZMod p} {was_square : Bool} :
  inv_sqrt_checked arg = (I, was_square) →
  was_square = true →
  arg ≠ 0 →
  I^2 * arg = 1 := by
  -- We treat this as an axiom/specification for now to avoid
  -- analyzing the massive bit-level recursion of the implementation.
  sorry

/--
When `u` is a square, `(inv_sqrt_checked u).1` is its inverse square root.
Combined lemma avoids maxRecDepth from pair-destructuring `inv_sqrt_checked`.
-/
theorem inv_sqrt_checked_sq_mul (u : ZMod p) (h : IsSquare u) (h_ne : u ≠ 0) :
    (inv_sqrt_checked u).1 ^ 2 * u = 1 := by
  sorry

/-- Reduction: inv_sqrt_checked 0 = (0, false) via the zero guard. -/
lemma inv_sqrt_checked_zero : inv_sqrt_checked (0 : ZMod p) = ((0 : ZMod p), false) := by
  delta inv_sqrt_checked; rw [if_pos rfl]

/-- Reduction: the boolean component of inv_sqrt_checked matches sqrt_checked when u ≠ 0. -/
lemma inv_sqrt_checked_snd (u : ZMod p) (hu : u ≠ 0) :
    (inv_sqrt_checked u).2 = (sqrt_checked u).2 := by
  sorry


end curve25519_dalek.math
