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
-- import PrimeCert.PrimeList

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

end curve25519_dalek.math
