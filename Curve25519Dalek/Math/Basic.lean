/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Types
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import PrimeCert.PrimeList
import Mathlib.FieldTheory.Finite.Basic

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

/-- The constant d in the defining equation for the twisted Edwards curve:
    ax^2 + y^2 = 1 + dx^2y^2 -/
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The constant a in the defining equation for the twisted Edwards curve:
    ax^2 + y^2 = 1 + dx^2y^2 -/
def a : Int := -1

/-! ## Scalar Montgomery arithmetic helpers -/

set_option exponentiation.threshold 260 in
/-- Cancel `R` from both sides of a congruence mod `L`.
    Used in Montgomery-form scalar specs (Scalar.reduce, Scalar52.mul). -/
lemma cancelR {a b : ℕ} (h : a * R ≡ b * R [MOD L]) : a ≡ b [MOD L] := by
  have hcoprime : Nat.Coprime R L := by
    unfold R L
    exact Nat.Coprime.pow_left 260 (by norm_num [Nat.Coprime])
  exact Nat.ModEq.cancel_right_of_coprime hcoprime.symm h

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

/-- Interpret a 4-element `u64` array as a 256-bit natural number in
    little-endian limb order. -/
def X64_as_Nat (limbs : Array U64 4#usize) : ℕ :=
  ∑ i ∈ Finset.range 4, 2 ^ (64 * i) * (limbs[i]!).val

/-- Interpret a 64-element `i8` array as a signed integer in base `2^w`. -/
def I8x64_as_Radix2w (w : ℕ) (digits : Array I8 64#usize) : ℤ :=
  ∑ i ∈ Finset.range 64, (2 ^ w : ℤ) ^ i * (digits[i]!).val

/-! ## Basic properties of the defined quantities -/

theorem L_lt : L < 2 ^ 260 := by
  unfold L
  omega

/-! ### Scalar52_as_Nat lemmas -/

attribute [-simp] Int.reducePow Nat.reducePow

/-- If all limbs are < 2^52, then Scalar52_as_Nat < 2^260 -/
theorem Scalar52_as_Nat_bounded (s : Aeneas.Std.Array U64 5#usize)
    (hs : ∀ i < 5, s[i]!.val < 2 ^ 52) :
    Scalar52_as_Nat s < 2 ^ 260 := by
  simp only [Scalar52_as_Nat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega)
  have h3 := hs 3 (by omega); have h4 := hs 4 (by omega)
  omega

/-- A single limb's weighted contribution is at most Scalar52_as_Nat -/
theorem Scalar52_limb_le_nat (s : Aeneas.Std.Array U64 5#usize) (i : Nat) (hi : i < 5) :
    2 ^ (52 * i) * s[i]!.val ≤ Scalar52_as_Nat s := by
  simp only [Scalar52_as_Nat, Finset.sum_range_succ]
  interval_cases i <;> omega

/-! ### Scalar52_wide_as_Nat lemmas -/

/-- A single limb's weighted contribution is at most Scalar52_wide_as_Nat -/
theorem Scalar52_wide_limb_le_nat (a : Aeneas.Std.Array U128 9#usize) (i : Nat) (hi : i < 9) :
    2 ^ (52 * i) * a[i]!.val ≤ Scalar52_wide_as_Nat a := by
  simp only [Scalar52_wide_as_Nat, Finset.sum_range_succ]
  interval_cases i <;> omega

/-! ## Primality and CurveField -/

instance : Fact (Nat.Prime p) := ⟨PrimeCert.prime_25519''⟩
instance : Fact (Nat.Prime L) := ⟨PrimeCert.prime_ed25519_order⟩

namespace Edwards

/-- The finite field F_p where p = 2^255 - 19. -/
abbrev CurveField : Type := ZMod p

/-- Helper lemma for modular arithmetic lifting -/
theorem lift_mod_eq (a b : ℕ) (h : a % p = b % p) : (a : CurveField) = (b : CurveField) :=
  (ZMod.natCast_eq_natCast_iff a b p).mpr h

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

/-- Lift a tighter limb bound (`< 2^k` for any `k ≤ 54`) to `FieldElement51.IsValid`.
Eliminates the repeated `Nat.lt_trans (h i hi) (by norm_num : 2^k < 2^54)` boilerplate
that appears across the Double / Add / Sub specs. -/
lemma FieldElement51.IsValid_of_lt_pow
    {fe : FieldElement51} {k : ℕ}
    (h : ∀ i < 5, fe[i]!.val < 2 ^ k) (hk : k ≤ 54) : fe.IsValid :=
  fun i hi => Nat.lt_of_lt_of_le (h i hi) (Nat.pow_le_pow_right (by decide) hk)

end curve25519_dalek.backend.serial.u64.field

/-! ## Field Utility Functions -/

namespace curve25519_dalek.math

open Edwards ZMod

/-- Nat.ModEq against zero as a remainder equality. -/
theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔ a % n = 0 := by
  simp [Nat.ModEq]

/-- Nat.ModEq against one modulo the field prime `p`. -/
theorem modEq_one_iff (a : ℕ) : a ≡ 1 [MOD p] ↔ a % p = 1 := by
  simp only [Nat.ModEq]
  have : 1 % p = 1 := by
    unfold p
    decide
  rw [this]

/-- Squaring preserves equality modulo `p` after moving one term across zero. -/
theorem nat_sq_of_add_modeq_zero {a b p : ℕ}
    (h : a + b ≡ 0 [MOD p]) :
    a ^ 2 ≡ b ^ 2 [MOD p] := by
  have h1 := h.mul_left a
  have h2 := h.mul_right b
  simp only [zero_mul] at h2
  have h1' : a * a + a * b ≡ 0 [MOD p] := by
    simpa only [Nat.mul_add, mul_zero] using h1
  have h2' : a * b + b * b ≡ 0 [MOD p] := by
    simpa only [Nat.add_mul] using h2
  have hsum : a * b + a * a ≡ a * b + b * b [MOD p] := by
    rw [add_comm]
    apply Nat.ModEq.symm at h2'
    exact Nat.ModEq.trans h1' h2'
  apply Nat.ModEq.add_left_cancel' at hsum
  simpa only [pow_two] using hsum

/-- Squaring after reduction modulo `p` agrees with squaring first modulo `p`. -/
theorem mod_sq_mod (a p : ℕ) : (a % p) ^ 2 ≡ a ^ 2 [MOD p] := by
  exact (Nat.mod_modEq a p).pow 2

/-- Multiplication after reduction modulo `p` agrees with multiplication first modulo `p`. -/
theorem mod_mul_mod (a b : ℕ) : (a % p) * (b % p) ≡ a * b [MOD p] := by
  exact ((Nat.mod_modEq a p).mul_right (b % p)).trans ((Nat.mod_modEq b p).mul_left a)

/-- Square-then-multiply form of `mod_sq_mod`. -/
theorem mod_sq_mod_mul (a b p : ℕ) : (a % p) ^ 2 * b ≡ a ^ 2 * b [MOD p] := by
  exact (Nat.ModEq.mul_right b (mod_sq_mod a p))

/-- Equality form of `mod_sq_mod_mul`. -/
theorem mod_sq_mod_mul_eq (a b p : ℕ) : ((a % p) ^ 2 * b) % p = (a ^ 2 * b) % p := by
  rw [← Nat.ModEq]
  exact mod_sq_mod_mul a b p

/-- Equality form of `mod_sq_mod`. -/
theorem mod_sq_mod_eq (a p : ℕ) : ((a % p) ^ 2) % p = (a ^ 2) % p := by
  exact (Nat.mod_modEq a p).pow 2

/-- Alias for `mod_sq_mod_eq`. -/
theorem sq_mod_eq_mod_sq (a p : ℕ) : ((a % p) ^ 2) % p = (a ^ 2) % p :=
  mod_sq_mod_eq a p

/-- Zero divisors do not exist modulo a prime. -/
theorem mul_zero_eq_or {a b p : ℕ} {hp : p.Prime}
    (hab : a * b ≡ 0 [MOD p]) :
    a ≡ 0 [MOD p] ∨ b ≡ 0 [MOD p] := by
  rw [Nat.ModEq] at hab
  have h_dvd : p ∣ a * b := Nat.dvd_of_mod_eq_zero hab
  obtain ha | hb := hp.dvd_mul.mp h_dvd
  · left
    exact Nat.mod_eq_zero_of_dvd ha
  · right
    exact Nat.mod_eq_zero_of_dvd hb

/-- SQRT_M1: The square root of -1 in the field (used for Elligator inverse sqrt).
    Value: 19681161...84752 -/
def sqrt_m1 : ZMod p :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

lemma p_sub_one_cast : (↑(p - 1) : ZMod p) = -1 := by
  rw [Nat.cast_sub (by decide : 1 ≤ p), ZMod.natCast_self, zero_sub, Nat.cast_one]

lemma ringChar_ne_two : ringChar (ZMod p) ≠ 2 := by
  suffices p ≠ 2 by simpa [ZMod.ringChar_zmod_n p]
  norm_num [p]

lemma ne_zero_of_not_isSquare {a : ZMod p} (h : ¬ IsSquare a) : a ≠ 0 := by by_contra; simp_all

-- TODO: this should probably be replaced by an argument using the quadratic character from
-- `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic`.
/-- In a finite field of odd characteristic, the product of two non-squares is a square. -/
theorem FiniteField.isSquare_mul_of_not_isSquare {F : Type*} [Field F] [Finite F]
    (hchar : ringChar F ≠ 2) {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  have := Fintype.ofFinite F
  have ha0 : a ≠ 0 := by intro h; exact ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := by intro h; exact hb (h ▸ IsSquare.zero)
  have half_pow_neg {z : F} (hz : z ≠ 0) (hns : ¬ IsSquare z) :
      z ^ (Fintype.card F / 2) = -1 :=
    (FiniteField.pow_dichotomy hchar hz).resolve_left
      (fun h1 => hns ((FiniteField.isSquare_iff hchar hz).mpr h1))
  rw [FiniteField.isSquare_iff hchar (mul_ne_zero ha0 hb0),
      mul_pow, half_pow_neg ha0 ha, half_pow_neg hb0 hb]
  norm_num

private lemma sqrt_m1_sq_nat :
    19681161376707505956807079304988542015446066515923890162744021073123829784752 ^ 2 % p =
    p - 1 := by
  decide

/-- `sqrt_m1` really is a square root of `-1` in `ZMod p`. -/
lemma sqrt_m1_sq : (sqrt_m1 : ZMod p) ^ 2 = -1 := by
  unfold sqrt_m1
  have h : (((19681161376707505956807079304988542015446066515923890162744021073123829784752
        ^ 2 : ℕ)) : ZMod p) =
      ((p - 1 : ℕ) : ZMod p) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (by simpa [Nat.ModEq] using sqrt_m1_sq_nat)
  push_cast at h
  rwa [p_sub_one_cast] at h

/-- `sqrt_m1` is not itself a square; otherwise there would be an element of order `8` in `F_pˣ`. -/
lemma sqrt_m1_not_square : ¬ IsSquare sqrt_m1 := by
  rintro ⟨y, hy⟩
  rw [← pow_two] at hy
  have y4 : y ^ 4 = -1 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, ← hy, sqrt_m1_sq]
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (by norm_num)] at y4
    norm_num at y4
  have y8 : y ^ 8 = 1 := by
    rw [show 8 = 4 * 2 by norm_num, pow_mul, y4]
    norm_num
  have h_order : orderOf y = 8 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) y8 ?_
    intro q hprime hdvd
    have hq : q = 2 := by
      rw [show 8 = 2 ^ 3 by norm_num] at hdvd
      exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hdvd)
    rw [hq, show 8 / 2 = 4 by norm_num, y4]
    intro h_eq
    have h_two : (2 : ZMod p) = 0 := by
      have := congrArg (fun z : ZMod p => z + 1) h_eq
      have h_zero : (0 : ZMod p) = 2 := by simpa using this
      exact h_zero.symm
    have h_dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h_two
    norm_num [p] at h_dvd
  have order_div : 8 ∣ (p - 1) := by
    simpa [ZMod.card, h_order] using ZMod.orderOf_dvd_card_sub_one hy_ne_zero
  have not_dvd : ¬ 8 ∣ (p - 1) := by
    intro h8
    have mod_zero : (p - 1) % 8 = 0 := Nat.mod_eq_zero_of_dvd h8
    norm_num [p] at mod_zero
  exact not_dvd order_div

/-! ## Isogeny Constants
    We use `@[irreducible]` to prevent the simplifier from unfolding
    these massive literals, which crashes the server.
-/

/-- Raw value for sqrt(ad - 1). Kept private so it's not accidentally used. -/
private def sqrt_ad_minus_one_val : Nat :=
  25063068953384623474111414158702152701244531502492656460079210482610430750235

/-- Square root of (a * d - 1). Used in the Ristretto isogeny map
(Step 7 of elligator_ristretto_flavor).
Since a = -1, this is sqrt(-d - 1). -/
def sqrt_ad_minus_one : ZMod p := sqrt_ad_minus_one_val

/-- Unfold `sqrt_ad_minus_one` to the raw Nat cast. Proved before `@[irreducible]` takes effect. -/
lemma sqrt_ad_minus_one_eq_val : sqrt_ad_minus_one = (sqrt_ad_minus_one_val : ZMod p) := rfl

/-- Key Property: `sqrt_ad_minus_one` is actually the square root of `-d - 1`. -/
lemma sqrt_ad_minus_one_sq : sqrt_ad_minus_one^2 = -d - 1 := by decide

attribute [irreducible] sqrt_ad_minus_one

/-- Helper: The constant is non-zero. -/
lemma sqrt_ad_minus_one_ne_zero : sqrt_ad_minus_one ≠ 0 := by
  intro h
  have h_sq : sqrt_ad_minus_one^2 = 0 := by rw [h]; ring
  rw [sqrt_ad_minus_one_sq] at h_sq
  dsimp only [d] at h_sq
  norm_num at h_sq
  contradiction

/-- Mathematical square root for ZMod p.
Returns a root if one exists, otherwise 0. -/
noncomputable def sqrt (x : ZMod p) : ZMod p :=
  if h : IsSquare x then Classical.choose h else 0

/-- Correctness Lemma:
If x is a square, then (math_sqrt x)^2 = x. -/
lemma sqrt_sq {x : ZMod p} (h : IsSquare x) : (sqrt x)^2 = x := by
  dsimp only [sqrt]
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

/-- Square property of the absolute value function.
Since `abs_edwards x` is either `x` or `-x`, its square is always `x^2`. -/
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
lemma abs_edwards_val_even (_ : p % 2 = 1) (b : ZMod p) :
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
    let y := Classical.choose h
    (abs_edwards y, true)
  else
    have h_ix : IsSquare (x * sqrt_m1) :=
      FiniteField.isSquare_mul_of_not_isSquare ringChar_ne_two h sqrt_m1_not_square
    let y := Classical.choose h_ix
    (abs_edwards y, false)

/-- Spec: If `sqrt_checked` returns true, the result is a valid square root. -/
theorem sqrt_checked_spec (u : ZMod p) {r : ZMod p} {b : Bool} :
  sqrt_checked u = (r, b) → b = true → r^2 = u := by
  intro h_call h_true
  unfold sqrt_checked at h_call
  split_ifs at h_call with h_sq
  · -- IsSquare branch: returned (abs_edwards y, true)
    obtain ⟨rfl, -⟩ := Prod.mk.inj h_call
    rw [abs_edwards_sq, pow_two]
    exact (Classical.choose_spec h_sq).symm
  · -- Not IsSquare branch: returned (_, false), contradicts b = true
    obtain ⟨-, hb⟩ := Prod.mk.inj h_call
    exact absurd h_true (by rw [← hb]; decide)

/-- Spec: `sqrt_checked` returns true iff the input is a square. -/
theorem sqrt_checked_iff_isSquare (u : ZMod p) {r : ZMod p} {b : Bool} :
  sqrt_checked u = (r, b) → (b = true ↔ IsSquare u) := by
  intro h_call
  unfold sqrt_checked at h_call
  split_ifs at h_call with h_sq
  · obtain ⟨-, rfl⟩ := Prod.mk.inj h_call
    exact ⟨fun _ => h_sq, fun _ => rfl⟩
  · obtain ⟨-, rfl⟩ := Prod.mk.inj h_call
    exact ⟨fun h => absurd h (by decide), fun h => absurd h h_sq⟩

/-- Inverse Square Root, matching Rust's sqrt_ratio_i(1, u). Computes 1/sqrt(u) or 1/sqrt(i*u)
depending on whether u is a square. Guard: inv_sqrt_checked 0 = (0, false) since 1/sqrt(0) is
undefined. This matches Rust's sqrt_ratio_i(1, 0) returning (Choice(0), 0). -/
noncomputable def inv_sqrt_checked (u : ZMod p) : (ZMod p × Bool) :=
  if u = 0 then (0, false)
  else (sqrt_checked u).map (·⁻¹) id -- return `sqrt_checked u` but invert the first component.
  -- The alternative using `let` here causes a nightmare later when working with the definition.

/-- For `u ≠ 0`, `inv_sqrt_checked u` equals `(sqrt_checked u)` with first component inverted. -/
private lemma inv_sqrt_checked_unfold (u : ZMod p) (hu : u ≠ 0) :
    inv_sqrt_checked u = (sqrt_checked u).map (·⁻¹) id := by
  delta inv_sqrt_checked; rw [if_neg hu]

/-- Mapping a function over the first component of a pair preserves the second component. -/
private theorem inv_snd_abstract {α β γ : Type*} {f : α → γ} {p : α × β} {q : γ × β}
    (h : q = p.map f id) : q.2 = p.2 := by
  rw [h, Prod.map_snd, id]

/-- If `f` returns a square root when the boolean is `true`, then mapping `(·⁻¹)` over the first
component yields an inverse square root. Proved abstractly to avoid kernel reduction of `ZMod p`. -/
private theorem inv_sqrt_spec_abstract {F : Type*} [Field F] (f : F → F × Bool)
    (f_spec : ∀ {r : F} {b : Bool} (x : F), f x = (r, b) → b = true → r ^ 2 = x)
    {arg I : F} (h : (f arg).map (·⁻¹) id = (I, true)) (hne : arg ≠ 0) : I ^ 2 * arg = 1 := by
  have hI : (f arg).1⁻¹ = I := by simpa only [Prod.map_fst] using congr_arg Prod.fst h
  have hws : (f arg).2 = true := by simpa only [Prod.map_snd, id] using congr_arg Prod.snd h
  have h_sq : (f arg).1 ^ 2 = arg := f_spec arg Prod.mk.eta.symm hws
  rw [← hI, inv_pow, h_sq, inv_mul_cancel₀ hne]

/-- If `inv_sqrt_checked arg = (I, true)` and `arg ≠ 0`, then `I` is an inverse square root:
`I ^ 2 * arg = 1`. -/
theorem inv_sqrt_checked_spec' (arg : ZMod p) {I : ZMod p} (h : inv_sqrt_checked arg = (I, true))
    (hne : arg ≠ 0) : I ^ 2 * arg = 1 := by
  rw [inv_sqrt_checked_unfold arg hne] at h
  exact inv_sqrt_spec_abstract sqrt_checked (fun x h hb => sqrt_checked_spec x h hb) h hne

/-- Variant of `inv_sqrt_checked_spec` with `was_square` as a separate hypothesis. -/
theorem inv_sqrt_checked_spec (arg : ZMod p) {I : ZMod p} {was_square : Bool}
    (h : inv_sqrt_checked arg = (I, was_square)) (hws : was_square = true) (hne : arg ≠ 0) :
    I ^ 2 * arg = 1 := by
  subst hws; exact inv_sqrt_checked_spec' arg h hne

/-- `inv_sqrt_checked 0 = (0, false)`. -/
lemma inv_sqrt_checked_zero : inv_sqrt_checked (0 : ZMod p) = ((0 : ZMod p), false) := by
  delta inv_sqrt_checked; rw [if_pos rfl]

/-- For `u ≠ 0`, the boolean component of `inv_sqrt_checked u` equals that of `sqrt_checked u`. -/
lemma inv_sqrt_checked_snd (u : ZMod p) (hu : u ≠ 0) :
    (inv_sqrt_checked u).2 = (sqrt_checked u).2 :=
  inv_snd_abstract (inv_sqrt_checked_unfold u hu)

/-- If `u` is a nonzero square, `(inv_sqrt_checked u).1` is an inverse square root of `u`. -/
theorem inv_sqrt_checked_sq_mul (u : ZMod p) (h : IsSquare u) (hne : u ≠ 0) :
    (inv_sqrt_checked u).1 ^ 2 * u = 1 := by
  have h_ws : (inv_sqrt_checked u).2 = true := by
    rw [inv_sqrt_checked_snd u hne]
    exact (sqrt_checked_iff_isSquare u Prod.mk.eta.symm).mpr h
  exact inv_sqrt_checked_spec' u (Prod.ext rfl h_ws) hne


end curve25519_dalek.math
