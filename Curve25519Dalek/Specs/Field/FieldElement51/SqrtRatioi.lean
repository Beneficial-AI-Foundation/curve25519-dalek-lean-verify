/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Field.FieldElement51.PowP58
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
/-! # Spec Theorem for `FieldElement51::sqrt_ratio_i`

Specification and proof for `FieldElement51::sqrt_ratio_i`.

This function computes a nonnegative square root of u/v or i*u/v (where i = sqrt(-1) = SQRT_M1 constant),
returning a flag indicating which case occurred and handling zero inputs specially.

**Source**: curve25519-dalek/src/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.field.FieldElement51


theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔  a % n = 0 := by simp [Nat.ModEq]

theorem mod_two_Eq_one_iff (a : ℕ) : a ≡ 1 [MOD 2] ↔  a % 2 = 1 := by simp [Nat.ModEq]


theorem nat_sq_of_add_modeq_zero {a b p : ℕ}
  (h : a + b ≡ 0 [MOD p]) :
  a ^ 2 ≡ b ^ 2 [MOD p] := by
  have h1  := h.mul_left a
  have h2  := h.mul_right b
  simp at h2
  have h1' : a * a + a * b ≡ 0 [MOD p] := by simpa [Nat.mul_add, pow_two] using h1
  have h2' : a * b + b * b ≡ 0 [MOD p] := by simpa [Nat.add_mul, pow_two] using h2
  have hsum : a * b + a * a ≡ a * b + b * b [MOD p] := by
    rw[add_comm]
    apply Nat.ModEq.symm at h2'
    apply Nat.ModEq.trans h1' h2'
  apply Nat.ModEq.add_left_cancel' at hsum
  simp[pow_two]
  exact hsum





lemma mod_idem (a p : Nat) : (a % p) % p = a % p := by
   by_cases h0 : p = 0
   · simp [h0]
   · have hp : 0 < p := Nat.pos_of_ne_zero h0
     exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)


-- Helper: equality of to_bytes implies equality modulo p of Field51_as_Nat
/-- If two FieldElement51 values produce identical canonical byte encodings,
then their natural-number interpretations are congruent modulo p. In particular,
(normal form) remainders modulo p are equal. -/
theorem eq_to_bytes_eq_Field51_as_Nat
    (u v : backend.serial.u64.field.FieldElement51)
    (h : u.to_bytes = v.to_bytes) :
  Field51_as_Nat u % p = Field51_as_Nat v % p := by
  classical
  obtain ⟨ru, hu, hru_mod, _⟩ := to_bytes_spec u
  obtain ⟨rv, hv, hrv_mod, _⟩ := to_bytes_spec v
  -- From the equality of the Result values, and the spec that they are ok, we get ru = rv
  have hrr : ru = rv := by
    have : ok ru = ok rv := by simpa [hu, hv] using h
    cases this
    rfl
  -- Chain the two congruences via the common bytes value
  have huv_mod : Nat.ModEq p (Field51_as_Nat u) (Field51_as_Nat v) := by
    have h1 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat u) := by
      simpa [hrr] using hru_mod
    have h2 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat v) := hrv_mod
    exact (Nat.ModEq.symm h1).trans h2
  -- Turn ModEq into equality of remainders
  simpa [Nat.ModEq] using huv_mod





set_option maxHeartbeats 100000000 in
-- simp_all heavy


/-
Natural language description:

    This function takes two field elements u and v and returns

    - (Choice(1), +sqrt(u/v))       if v is nonzero and u/v is square;
    - (Choice(1), zero)             if u is zero;
    - (Choice(0), zero)             if v is zero and u is nonzero;
    - (Choice(0), +sqrt(i * u/v))   if u/v is nonsquare (so i*u/v is square).

Here i represents a square root of -1 in the field (mod p) and is stored as the constant SQRT_M1.
Every returned square root is nonnegative.

Natural language specs:

    • The function succeeds (no panic) for all field element inputs
    • The result (c, r) satisfies four mutually exclusive cases:

      - If u = 0 (mod p), then (c, r) = (Choice(1), 0)

      - If u ≠ 0 (mod p) and v = 0 (mod p), then (c, r) = (Choice(0), 0)

      - If u ≠ 0 (mod p) and v ≠ 0 (mod p) and (u/v) is a square, then (c, r) = (Choice(1), sqrt(u/v))

      - If u ≠ 0 (mod p) and v ≠ 0 (mod p) and (u/v) is not a square, then (c, r) = (Choice(0), sqrt(SQRT_M1 * u/v))

    • In all cases, r is non-negative
-/

/-- **Spec and proof concerning `field.FieldElement51.sqrt_ratio_i`**:
- No panic for field element inputs u and v (always returns (c, r) successfully)
- The result satisfies exactly one of four mutually exclusive cases:
  1. If u ≡ 0 (mod p), then c.val = 1 and r ≡ 0 (mod p)
  2. If u ≢ 0 (mod p) and v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
  3. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 1 and r^2 ≡ u * v^(-1) (mod p)
  4. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ¬∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 0 and r^2 ≡ SQRT_M1 * u * v^(-1) (mod p)
-/


@[progress]
theorem sqrt_ratio_i_spec

    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val ≤ 2 ^ 51 - 1)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 51 - 1) :

    ∃ c r, sqrt_ratio_i u v = ok (c, r) ∧
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat r % p
    let i_nat := Field51_as_Nat backend.serial.u64.constants.SQRT_M1 % p

    -- Case 1: u is zero
    (u_nat = 0 →
    c.val = 1#u8 ∧ r_nat = 0) ∧

    -- Case 2: u is nonzero and v is zero
    (u_nat ≠ 0 ∧ v_nat = 0 →
    c.val = 0#u8 ∧ r_nat = 0) ∧

    -- Case 3: u and v are nonzero and u/v is a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.val = 1#u8 ∧ (r_nat^2 * v_nat) % p = u_nat) ∧

    -- Case 4: u and v are nonzero and u/v is not a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ ¬(∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.val = 0#u8 ∧ (r_nat^2 * v_nat) % p = (i_nat * u_nat) % p)

    := by
    unfold sqrt_ratio_i
    progress*
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (fe_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (v3_post_2 i hi)
      simp
    · intro i hi
      apply lt_trans (fe1_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_u_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (v3_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_u_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (v7_post_2 i hi)
      simp
    · intro i hi
      apply Nat.le_pred_of_lt (fe3_post_2 i hi)
    · intro i hi
      apply lt_trans (fe2_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (fe4_post_2 i hi)
      simp
    · intro i hi
      apply lt_trans (r_post_2  i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (fe5_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_u_bounds i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (fe6_post_2  i hi)
      simp
    · unfold constants.SQRT_M1
      decide
    · unfold constants.SQRT_M1
      decide
    · intro i hi
      apply lt_trans (r_post_2  i hi)
      simp
    unfold   subtle.BitOrsubtleChoicesubtleChoicesubtleChoice.bitor
    by_cases h : flipped_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt_i.val = 1#u8
    · simp[h]
      unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
      progress*
      · simp_all
        intro i a
        simp[Choice.one]
        apply lt_trans (r_prime_post_2  i a)
        simp
      ·  by_cases hs :correct_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt.val = 1#u8
         · simp[hs, Choice.one]
           constructor
           · intro hu
             simp_all
             simp[Choice.one] at r1_post
             have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
               simp[Field51_as_Nat, Finset.sum_range_succ]
               simp_all
             simp[Choice.one, this] at r2_post
             rw[← modEq_zero_iff]
             rw[← modEq_zero_iff] at hu
             have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
             simp at this
             have := Nat.ModEq.trans fe2_post_1 this
             have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
             simp at this
             have := Nat.ModEq.trans r_post_1 this
             have := Nat.ModEq.mul_left (Field51_as_Nat constants.SQRT_M1) this
             have r_prime_eq0:= Nat.ModEq.trans r_prime_post_1 this
             simp at r_prime_eq0
             have : Field51_as_Nat r_prime % p % 2 = 0 := by
                    simp[Nat.ModEq] at r_prime_eq0
                    rw[r_prime_eq0]
             simp[this] at r2_post
             have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
               simp[Field51_as_Nat, Finset.sum_range_succ]
               simp_all
             rw[this]
             apply r_prime_eq0
           · constructor
             · intro hup hvp
               apply hup
               rw[← modEq_zero_iff]
               rw[← modEq_zero_iff] at hvp
               have := Nat.ModEq.mul_right (Field51_as_Nat fe5) hvp
               simp at this
               have check0:= Nat.ModEq.trans check_post_1 this
               rcases hs with hs | hs
               · have : correct_sign_sqrt = Choice.one := by
                   exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp hs
                 simp[this] at correct_sign_sqrt_post
                 have := eq_to_bytes_eq_Field51_as_Nat check u correct_sign_sqrt_post
                 rw[← Nat.ModEq] at this
                 apply Nat.ModEq.trans (Nat.ModEq.symm this) check0
               · have : flipped_sign_sqrt = Choice.one := by
                   exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp hs
                 simp[this] at flipped_sign_sqrt_post
                 have := eq_to_bytes_eq_Field51_as_Nat check fe6 flipped_sign_sqrt_post
                 rw[← Nat.ModEq] at this
                 have := Nat.ModEq.trans (Nat.ModEq.symm this) check0
                 have := Nat.ModEq.add_left (Field51_as_Nat u) this
                 rw[← modEq_zero_iff] at fe6_post_1
                 have := Nat.ModEq.trans (Nat.ModEq.symm this) fe6_post_1
                 simp at this
                 exact this
             · constructor
               · intro hup hvp x1 hx1
                 rw[← Nat.ModEq]
                 rw[← Nat.ModEq] at hx1
                 simp_all
                 simp[Choice.one] at r1_post
                 simp[Choice.one] at r2_post
                 have r1_eq: Field51_as_Nat r1 = Field51_as_Nat r_prime := by
                    simp[Field51_as_Nat, Finset.sum_range_succ]
                    simp_all
                 rw[r1_eq] at r2_post
                 by_cases hr_p: Field51_as_Nat r_prime % p % 2 = 1
                 · simp[hr_p] at r2_post
                   have : Field51_as_Nat r2 = Field51_as_Nat x := by
                    simp[Field51_as_Nat, Finset.sum_range_succ]
                    simp_all
                   rw[this]
                   rw[← modEq_zero_iff] at x_post_1
                   have := nat_sq_of_add_modeq_zero x_post_1
                   rw[r1_eq] at this






                 · simp[hr_p] at r2_post
                   have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
                    simp[Field51_as_Nat, Finset.sum_range_succ]
                    simp_all
                   rw[this]




                 rcases hs with hs | hs
                 · have : correct_sign_sqrt = Choice.one := by
                    exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp hs
                   simp[this] at correct_sign_sqrt_post
                   have check_eq:= eq_to_bytes_eq_Field51_as_Nat check u correct_sign_sqrt_post
                   rw[← Nat.ModEq] at check_eq
                   by_cases his: r_is_negative.val = 1#u8
                   · simp_all

                   apply Nat.ModEq.symm
                   apply Nat.ModEq.trans (Nat.ModEq.symm check_eq)
                   rw[mul_comm]
                   apply  Nat.ModEq.trans check_post_1
                   apply Nat.ModEq.mul_left
                   apply  Nat.ModEq.trans fe5_post_1
                   apply Nat.ModEq.pow
                   have := Nat.ModEq.trans (Nat.ModEq.symm check_post_1) check_eq
                   apply Nat.ModEq.symm at hx1
                   apply Nat.ModEq.trans check_eq at hx1
                   rw[mul_comm] at hx1
                   apply  Nat.ModEq.trans (Nat.ModEq.symm  check_post_1) at hx1
                   rw[← modEq_zero_iff] at hvp
                   have := Nat.ModEq.mul_left (Field51_as_Nat v) fe5_post_1
                   have := Nat.ModEq.trans (Nat.ModEq.symm hx1) this
                   simp[Choice.one] at r1_post
                   have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
                    simp[Field51_as_Nat, Finset.sum_range_succ]
                    simp_all
                   rw[this] at  r_is_negative_post
                   rw[Nat.ModEq, mod_idem]
                   rw[← Nat.ModEq]
                   have := Nat.ModEq.pow 2 r_prime_post_1
                   rw[mul_pow] at this
                   by_cases his: r_is_negative.val = 1#u8
                   · rw[his] at r2_post
                     simp[his] at r_is_negative_post
                     have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
                        simp[Field51_as_Nat, Finset.sum_range_succ]
                        simp_all
                     rw[this]
                     apply Nat.ModEq.symm
                     apply Nat.ModEq.trans r_prime_post_1
                     rw[Nat.ModEq] at r_prime_post_1
                     rw[r_prime_post_1, ← mod_two_Eq_one_iff] at r_is_negative_post
                     simp_all























               · intro hup hvp
                 sorry
         · simp[hs, Choice.zero]
           constructor
           · sorry
           · constructor
             · sorry
             · sorry
    · simp[h]
      unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
      progress*
      · simp_all
        intro i a
        simp[Choice.zero]
        apply lt_trans (r_post_2  i a)
        simp
      ·  by_cases hs :correct_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt.val = 1#u8
         · simp[hs, Choice.one]
           constructor
           · sorry
           · constructor
             · sorry
             · sorry
         · simp[hs, Choice.zero]
           constructor
           · sorry
           · sorry







































end curve25519_dalek.field.FieldElement51
