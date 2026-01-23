/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Curve

import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Field.FieldElement51.PowP58
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SQRT_M1
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero
/-! # Spec Theorem for `FieldElement51::sqrt_ratio_i`

Specification and proof for `FieldElement51::sqrt_ratio_i`.

This function computes a nonnegative square root of u/v or i*u/v (where i = sqrt(-1) = SQRT_M1 constant),
returning a flag indicating which case occurred and handling zero inputs specially.

**Source**: curve25519-dalek/src/field.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.field.FieldElement51

theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔  a % n = 0 := by simp [Nat.ModEq]

theorem modEq_one_iff (a : ℕ) : a ≡ 1 [MOD p] ↔  a % p = 1 := by
  simp [Nat.ModEq]
  have :1 % p= 1:= by unfold p; decide
  rw[this]

theorem mod_two_Eq_one_iff (a : ℕ) : a ≡ 1 [MOD 2] ↔  a % 2 = 1 := by simp [Nat.ModEq]

theorem mod_Eq_one_iff (a : ℕ) : a ≡ 1 [MOD 2] ↔  ¬(a ≡ 0 [MOD 2]) := by simp [Nat.ModEq]

theorem mod_two_zero_or_one (a : ℕ) : (a ≡ 1 [MOD 2]) ∨  (a ≡ 0 [MOD 2]) := by
  simp [Nat.ModEq]
  grind

theorem pow_add_one (a n : ℕ) : a ^ n * a = a^ (n + 1) := by
  grind

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

theorem nat_sqrt_m1_sq_of_add_modeq_zero {a b : ℕ}
  (h : a + b ≡ 0 [MOD p]) :
  a ≡ (Field51_as_Nat constants.SQRT_M1) ^ 2 * b [MOD p] := by
  have h_sqrt_eq : (Field51_as_Nat constants.SQRT_M1) ^ 2 % p = p - 1 :=
    constants.SQRT_M1_spec
  have h_sqrt_mod : (Field51_as_Nat constants.SQRT_M1) ^ 2 ≡ p - 1 [MOD p] := by
    simp [Nat.ModEq, h_sqrt_eq]
  have h1 : (Field51_as_Nat constants.SQRT_M1) ^ 2 * b ≡ (p - 1) * b [MOD p] := by
    exact h_sqrt_mod.mul_right b
  have hp_pos : 1 ≤ p := by unfold p; simp
  have h2 : (p - 1) * b = p * b - b := by
      rw [Nat.sub_mul _ _ _, Nat.one_mul]
  have h3 : 0 ≡ p * b  [MOD p] := by
      simp [Nat.ModEq]
  have : p *b =  b + (p-1) *b  := by unfold p; grind
  rw[this] at h3
  have h4:=h3.add_left a
  have : a + (b + (p - 1) * b) =(a + b) + (p - 1) * b := by grind
  simp[this] at h4
  have h5:=h.add_right ((p - 1) * b)
  have h6:=h4.trans h5
  simp at h6
  exact h6.trans (h1.symm)

theorem eq_to_bytes_eq_Field51_as_Nat
    {u v : backend.serial.u64.field.FieldElement51}
    (h : u.to_bytes = v.to_bytes) :
  Field51_as_Nat u % p = Field51_as_Nat v % p := by
  classical
  obtain ⟨ru, hu, hru_mod, _⟩ := to_bytes_spec u
  obtain ⟨rv, hv, hrv_mod, _⟩ := to_bytes_spec v
  have hrr : ru = rv := by
    have : ok ru = ok rv := by simpa [hu, hv] using h
    cases this
    rfl
  have huv_mod : Nat.ModEq p (Field51_as_Nat u) (Field51_as_Nat v) := by
    have h1 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat u) := by
      simpa [hrr] using hru_mod
    have h2 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat v) := hrv_mod
    exact (Nat.ModEq.symm h1).trans h2
  simpa [Nat.ModEq] using huv_mod

lemma zero_mod_lt_zero {u p : ℕ} (hu_lt : u < p) (hu_mod : u ≡ 0 [MOD p]) :
    u = 0 := by
    rw[Nat.ModEq] at hu_mod
    simp at hu_mod
    have : u % p = u := Nat.mod_eq_of_lt hu_lt
    rw[hu_mod] at this
    simp at this
    exact this

theorem to_bytes_zero_of_Field51_as_Nat_zero
    {u : backend.serial.u64.field.FieldElement51}
    (h : Field51_as_Nat u % p = 0) :
   u.to_bytes = Array.repeat 32#usize 0#u8  := by
  classical
  obtain ⟨ru, hu, hru_mod, hru_lt⟩ := to_bytes_spec u
  rw[← modEq_zero_iff] at h
  have := hru_mod.trans h
  have h_bytes_zero:= zero_mod_lt_zero hru_lt this
  obtain ⟨c, c_ok, hc ⟩  := is_zero_spec u
  have hru_eq : ru = Array.repeat 32#usize 0#u8 := by
    unfold U8x32_as_Nat at h_bytes_zero
    simp_all
    apply Subtype.ext
    apply List.ext_getElem
    repeat simp
    intro i hi _
    have hi_val := h_bytes_zero i hi
    interval_cases i
    all_goals simp [Array.repeat, List.replicate]; scalar_tac
  rw [← hru_eq]
  exact hu

theorem mod_sq_mod (a p : ℕ) : (a % p) ^ 2 ≡ a ^ 2 [MOD p] := by
  exact (Nat.mod_modEq a p).pow 2

theorem mod_mul_mod (a b : ℕ) : (a % p) * (b % p) ≡ a * b [MOD p] := by
 exact ((Nat.mod_modEq a p).mul_right (b % p)).trans  ((Nat.mod_modEq b p).mul_left a)

theorem mod_sq_mod_mul (a b p : ℕ) : (a % p) ^ 2 * b ≡ a ^ 2 * b[MOD p] := by
  exact (Nat.ModEq.mul_right  b (mod_sq_mod a p))

theorem mod_sq_mod_mul_eq (a b p : ℕ) : ((a % p) ^ 2 * b) % p = (a ^ 2 * b) % p := by
  rw[← Nat.ModEq]
  apply mod_sq_mod_mul


theorem mod_sq_mod_eq (a p : ℕ) : ((a % p) ^ 2) % p = (a ^ 2) % p := by
  exact (Nat.mod_modEq a p).pow 2

theorem sq_mod_eq_mod_sq (a p : ℕ) : ((a % p) ^ 2) % p = (a ^ 2) % p :=
  mod_sq_mod_eq a p

theorem aux1 {a b c : ℕ} : a * b * c = a * c * b := by grind

theorem SQRT_M1_not_square (x : ℕ) :
  ¬ (x ^ 4 ≡ p - 1 [MOD p]) := by
  intro hx
  by_cases hpx: p ∣ x
  · -- BEGIN TASK
    rw[← Nat.modEq_zero_iff_dvd] at hpx
    have := (hpx.pow 4).symm
    have := this.trans hx
    unfold p at this
    rw[Nat.ModEq] at this
    simp at this
    -- END TASK
  ·  -- BEGIN TASK
    have eq1:= hx.pow ((p-1)/4)
    rw[← pow_mul] at eq1
    have : 4 * ((p - 1) / 4) = p -1 := by
      unfold p
      simp
    rw[this] at eq1

    have := coprime_of_prime_not_dvd prime_25519 hpx
    have fermat:= (Nat.ModEq.pow_card_sub_one_eq_one prime_25519 this ).symm.trans eq1
    have :(p-1)^2 ≡ 1[MOD p]:= by
      have : (p - 1) ^ 2 = p*(p - 2)+1 := by
        unfold p
        simp
      rw[this, Nat.ModEq]
      norm_num
    have := this.pow  (2 ^ 252 - 3)
    rw[← pow_mul, (by simp :  1^ (2 ^ 252 - 3) =1)] at this
    have := this.mul_right (p-1)
    rw[pow_add_one, (by simp : 1 * (p-1)= p-1)] at this
    have eq1:  2* (2 ^ 252 - 3)+1 =(p-1)/4  := by
      unfold p
      simp
    rw[eq1] at this
    have := fermat.trans this
    unfold p at this
    rw[Nat.ModEq] at this
    simp at this
    -- END TASK

lemma gcd_one_of_p {a : ℕ}
   (ha : ¬a ≡ 0 [MOD p]) : p.gcd a = 1 := by
    rw[Nat.modEq_zero_iff_dvd] at ha
    have := coprime_of_prime_not_dvd prime_25519 ha
    apply Nat.Coprime.symm at this
    apply Nat.Coprime.gcd_eq_one at this
    apply this

lemma zero_of_mul_SQRT_M1_zero {a : ℕ} (ha : a * Field51_as_Nat constants.SQRT_M1 ≡ 0 [MOD p]) :
  a ≡ 0 [MOD p] := by
  have eq:= ha.mul_right (Field51_as_Nat constants.SQRT_M1)
  simp[mul_assoc] at eq
  have : Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat constants.SQRT_M1 ≡ p-1 [MOD p] := by
    unfold constants.SQRT_M1
    decide
  have eq:= ((this.mul_left a).symm.trans eq).add_right a
  rw[(by simp : 0 +a =a)] at eq
  have : a * (p - 1) + a= p * a := by
    unfold p
    grind
  rw[this] at eq
  have : p * a ≡ 0  [MOD p] := by
    rw[Nat.ModEq]
    simp
  apply eq.symm.trans this

theorem mul_zero_eq_or {a b : ℕ} {p : ℕ} (hp : p.Prime)
    (hab : a * b ≡ 0 [MOD p]) :
    a ≡ 0 [MOD p] ∨ b ≡ 0 [MOD p] := by
  rw [Nat.ModEq] at hab
  have h_dvd : p ∣ a * b := Nat.dvd_of_mod_eq_zero hab
  obtain ha | hb := hp.dvd_mul.mp h_dvd
  · left
    exact Nat.mod_eq_zero_of_dvd ha
  · right
    exact Nat.mod_eq_zero_of_dvd hb

theorem pow_div_two_eq_neg_one_or_one {a : ℕ} (ha : ¬ a ≡ 0 [MOD p]) :
    a ^ ((p -1) / 2) ≡ 1 [MOD p]∨ a ^ ((p-1) / 2) ≡ p - 1 [MOD p] := by
    have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1) ≡ 0 [MOD p] := by
      have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1)
        = a ^ ((p -1) ) + p * a ^ ((p -1) / 2) + (p-1) := by
        rw[mul_add, add_mul, (by grind : ∀ a, a * a = a^2), ← pow_mul]
        simp[← add_assoc]
        simp[add_assoc, (by grind : (p-1)* a^ ((p - 1) / 2)+ a^ ((p - 1) / 2)= ((p-1)+1)*a^ ((p - 1) / 2))]
        have : p-1 +1 =p := by unfold p; scalar_tac
        rw[this]
        have : (p-1)/2 *2 =p-1 := by unfold p; scalar_tac
        rw[this]
      rw[this]
      rw[Nat.modEq_zero_iff_dvd] at ha
      have := coprime_of_prime_not_dvd prime_25519 ha
      have fermat:= Nat.ModEq.pow_card_sub_one_eq_one prime_25519 this
      have :p * a ^ ((p - 1) / 2) ≡ 0 [MOD p] := by
        rw[Nat.modEq_zero_iff_dvd]
        simp
      have := (fermat.add this).add_right (p-1)
      apply this.trans
      have : 1 + 0 + (p - 1) =p := by unfold p; scalar_tac
      rw[this]
      rw[Nat.modEq_zero_iff_dvd]
    have := mul_zero_eq_or prime_25519 this
    rcases this with r | l
    · have r:= r.add_right 1
      rw[add_assoc] at r
      have : p-1 +1 =p := by unfold p; scalar_tac
      simp[this] at r
      simp[r]
    · have r:= l.add_right (p-1)
      rw[add_assoc] at r
      have :  1 + (p-1) =p := by unfold p; scalar_tac
      simp[this] at r
      simp[r]

theorem pow_div_four_eq_four_cases {a : ℕ} (ha : ¬ a ≡ 0 [MOD p]) :
    a ^ ((p -1) / 4) ≡ 1 [MOD p] ∨
    a ^ ((p-1) / 4) ≡ Field51_as_Nat constants.SQRT_M1 [MOD p] ∨
    a ^ ((p-1) / 4) ≡ (Field51_as_Nat constants.SQRT_M1)^2 [MOD p] ∨
    a ^ ((p-1) / 4) ≡ (Field51_as_Nat constants.SQRT_M1)^3 [MOD p] := by
  have eq1:  (a ^ ((p -1) / 4) + (p-1)) *
          (a ^ ((p -1) / 4) + 1)
           =
          a ^ ((p -1)/2 ) + p * a ^ ((p -1) / 4) + (p-1)
           := by
        rw[mul_add, add_mul, (by grind : ∀ a, a * a = a^2), ← pow_mul]
        simp[← add_assoc]
        simp[add_assoc, (by grind : (p-1)* a^ ((p - 1) / 4)+ a^ ((p - 1) / 4)= ((p-1)+1)*a^ ((p - 1) / 4))]
        have : p-1 +1 =p := by unfold p; scalar_tac
        rw[this]
        have : (p-1)/4 *2 =(p-1)/2 := by unfold p; scalar_tac
        rw[this]

  have eq2:  (a ^ ((p -1) / 4) + (p-1)* (Field51_as_Nat constants.SQRT_M1)) *
          (a ^ ((p -1) / 4) + Field51_as_Nat constants.SQRT_M1)
           =
          a ^ ((p -1)/2 ) + p * a ^ ((p -1) / 4) *(Field51_as_Nat constants.SQRT_M1) + (p-1) * Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat constants.SQRT_M1
           := by
        rw[mul_add, add_mul,add_mul, (by grind : ∀ a, a * a = a^2), ← pow_mul]
        rw[← add_assoc]
        simp[add_assoc, (by grind : (p-1)*(Field51_as_Nat constants.SQRT_M1) * a^ ((p - 1) / 4)+ a^ ((p - 1) / 4) * Field51_as_Nat constants.SQRT_M1
        = ((p-1)+1)*a^ ((p - 1) / 4) * Field51_as_Nat constants.SQRT_M1)]
        have : p-1 +1 =p := by unfold p; scalar_tac
        rw[this]
        have : (p-1)/4 *2 =(p-1)/2 := by unfold p; scalar_tac
        rw[this, ← add_assoc]
  have : (a ^ ((p -1) / 4) + (p-1)) *
          (a ^ ((p -1) / 4) + 1) *
          (a ^ ((p -1) / 4) + (p-1)* (Field51_as_Nat constants.SQRT_M1)) *
          (a ^ ((p -1) / 4) + Field51_as_Nat constants.SQRT_M1)
          ≡ 0 [MOD p] := by
          simp[eq1, mul_assoc, eq2]
          have eq1:a ^ ((p -1)/2 ) + p * a ^ ((p -1) / 4) + (p-1) ≡
            a ^ ((p -1)/2 ) + (p-1)
            [MOD p] := by
            simp[Nat.modEq_iff_dvd]
          have : a ^ ((p - 1) / 2) + p * (a ^ ((p - 1) / 4) * Field51_as_Nat constants.SQRT_M1) +
            (p - 1) * (Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat constants.SQRT_M1) ≡
            a ^ ((p -1)/2 ) + 1
            [MOD p] := by
            have :(p - 1) * (Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat constants.SQRT_M1) ≡ 1 [MOD p]:= by
              unfold constants.SQRT_M1
              decide
            have :=this.add_left (a ^ ((p - 1) / 2) + p * (a ^ ((p - 1) / 4) * Field51_as_Nat constants.SQRT_M1))
            apply Nat.ModEq.trans this
            simp[Nat.modEq_iff_dvd]

          apply (eq1.mul this).trans
          have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1) ≡ 0 [MOD p] := by
            have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1)
              = a ^ ((p -1) ) + p * a ^ ((p -1) / 2) + (p-1) := by
              rw[mul_add, add_mul, (by grind : ∀ a, a * a = a^2), ← pow_mul]
              simp[← add_assoc]
              simp[add_assoc, (by grind : (p-1)* a^ ((p - 1) / 2)+ a^ ((p - 1) / 2)= ((p-1)+1)*a^ ((p - 1) / 2))]
              have : p-1 +1 =p := by unfold p; scalar_tac
              rw[this]
              have : (p-1)/2 *2 =p-1 := by unfold p; scalar_tac
              rw[this]
            rw[this]
            rw[Nat.modEq_zero_iff_dvd] at ha
            have := coprime_of_prime_not_dvd prime_25519 ha
            have fermat:= Nat.ModEq.pow_card_sub_one_eq_one prime_25519 this
            have :p * a ^ ((p - 1) / 2) ≡ 0 [MOD p] := by
              rw[Nat.modEq_zero_iff_dvd]
              simp
            have := (fermat.add this).add_right (p-1)
            apply this.trans
            have : 1 + 0 + (p - 1) =p := by unfold p; scalar_tac
            rw[this]
            rw[Nat.modEq_zero_iff_dvd]
          apply this
  have := mul_zero_eq_or prime_25519 this
  rcases this with hl | hl
  · have := mul_zero_eq_or prime_25519 hl
    rcases this with hl | hl
    · have := mul_zero_eq_or prime_25519 hl
      rcases this with hl | hl
      · have r:= hl.add_right 1
        rw[add_assoc] at r
        have : p-1 +1 =p := by unfold p; scalar_tac
        simp[this] at r
        simp[r]
      · have r:= hl.add_right (p-1)
        rw[add_assoc] at r
        have :  1 + (p-1) =p := by unfold p; scalar_tac
        simp[this] at r
        have :p - 1  ≡Field51_as_Nat constants.SQRT_M1 ^2  [MOD p]:= by
              unfold constants.SQRT_M1
              decide
        have r:= r.trans this
        simp[r]
    · have r:= hl.add_right (Field51_as_Nat constants.SQRT_M1)
      rw[add_assoc] at r
      have : (p-1) * Field51_as_Nat constants.SQRT_M1 + Field51_as_Nat constants.SQRT_M1 =p * (Field51_as_Nat constants.SQRT_M1) := by unfold p; scalar_tac
      simp[this] at r
      simp[r]
  · have r:= hl.add_right ((p-1)*Field51_as_Nat constants.SQRT_M1)
    rw[add_assoc] at r
    have :  Field51_as_Nat constants.SQRT_M1 + (p-1) * Field51_as_Nat constants.SQRT_M1=p * (Field51_as_Nat constants.SQRT_M1) := by unfold p; scalar_tac
    simp[this] at r
    have :(p - 1)* (Field51_as_Nat constants.SQRT_M1)  ≡Field51_as_Nat constants.SQRT_M1 ^3  [MOD p]:= by
              unfold constants.SQRT_M1
              decide
    have r:= r.trans this
    simp[r]

set_option maxHeartbeats 2000000000 in
-- scalar_tac haevy
lemma eq_U8x32_as_Nat_eq {a b : Aeneas.Std.Array U8 32#usize}
    (hab : U8x32_as_Nat a = U8x32_as_Nat b) : a = b := by
    apply Subtype.ext
    apply List.ext_getElem
    repeat simp
    intro i h1 h2
    interval_cases i
    all_goals(simp[U8x32_as_Nat,Finset.sum_range_succ] at hab; scalar_tac)

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

/- **Spec and proof concerning `field.FieldElement51.sqrt_ratio_i`**:
- No panic for field element inputs u and v (always returns (c, r) successfully)
- The result satisfies exactly one of four mutually exclusive cases:
  1. If u ≡ 0 (mod p), then c.val = 1 and r ≡ 0 (mod p)
  2. If u ≢ 0 (mod p) and v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
  3. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 1 and r^2 ≡ u * v^(-1) (mod p)
  4. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ¬∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 0 and r^2 ≡ SQRT_M1 * u * v^(-1) (mod p)
-/

set_option maxHeartbeats  1000000000000 in
-- progress heavy

@[progress]
theorem sqrt_ratio_i_spec
    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val ≤ 2 ^ 51 - 1)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 51 - 1) :
    sqrt_ratio_i u v ⦃ c r =>
      let u_nat := Field51_as_Nat u % p;
      let v_nat := Field51_as_Nat v % p;
      let r_nat := Field51_as_Nat r % p;
      let i_nat := Field51_as_Nat backend.serial.u64.constants.SQRT_M1 % p;

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
    ⦄ := by
  sorry

end curve25519_dalek.field.FieldElement51
