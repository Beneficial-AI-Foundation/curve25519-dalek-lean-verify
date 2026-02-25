/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Curve

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



open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.field.FieldElement51

theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔  a % n = 0 := by simp [Nat.ModEq]

theorem modEq_one_iff (a : ℕ) : a ≡ 1 [MOD p] ↔  a % p = 1 := by
  simp only [Nat.ModEq]
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
  simp only [zero_mul] at h2
  have h1' : a * a + a * b ≡ 0 [MOD p] := by simpa [Nat.mul_add, pow_two] using h1
  have h2' : a * b + b * b ≡ 0 [MOD p] := by simpa [Nat.add_mul, pow_two] using h2
  have hsum : a * b + a * a ≡ a * b + b * b [MOD p] := by
    rw[add_comm]
    apply Nat.ModEq.symm at h2'
    apply Nat.ModEq.trans h1' h2'
  apply Nat.ModEq.add_left_cancel' at hsum
  simp only [pow_two]
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
  simp only [add_zero, this] at h4
  have h5:=h.add_right ((p - 1) * b)
  have h6:=h4.trans h5
  simp at h6
  exact h6.trans (h1.symm)

theorem eq_to_bytes_eq_Field51_as_Nat
    {u v : backend.serial.u64.field.FieldElement51}
    (h : u.to_bytes = v.to_bytes) :
  Field51_as_Nat u % p = Field51_as_Nat v % p := by
  classical
  obtain ⟨ru, hu, hru_mod, _⟩ := spec_imp_exists (to_bytes_spec u)
  obtain ⟨rv, hv, hrv_mod, _⟩ := spec_imp_exists (to_bytes_spec v)
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
    simp only [Nat.zero_mod] at hu_mod
    have : u % p = u := Nat.mod_eq_of_lt hu_lt
    rw[hu_mod] at this
    simp only [ReduceNat.reduceNatEq] at this
    exact this

theorem to_bytes_zero_of_Field51_as_Nat_zero
    {u : backend.serial.u64.field.FieldElement51}
    (h : Field51_as_Nat u % p = 0) :
   u.to_bytes = Array.repeat 32#usize 0#u8  := by
  classical
  obtain ⟨ru, hu, hru_mod, hru_lt⟩ := spec_imp_exists (to_bytes_spec u)
  rw[← modEq_zero_iff] at h
  have := hru_mod.trans h
  have h_bytes_zero:= zero_mod_lt_zero hru_lt this
  obtain ⟨c, c_ok, hc ⟩  := spec_imp_exists (is_zero_spec u)
  have hru_eq : ru = Array.repeat 32#usize 0#u8 := by
    unfold U8x32_as_Nat at h_bytes_zero
    simp_all only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_eq_zero_iff,
      Finset.mem_range, List.Vector.length_val, UScalar.ofNat_val_eq, getElem?_pos,
      Option.getD_some, mul_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_or,
      false_and]
    apply Subtype.ext
    apply List.ext_getElem
    repeat simp only [List.Vector.length_val, UScalar.ofNat_val_eq]
    intro i hi _
    have hi_val := h_bytes_zero i hi
    interval_cases i
    all_goals simp only [Array.repeat, UScalar.ofNat_val_eq, List.replicate, List.getElem_cons_succ,
      List.getElem_cons_zero]; scalar_tac
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
  simp only [mul_assoc, zero_mul] at eq
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
        simp only [mul_one, ← add_assoc, Nat.add_right_cancel_iff]
        simp only [add_assoc,
          (by grind :
              (p - 1) * a ^ ((p - 1) / 2) + a ^ ((p - 1) / 2) = ((p - 1) + 1) * a ^ ((p - 1) / 2))]
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
        simp only [mul_one, ← add_assoc, Nat.add_right_cancel_iff]
        simp only [add_assoc,
          (by grind :
              (p - 1) * a ^ ((p - 1) / 4) + a ^ ((p - 1) / 4) = ((p - 1) + 1) * a ^ ((p - 1) / 4))]
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
        simp only [add_assoc,
          (by grind :
              (p - 1) * (Field51_as_Nat constants.SQRT_M1) * a ^ ((p - 1) / 4) +
                  a ^ ((p - 1) / 4) * Field51_as_Nat constants.SQRT_M1 =
                ((p - 1) + 1) * a ^ ((p - 1) / 4) * Field51_as_Nat constants.SQRT_M1)]
        have : p-1 +1 =p := by unfold p; scalar_tac
        rw [this]
        have : (p-1)/4 *2 =(p-1)/2 := by unfold p; scalar_tac
        rw[this, ← add_assoc]
  have : (a ^ ((p -1) / 4) + (p-1)) *
          (a ^ ((p -1) / 4) + 1) *
          (a ^ ((p -1) / 4) + (p-1)* (Field51_as_Nat constants.SQRT_M1)) *
          (a ^ ((p -1) / 4) + Field51_as_Nat constants.SQRT_M1)
          ≡ 0 [MOD p] := by
          simp only [eq1, mul_assoc, eq2]
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
              simp only [mul_one, ← add_assoc, Nat.add_right_cancel_iff]
              simp only [add_assoc,
                (by grind :
                    (p - 1) * a ^ ((p - 1) / 2) + a ^ ((p - 1) / 2) =
                      ((p - 1) + 1) * a ^ ((p - 1) / 2))]
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
        simp only [this, zero_add, Nat.add_modulus_modEq_iff] at r
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
    simp only [this, zero_add, Nat.add_modulus_mul_modEq_iff] at r
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
    repeat simp only [List.Vector.length_val, UScalar.ofNat_val_eq]
    intro i h1 h2
    interval_cases i
    all_goals(simp only [U8x32_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
      List.Vector.length_val, UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem?_pos, Option.getD_some,
      one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
      Nat.lt_add_one] at hab; scalar_tac)

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

private theorem nonneg_of_neg_mod_p (a b : ℕ)
    (h_sum : (a + b) % p = 0) (h_a_odd : a % p % 2 = 1) :
    b % p % 2 = 0 := by
  have hp_pos : 0 < p := by unfold p; omega
  have hp_odd : p % 2 = 1 := by unfold p; decide
  have ha_lt := Nat.mod_lt a hp_pos
  have hb_lt := Nat.mod_lt b hp_pos
  rw [Nat.add_mod] at h_sum
  have h_cases : a % p + b % p = 0 ∨ a % p + b % p = p := by
    by_cases h_lt : a % p + b % p < p
    · left
      have h_mod : (a % p + b % p) % p = a % p + b % p := Nat.mod_eq_of_lt h_lt
      rw [h_mod] at h_sum
      exact h_sum
    · right
      have h_ge : p ≤ a % p + b % p := by omega
      have h_rw : a % p + b % p = (a % p + b % p - p) + p := by omega
      rw [h_rw] at h_sum
      rw [Nat.add_mod_right] at h_sum
      have h_sub_lt : a % p + b % p - p < p := by omega
      have h_sub_mod : (a % p + b % p - p) % p = a % p + b % p - p := Nat.mod_eq_of_lt h_sub_lt
      rw [h_sub_mod] at h_sum
      omega
  rcases h_cases with h | h
  · omega
  · have h1 : (a % p + b % p) % 2 = 1 := by rw [h]; exact hp_odd
    rw [Nat.add_mod, h_a_odd] at h1
    have := Nat.mod_two_eq_zero_or_one (b % p)
    omega

/-- After `conditional_negate`, the result `r2` is always non-negative (even mod p). -/
private theorem conditional_negate_nonneg
    (r1 x r2 : backend.serial.u64.field.FieldElement51)
    (r_is_negative : subtle.Choice)
    (r_is_negative_post : r_is_negative.val = 1#u8 ↔ Field51_as_Nat r1 % p % 2 = 1)
    (x_post_1 : (Field51_as_Nat r1 + Field51_as_Nat x) % p = 0)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then x[i]! else r1[i]!) :
    Field51_as_Nat r2 % p % 2 = 0 := by
  by_cases h : r_is_negative.val = 1#u8
  · simp [h] at r2_post
    have : Field51_as_Nat r2 = Field51_as_Nat x := by
      simp [Field51_as_Nat, Finset.sum_range_succ]; simp_all
    rw [this]
    exact nonneg_of_neg_mod_p (Field51_as_Nat r1) (Field51_as_Nat x) x_post_1
      (r_is_negative_post.mp h)
  · simp [h] at r2_post
    have : Field51_as_Nat r2 = Field51_as_Nat r1 := by
      simp [Field51_as_Nat, Finset.sum_range_succ]; simp_all
    rw [this]
    have := Nat.mod_two_eq_zero_or_one (Field51_as_Nat r1 % p)
    have := mt r_is_negative_post.mpr h
    omega

set_option maxHeartbeats 400000 in -- nested and non trivial proof.
theorem sqrt_ratio_i_spec'
    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val ≤ 2 ^ 52 - 1)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 52 - 1) :
    ∃ c, sqrt_ratio_i u v = ok c ∧
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat c.2 % p
    let i_nat := Field51_as_Nat backend.serial.u64.constants.SQRT_M1 % p
    -- Case 1: u is zero
    (u_nat = 0 →
    c.1.val = 1#u8 ∧ r_nat = 0 ∧
    (∀ i < 5,  c.2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    -- Case 2: u is nonzero and v is zero
    (u_nat ≠ 0 ∧ v_nat = 0 →
    c.1.val = 0#u8 ∧ r_nat = 0 ∧
    (∀ i < 5,  c.2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    -- Case 3: u and v are nonzero and u/v is a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.1.val = 1#u8 ∧ (r_nat ^ 2 * v_nat) % p = u_nat ∧
    (∀ i < 5,  c.2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    -- Case 4: u and v are nonzero and u/v is not a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (¬(∃ x : Nat, (x^2 * v_nat) % p = u_nat)) →
    c.1.val = 0#u8 ∧ (r_nat ^2 * v_nat) % p = (i_nat * u_nat) % p ∧
    (∀ i < 5,  c.2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    -- Non-negativity of the result
    (r_nat % 2 = 0)
    := by
    apply spec_imp_exists
    unfold sqrt_ratio_i subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
    progress*
    · grind only [#c967]
    · grind only [#c51c]
    · grind only [#c967]
    · grind only [#fd6c]
    · grind only [#5f74]
    · grind only [#c967]
    · grind only [#ca7d]
    · grind only [#fd6c]
    · grind only [#ca7d]
    · grind only [#a5fc]
    · grind only [#74f6]
    · grind only [#e9d5]
    · grind only [#79e1]
    · grind only [#e2b0]
    · grind only [#c967]
    · grind only [#e8a6]
    · grind only [#ca7d]
    · grind only [#134e]
    · unfold constants.SQRT_M1
      try decide
    · unfold constants.SQRT_M1
      try decide
    · grind only [#e2b0]

    have eq1_mod: (Field51_as_Nat r_prime)^2 *  (Field51_as_Nat v)
      ≡ (Field51_as_Nat constants.SQRT_M1) ^2 * (Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35))
      [MOD p]:= by
      have := r_prime_post_1.pow 2
      rw[mul_pow] at this
      have := this.mul_right (Field51_as_Nat v)
      apply this.trans
      rw[mul_assoc]
      apply Nat.ModEq.mul_left
      have := Nat.ModEq.pow 2 r_post_1
      rw[mul_pow] at this
      have := this.mul_right (Field51_as_Nat v)
      apply this.trans
      rw[← Nat.ModEq] at fe4_post_1
      have eq1:= fe4_post_1.pow 2
      rw[← pow_mul] at eq1
      have :=fe3_post_1.pow ((2 ^ 252 - 3) * 2)
      have eq2:= eq1.trans  this
      rw[mul_pow] at eq2
      have := fe_post_1.mul_right (Field51_as_Nat v)
      have eq_v3:= v3_post_1.trans this
      rw[pow_add_one] at eq_v3
      have := eq_v3.pow 2
      rw[← pow_mul] at this
      have := fe1_post_1.trans  this
      have := this.mul_right (Field51_as_Nat v)
      rw[pow_add_one] at this
      have := v7_post_1.trans  this
      have := this.pow ((2 ^ 252 - 3) * 2)
      rw[← pow_mul] at this
      have := this.mul_left  ((Field51_as_Nat u)^ ((2 ^ 252 - 3) * 2))
      have eq3:= eq2.trans  this
      have := eq_v3.mul_left (Field51_as_Nat u)
      have := fe2_post_1.trans  this
      have eq4:= this.pow 2
      rw[mul_pow] at eq4
      have := eq4.mul  eq3
      have := this.mul_right (Field51_as_Nat v)
      apply this.trans
      have :  Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
       (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2))) * Field51_as_Nat v
        =  (Field51_as_Nat u ^ 2 * Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2)) *
        ((Field51_as_Nat v ^ (2 + 1)) ^ 2 *
         Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2)) *
        Field51_as_Nat v)
          := by
          simp
          ring
      rw[this]
      clear this
      rw[← pow_add, ← pow_mul, ← pow_add, pow_add_one,
      (by simp : (2 + 1) * 2 + ((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2) + 1= 7 * 2 ^ 253 - 35)]
    have check_eq_v: Field51_as_Nat check ≡    Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) [MOD p] := by
      apply check_post_1.trans
      have := fe5_post_1.mul_left (Field51_as_Nat v)
      apply this.trans
      have := r_post_1.pow 2
      rw[mul_pow] at this
      have := this.mul_left (Field51_as_Nat v)
      apply this.trans
      rw[← Nat.ModEq] at fe4_post_1
      have eq1:= Nat.ModEq.pow 2 fe4_post_1
      rw[← pow_mul] at eq1
      have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) fe3_post_1
      have eq2:= Nat.ModEq.trans eq1 this
      rw[mul_pow] at eq2
      have := Nat.ModEq.mul_right (Field51_as_Nat v) fe_post_1
      have eq_v3:= Nat.ModEq.trans v3_post_1 this
      rw[pow_add_one] at eq_v3
      have := Nat.ModEq.pow 2 eq_v3
      rw[← pow_mul] at this
      have := Nat.ModEq.trans fe1_post_1 this
      have := Nat.ModEq.mul_right (Field51_as_Nat v) this
      rw[pow_add_one] at this
      have := Nat.ModEq.trans v7_post_1 this
      have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) this
      rw[← pow_mul] at this
      have := Nat.ModEq.mul_left  ((Field51_as_Nat u)^ ((2 ^ 252 - 3) * 2)) this
      have eq3:= Nat.ModEq.trans eq2 this
      have := Nat.ModEq.mul_left (Field51_as_Nat u) eq_v3
      have := Nat.ModEq.trans fe2_post_1 this
      have eq4:= Nat.ModEq.pow 2 this
      rw[mul_pow] at eq4
      have := Nat.ModEq.mul eq4 eq3
      have := Nat.ModEq.mul_left (Field51_as_Nat v) this
      apply Nat.ModEq.trans this
      have :  Field51_as_Nat v *
        (Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
        (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2))))
        =  Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35)
          := by
          simp
          ring
      rw[this]
    have check_eq_mod: (Field51_as_Nat r_prime)^2 *  (Field51_as_Nat v)
      ≡ (Field51_as_Nat constants.SQRT_M1) ^2 *Field51_as_Nat check [MOD p] := by
      have := Nat.ModEq.mul_left ((Field51_as_Nat constants.SQRT_M1) ^2) check_eq_v
      apply Nat.ModEq.trans eq1_mod
      apply Nat.ModEq.symm this
    have :=nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1
    have check_eq_r_v:= check_post_1.trans (fe5_post_1.mul_left (Field51_as_Nat v))
    rw[mul_comm] at check_eq_r_v
    by_cases first_choice :  flipped_sign_sqrt.val = 1#u8
    · simp only [first_choice, true_or, ↓reduceIte, or_true, bind_tc_ok, Array.getElem!_Nat_eq,
      List.getElem!_eq_getElem?_getD, Nat.reducePow, Nat.add_one_sub_one, ne_eq, and_imp,
      Nat.mul_mod_mod, forall_exists_index, not_exists, Nat.mod_mul_mod]
      progress*
      · --
        
        sorry
      · sorry

    · sorry

    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · grind
    -- · unfold constants.SQRT_M1
    --   decide
    -- · unfold constants.SQRT_M1
    --   decide
    -- · grind
    -- · -- BEGIN TASK
    --   have eq1_mod: (Field51_as_Nat r_prime)^2 *  (Field51_as_Nat v)
    --     ≡ (Field51_as_Nat constants.SQRT_M1) ^2 * (Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35))
    --     [MOD p]:= by
    --     have := r_prime_post_1.pow 2
    --     rw[mul_pow] at this
    --     have := this.mul_right (Field51_as_Nat v)
    --     apply this.trans
    --     rw[mul_assoc]
    --     apply Nat.ModEq.mul_left
    --     have := Nat.ModEq.pow 2 r_post_1
    --     rw[mul_pow] at this
    --     have := this.mul_right (Field51_as_Nat v)
    --     apply this.trans
    --     rw[← Nat.ModEq] at fe4_post_1
    --     have eq1:= fe4_post_1.pow 2
    --     rw[← pow_mul] at eq1
    --     have :=fe3_post_1.pow ((2 ^ 252 - 3) * 2)
    --     have eq2:= eq1.trans  this
    --     rw[mul_pow] at eq2
    --     have := fe_post_1.mul_right (Field51_as_Nat v)
    --     have eq_v3:= v3_post_1.trans this
    --     rw[pow_add_one] at eq_v3
    --     have := eq_v3.pow 2
    --     rw[← pow_mul] at this
    --     have := fe1_post_1.trans  this
    --     have := this.mul_right (Field51_as_Nat v)
    --     rw[pow_add_one] at this
    --     have := v7_post_1.trans  this
    --     have := this.pow ((2 ^ 252 - 3) * 2)
    --     rw[← pow_mul] at this
    --     have := this.mul_left  ((Field51_as_Nat u)^ ((2 ^ 252 - 3) * 2))
    --     have eq3:= eq2.trans  this
    --     have := eq_v3.mul_left (Field51_as_Nat u)
    --     have := fe2_post_1.trans  this
    --     have eq4:= this.pow 2
    --     rw[mul_pow] at eq4
    --     have := eq4.mul  eq3
    --     have := this.mul_right (Field51_as_Nat v)
    --     apply this.trans
    --     have :  Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
    --      (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2))) * Field51_as_Nat v
    --       =  (Field51_as_Nat u ^ 2 * Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2)) *
    --       ((Field51_as_Nat v ^ (2 + 1)) ^ 2 *
    --        Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2)) *
    --       Field51_as_Nat v)
    --         := by
    --         simp
    --         ring
    --     rw[this]
    --     clear this
    --     rw[← pow_add, ← pow_mul, ← pow_add, pow_add_one,
    --     (by simp : (2 + 1) * 2 + ((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2) + 1= 7 * 2 ^ 253 - 35)]
    --   have check_eq_v: Field51_as_Nat check ≡    Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) [MOD p] := by
    --     apply check_post_1.trans
    --     have := fe5_post_1.mul_left (Field51_as_Nat v)
    --     apply this.trans
    --     have := r_post_1.pow 2
    --     rw[mul_pow] at this
    --     have := this.mul_left (Field51_as_Nat v)
    --     apply this.trans
    --     rw[← Nat.ModEq] at fe4_post_1
    --     have eq1:= Nat.ModEq.pow 2 fe4_post_1
    --     rw[← pow_mul] at eq1
    --     have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) fe3_post_1
    --     have eq2:= Nat.ModEq.trans eq1 this
    --     rw[mul_pow] at eq2
    --     have := Nat.ModEq.mul_right (Field51_as_Nat v) fe_post_1
    --     have eq_v3:= Nat.ModEq.trans v3_post_1 this
    --     rw[pow_add_one] at eq_v3
    --     have := Nat.ModEq.pow 2 eq_v3
    --     rw[← pow_mul] at this
    --     have := Nat.ModEq.trans fe1_post_1 this
    --     have := Nat.ModEq.mul_right (Field51_as_Nat v) this
    --     rw[pow_add_one] at this
    --     have := Nat.ModEq.trans v7_post_1 this
    --     have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) this
    --     rw[← pow_mul] at this
    --     have := Nat.ModEq.mul_left  ((Field51_as_Nat u)^ ((2 ^ 252 - 3) * 2)) this
    --     have eq3:= Nat.ModEq.trans eq2 this
    --     have := Nat.ModEq.mul_left (Field51_as_Nat u) eq_v3
    --     have := Nat.ModEq.trans fe2_post_1 this
    --     have eq4:= Nat.ModEq.pow 2 this
    --     rw[mul_pow] at eq4
    --     have := Nat.ModEq.mul eq4 eq3
    --     have := Nat.ModEq.mul_left (Field51_as_Nat v) this
    --     apply Nat.ModEq.trans this
    --     have :  Field51_as_Nat v *
    --       (Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
    --       (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2))))
    --       =  Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35)
    --         := by
    --         simp
    --         ring
    --     rw[this]
    --   have check_eq_mod: (Field51_as_Nat r_prime)^2 *  (Field51_as_Nat v)
    --     ≡ (Field51_as_Nat constants.SQRT_M1) ^2 *Field51_as_Nat check [MOD p] := by
    --     have := Nat.ModEq.mul_left ((Field51_as_Nat constants.SQRT_M1) ^2) check_eq_v
    --     apply Nat.ModEq.trans eq1_mod
    --     apply Nat.ModEq.symm this
    --   have :=nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1
    --   have check_eq_r_v:= check_post_1.trans (fe5_post_1.mul_left (Field51_as_Nat v))
    --   rw[mul_comm] at check_eq_r_v
    --   by_cases first_choice :  flipped_sign_sqrt.val = 1#u8
    --   · -- BEGIN TASK
    --     simp[first_choice]
    --     progress*
    --     · -- BEGIN TASK
    --       simp[Choice.one] at r1_post
    --       simp_all
    --       clear check_eq_mod check_eq_v eq1_mod
    --       grind
    --       -- END TASK
    --     · -- BEGIN TASK
    --         simp[Choice.one] at r1_post
    --         simp[Choice.one]
    --         have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
    --             simp[Field51_as_Nat, Finset.sum_range_succ]
    --             simp_all
    --         simp[← modEq_zero_iff]
    --         constructor
    --         · -- BEGIN TASK
    --           intro hu
    --           have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
    --           simp at this
    --           have := Nat.ModEq.trans fe2_post_1 this
    --           have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
    --           simp at this
    --           have := Nat.ModEq.trans r_post_1 this
    --           have := Nat.ModEq.mul_left (Field51_as_Nat constants.SQRT_M1) this
    --           have r_prime_eq0:= Nat.ModEq.trans r_prime_post_1 this
    --           simp at r_prime_eq0
    --           have : Field51_as_Nat r_prime % p % 2 = 0 := by
    --                   simp[Nat.ModEq] at r_prime_eq0
    --                   rw[r_prime_eq0]
    --           simp[r_is_negative_post] at r2_post
    --           have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
    --             simp[Field51_as_Nat, Finset.sum_range_succ]
    --             simp_all
    --           rw[this]
    --           constructor
    --           · apply  r_prime_eq0
    --           · by_cases h:Field51_as_Nat r1 % p % 2 = 1
    --             · simp_all
    --             · simp_all
    --               clear *- r_prime_post_2
    --               grind
    --           -- END TASK
    --         · -- BEGIN TASK
    --           constructor
    --           · -- BEGIN TASK
    --             intro hu hv
    --             simp_all
    --             apply hu
    --             have := Nat.ModEq.mul_right (Field51_as_Nat fe5) hv
    --             have check0:= Nat.ModEq.trans  check_post_1 this
    --             simp at check0
    --             have : flipped_sign_sqrt = Choice.one := by
    --               exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp first_choice
    --             simp[this] at flipped_sign_sqrt_post
    --             have := eq_to_bytes_eq_Field51_as_Nat  flipped_sign_sqrt_post
    --             rw[← Nat.ModEq] at this
    --             have :=  Nat.ModEq.trans (Nat.ModEq.symm this) check0
    --             have := Nat.ModEq.add_left (Field51_as_Nat u) this
    --             rw[← modEq_zero_iff] at fe6_post_1
    --             have :=  Nat.ModEq.trans (Nat.ModEq.symm this) fe6_post_1
    --             simp at this
    --             apply this
    --             -- END TASK
    --           · -- BEGIN TASK
    --             have r2_eq: (Field51_as_Nat r2 )^2 ≡ (Field51_as_Nat r_prime) ^2 [MOD p] := by
    --                   rcases (mod_two_zero_or_one (Field51_as_Nat r_prime % p)) with one | zero
    --                   · -- BEGIN TASK
    --                     rw[mod_two_Eq_one_iff] at one
    --                     simp[this, one] at r_is_negative_post
    --                     simp[r_is_negative_post] at r2_post
    --                     have : Field51_as_Nat r2 = Field51_as_Nat r_neg:= by
    --                       simp[Field51_as_Nat, Finset.sum_range_succ]
    --                       simp_all
    --                     rw[← this] at r_neg_post_1
    --                     simp_all
    --                     rw[← modEq_zero_iff] at r_neg_post_1
    --                     apply nat_sq_of_add_modeq_zero
    --                     rw[add_comm]
    --                     apply  r_neg_post_1
    --                     -- END TASK
    --                   · -- BEGIN TASK
    --                     rw[modEq_zero_iff] at zero
    --                     simp[this, zero] at r_is_negative_post
    --                     simp[r_is_negative_post] at r2_post
    --                     have : Field51_as_Nat r2 = Field51_as_Nat r_prime:= by
    --                       simp[Field51_as_Nat, Finset.sum_range_succ]
    --                       simp_all
    --                     rw[this]
    --                     -- END TASK
    --             constructor
    --             · -- BEGIN TASK
    --               intro hu hv xx hxx
    --               constructor
    --               · -- BEGIN TASK
    --                 have := Nat.ModEq.mul_right (Field51_as_Nat v) r2_eq
    --                 rw[mod_sq_mod_mul_eq, ← Nat.ModEq]
    --                 rw[← Nat.ModEq] at hxx
    --                 have := Nat.ModEq.trans this check_eq_mod
    --                 apply Nat.ModEq.trans this
    --                 have : flipped_sign_sqrt = Choice.one := by
    --                     exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp first_choice
    --                 simp[this] at flipped_sign_sqrt_post
    --                 have this:= eq_to_bytes_eq_Field51_as_Nat  flipped_sign_sqrt_post
    --                 rw[← Nat.ModEq] at this
    --                 have :=this.mul_left  (Field51_as_Nat constants.SQRT_M1 ^ 2)
    --                 rw[← modEq_zero_iff] at fe6_post_1
    --                 have :=this.trans  (nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1).symm
    --                 apply this
    --                 -- END TASK
    --               · -- BEGIN TASK
    --                 rcases (mod_two_zero_or_one (Field51_as_Nat r_prime % p)) with one | zero
    --                 · -- BEGIN TASK
    --                     intro i hi
    --                     interval_cases i
    --                     all_goals try (rw[mod_two_Eq_one_iff] at one; simp[this, one] at r_is_negative_post; simp[r_is_negative_post] at r2_post; simp_all; expand r_neg_post_2 with 5; scalar_tac)
    --                     -- END TASK
    --                 · -- BEGIN TASK
    --                     intro i hi
    --                     interval_cases i
    --                     · rw[modEq_zero_iff] at zero
    --                       simp[this, zero] at r_is_negative_post
    --                       simp[r_is_negative_post] at r2_post
    --                       simp_all
    --                       expand r_prime_post_2  with 5
    --                       scalar_tac
    --                     · rw[modEq_zero_iff] at zero
    --                       simp[this, zero] at r_is_negative_post
    --                       simp[r_is_negative_post] at r2_post
    --                       simp_all
    --                       expand r_prime_post_2  with 5
    --                       scalar_tac
    --                     · rw[modEq_zero_iff] at zero
    --                       simp[this, zero] at r_is_negative_post
    --                       simp[r_is_negative_post] at r2_post
    --                       simp_all
    --                       expand r_prime_post_2  with 5
    --                       scalar_tac
    --                     · rw[modEq_zero_iff] at zero
    --                       simp[this, zero] at r_is_negative_post
    --                       simp[r_is_negative_post] at r2_post
    --                       simp_all
    --                       expand r_prime_post_2  with 5
    --                       scalar_tac
    --                     · rw[modEq_zero_iff] at zero
    --                       simp[this, zero] at r_is_negative_post
    --                       simp[r_is_negative_post] at r2_post
    --                       simp_all
    --                       expand r_prime_post_2  with 5
    --                       scalar_tac
    --                     -- END TASK
    --               -- END TASK
    --             · -- BEGIN TASK
    --                   have : flipped_sign_sqrt = Choice.one := by
    --                     exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp first_choice
    --                   simp[this] at flipped_sign_sqrt_post
    --                   have this:= eq_to_bytes_eq_Field51_as_Nat  flipped_sign_sqrt_post
    --                   rw[← Nat.ModEq] at this
    --                   have :=this.mul_left  (Field51_as_Nat constants.SQRT_M1 ^ 2)
    --                   rw[← modEq_zero_iff] at fe6_post_1
    --                   have :=this.trans  (nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1).symm
    --                   have := check_eq_mod.trans this
    --                   constructor
    --                   · intro hu hv
    --                     use Field51_as_Nat r_prime
    --                     rw[← Nat.ModEq]
    --                     apply this
    --                   · -- Non-negativity
    --                     exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
    --                       r_is_negative_post r_neg_post_1 r2_post
    --                   -- END TASK
    --           -- END TASK
    --         -- END TASK
    --   · -- BEGIN TASK
    --     simp[first_choice]
    --     have : ¬ flipped_sign_sqrt = Choice.one := by
    --       intro h
    --       apply first_choice
    --       exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mpr h
    --     simp[this] at flipped_sign_sqrt_post
    --     have : ¬ check = fe6 := by
    --       intro h
    --       apply flipped_sign_sqrt_post
    --       rw[h]
    --     have u_m:=nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1
    --     by_cases second_choice: flipped_sign_sqrt_i.val = 1#u8
    --     · -- BEGIN TASK
    --       simp[second_choice]
    --       progress*
    --       · simp[Choice.one] at r1_post
    --         simp_all
    --         clear check_eq_mod check_eq_v eq1_mod
    --         grind
    --       · -- BEGIN TASK
    --         have : flipped_sign_sqrt_i = Choice.one := by
    --           exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp second_choice
    --         simp[this] at flipped_sign_sqrt_i_post
    --         have := eq_to_bytes_eq_Field51_as_Nat  flipped_sign_sqrt_i_post
    --         rw[← Nat.ModEq] at this
    --         have := this.trans fe7_post_1
    --         have check_1:=this.mul_left  (Field51_as_Nat constants.SQRT_M1)
    --         have :Field51_as_Nat constants.SQRT_M1 * (Field51_as_Nat fe6 * Field51_as_Nat constants.SQRT_M1) =
    --          Field51_as_Nat constants.SQRT_M1 ^2 * Field51_as_Nat fe6 := by ring
    --         rw[this] at check_1
    --         have u_eq1:= check_1.trans u_m.symm
    --         by_cases choise3 : correct_sign_sqrt.val = 1#u8
    --         · -- BEGIN TASK
    --           have : correct_sign_sqrt = Choice.one := by
    --             exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp choise3
    --           simp[this] at correct_sign_sqrt_post
    --           have := eq_to_bytes_eq_Field51_as_Nat  correct_sign_sqrt_post
    --           rw[← Nat.ModEq] at this
    --           have :=this.mul_left  (Field51_as_Nat constants.SQRT_M1)
    --           have eq_im:=this.symm.trans u_eq1
    --           simp[choise3, Choice.one]
    --           have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
    --             simp[Field51_as_Nat, Finset.sum_range_succ]
    --             simp_all
    --           simp[← modEq_zero_iff]
    --           constructor
    --           · -- BEGIN TASK
    --             intro hu
    --             have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
    --             simp at this
    --             have := Nat.ModEq.trans fe2_post_1 this
    --             have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
    --             simp at this
    --             have := Nat.ModEq.trans r_post_1 this
    --             have := Nat.ModEq.mul_left (Field51_as_Nat constants.SQRT_M1) this
    --             have r_prime_eq0:= Nat.ModEq.trans r_prime_post_1 this
    --             simp at r_prime_eq0
    --             have : Field51_as_Nat r_prime % p % 2 = 0 := by
    --                     simp[Nat.ModEq] at r_prime_eq0
    --                     rw[r_prime_eq0]
    --             simp[r_is_negative_post] at r2_post
    --             have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
    --               simp[Field51_as_Nat, Finset.sum_range_succ]
    --               simp_all
    --             rw[this]
    --             constructor
    --             · apply  r_prime_eq0
    --             · by_cases h:Field51_as_Nat r1 % p % 2 = 1
    --               · simp_all
    --               · simp_all
    --                 clear *- r_prime_post_2
    --                 grind
    --             -- END TASK
    --           · -- BEGIN TASK
    --             constructor
    --             · -- BEGIN TASK
    --               intro hu
    --               have :  ∀ i < 5, (u[i]!).val < 2 ^ 54 := by
    --                         intro i _
    --                         interval_cases i
    --                         all_goals (expand h_u_bounds with 5; scalar_tac)
    --               obtain ⟨ inv_u, inv_u_ok, inv_u_1, inv_u_2 ⟩  := invert_spec u this
    --               have : Field51_as_Nat u % p ≠ 0 := by
    --                 intro hu1
    --                 apply hu
    --                 rw[modEq_zero_iff]
    --                 apply hu1
    --               have inv_u_1:= inv_u_1 this
    --               rw[← modEq_one_iff] at inv_u_1
    --               have inv_u_1:= (mod_mul_mod (Field51_as_Nat inv_u) (Field51_as_Nat u)).symm.trans inv_u_1
    --               simp[mul_comm] at inv_u_1
    --               have u_eq:= (eq_im.mul_right (Field51_as_Nat inv_u)).trans inv_u_1
    --               have := (inv_u_1.mul_left (Field51_as_Nat constants.SQRT_M1 )).symm
    --               rw[← mul_assoc] at this
    --               have u_eq:= this.trans u_eq
    --               simp at u_eq
    --               have u_eq:= u_eq.pow 2
    --               simp at u_eq
    --               have : (Field51_as_Nat constants.SQRT_M1) ^2 ≡ p-1 [MOD p] := by
    --                 unfold constants.SQRT_M1
    --                 decide
    --               have := this.symm.trans u_eq
    --               unfold p at this
    --               rw[Nat.ModEq] at this
    --               simp at this
    --               -- END TASK
    --             · constructor
    --               · -- BEGIN TASK
    --                 intro hu
    --                 have :  ∀ i < 5, (u[i]!).val < 2 ^ 54 := by
    --                           intro i _
    --                           interval_cases i
    --                           all_goals (expand h_u_bounds with 5; scalar_tac)
    --                 obtain ⟨ inv_u, inv_u_ok, inv_u_1, inv_u_2 ⟩  := invert_spec u this
    --                 have : Field51_as_Nat u % p ≠ 0 := by
    --                   intro hu1
    --                   apply hu
    --                   rw[modEq_zero_iff]
    --                   apply hu1
    --                 have inv_u_1:= inv_u_1 this
    --                 rw[← modEq_one_iff] at inv_u_1
    --                 have inv_u_1:= (mod_mul_mod (Field51_as_Nat inv_u) (Field51_as_Nat u)).symm.trans inv_u_1
    --                 simp[mul_comm] at inv_u_1
    --                 have u_eq:= (eq_im.mul_right (Field51_as_Nat inv_u)).trans inv_u_1
    --                 have := (inv_u_1.mul_left (Field51_as_Nat constants.SQRT_M1 )).symm
    --                 rw[← mul_assoc] at this
    --                 have u_eq:= this.trans u_eq
    --                 simp at u_eq
    --                 have u_eq:= u_eq.pow 2
    --                 simp at u_eq
    --                 have : (Field51_as_Nat constants.SQRT_M1) ^2 ≡ p-1 [MOD p] := by
    --                   unfold constants.SQRT_M1
    --                   decide
    --                 have := this.symm.trans u_eq
    --                 unfold p at this
    --                 rw[Nat.ModEq] at this
    --                 simp at this
    --                 -- END TASK
    --               · -- BEGIN TASK
    --                 constructor
    --                 · intro hu
    --                   have :  ∀ i < 5, (u[i]!).val < 2 ^ 54 := by
    --                             intro i _
    --                             interval_cases i
    --                             all_goals (expand h_u_bounds with 5; scalar_tac)
    --                   obtain ⟨ inv_u, inv_u_ok, inv_u_1, inv_u_2 ⟩  := invert_spec u this
    --                   have : Field51_as_Nat u % p ≠ 0 := by
    --                     intro hu1
    --                     apply hu
    --                     rw[modEq_zero_iff]
    --                     apply hu1
    --                   have inv_u_1:= inv_u_1 this
    --                   rw[← modEq_one_iff] at inv_u_1
    --                   have inv_u_1:= (mod_mul_mod (Field51_as_Nat inv_u) (Field51_as_Nat u)).symm.trans inv_u_1
    --                   simp[mul_comm] at inv_u_1
    --                   have u_eq:= (eq_im.mul_right (Field51_as_Nat inv_u)).trans inv_u_1
    --                   have := (inv_u_1.mul_left (Field51_as_Nat constants.SQRT_M1 )).symm
    --                   rw[← mul_assoc] at this
    --                   have u_eq:= this.trans u_eq
    --                   simp at u_eq
    --                   have u_eq:= u_eq.pow 2
    --                   simp at u_eq
    --                   have : (Field51_as_Nat constants.SQRT_M1) ^2 ≡ p-1 [MOD p] := by
    --                     unfold constants.SQRT_M1
    --                     decide
    --                   have := this.symm.trans u_eq
    --                   unfold p at this
    --                   rw[Nat.ModEq] at this
    --                   simp at this
    --                   -- END TASK
    --                 · exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
    --                     r_is_negative_post r_neg_post_1 r2_post -- Non-negativity
    --             -- END TASK
    --         · -- BEGIN TASK
    --           simp[choise3, Choice.zero]
    --           have :¬ correct_sign_sqrt = Choice.one := by
    --             intro h
    --             apply choise3
    --             simp[h, Choice.one]
    --           simp[this] at correct_sign_sqrt_post
    --           have : ¬ check = u := by
    --             intro h
    --             apply correct_sign_sqrt_post
    --             rw[h]
    --           · constructor
    --             · -- BEGIN TASK
    --               intro hu
    --               rw[← modEq_zero_iff] at hu
    --               have := u_eq1.trans hu
    --               rw[mul_comm] at this
    --               have check_zero:= zero_of_mul_SQRT_M1_zero this
    --               have := u_m.symm.trans hu
    --               rw[mul_comm, (by ring :
    --               Field51_as_Nat constants.SQRT_M1 ^ 2 =
    --                Field51_as_Nat constants.SQRT_M1 *
    --                Field51_as_Nat constants.SQRT_M1 ),
    --                ←  mul_assoc
    --                ] at this
    --               have := zero_of_mul_SQRT_M1_zero (zero_of_mul_SQRT_M1_zero this)
    --               have hu:=to_bytes_zero_of_Field51_as_Nat_zero hu
    --               have :=to_bytes_zero_of_Field51_as_Nat_zero check_zero
    --               rw[← hu] at this
    --               apply correct_sign_sqrt_post this
    --               -- END TASK
    --             · -- BEGIN TASK
    --               constructor
    --               · -- BEGIN TASK
    --                 simp[← modEq_zero_iff]
    --                 intro hu hv
    --                 have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
    --                   simp[Field51_as_Nat, Finset.sum_range_succ]
    --                   simp_all
    --                 have := (v3_post_1.trans (hv.mul_left (Field51_as_Nat fe))).mul_left (Field51_as_Nat u)
    --                 have :=r_post_1.trans ((fe2_post_1.trans this).mul_right (Field51_as_Nat fe4))
    --                 have r_prime_eq0 := r_prime_post_1.trans (this.mul_left (Field51_as_Nat constants.SQRT_M1))
    --                 simp at r_prime_eq0
    --                 have : Field51_as_Nat r_prime % p % 2 = 0 := by
    --                     simp[Nat.ModEq] at r_prime_eq0
    --                     rw[r_prime_eq0]
    --                 simp[r_is_negative_post] at r2_post
    --                 have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
    --                   simp[Field51_as_Nat, Finset.sum_range_succ]
    --                   simp_all
    --                 rw[this]
    --                 constructor
    --                 · apply  r_prime_eq0
    --                 · by_cases h: Field51_as_Nat r1 % p % 2 = 1
    --                   · simp_all
    --                   · simp_all
    --                     intro i hi
    --                     interval_cases i
    --                     all_goals (expand r_prime_post_2 with 5 ; scalar_tac)
    --                 -- END TASK
    --               · -- BEGIN TASK
    --                 constructor
    --                 · -- BEGIN TASK
    --                   simp[← modEq_zero_iff]
    --                   intro hu hv x
    --                   rw[← Nat.ModEq]
    --                   have :=u_eq1.mul_left (Field51_as_Nat constants.SQRT_M1)
    --                   rw[← mul_assoc, (by ring :
    --                   Field51_as_Nat constants.SQRT_M1 *
    --                   Field51_as_Nat constants.SQRT_M1 =Field51_as_Nat constants.SQRT_M1 ^ 2  ),
    --                   ] at this
    --                   have :=check_eq_mod.trans this
    --                   intro hxx
    --                   have eq_im:= hxx.mul this
    --                   rw[(by ring : x ^ 2 * Field51_as_Nat v *
    --                   (Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v) =
    --                   (x * Field51_as_Nat v *Field51_as_Nat r_prime) ^ 2
    --                   ), (by ring : Field51_as_Nat u * (Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat u)
    --                   = Field51_as_Nat u ^2 * Field51_as_Nat constants.SQRT_M1 )] at eq_im
    --                   have :  ∀ i < 5, (u[i]!).val < 2 ^ 54 := by
    --                           intro i _
    --                           interval_cases i
    --                           all_goals (expand h_u_bounds with 5; scalar_tac)
    --                   obtain ⟨ inv_u, inv_u_ok, inv_u_1, inv_u_2 ⟩  := invert_spec u this
    --                   have : Field51_as_Nat u % p ≠ 0 := by
    --                     intro hu1
    --                     apply hu
    --                     rw[modEq_zero_iff]
    --                     apply hu1
    --                   have inv_u_1:= inv_u_1 this
    --                   rw[← modEq_one_iff] at inv_u_1
    --                   have inv_u_1:= (mod_mul_mod (Field51_as_Nat inv_u) (Field51_as_Nat u)).symm.trans inv_u_1
    --                   have inv_u_1:=(inv_u_1.pow 2).mul_right (Field51_as_Nat constants.SQRT_M1)
    --                   simp[mul_pow] at inv_u_1
    --                   have u_eq:= eq_im.mul_left ((Field51_as_Nat inv_u)^2)
    --                   rw[← mul_assoc, ← mul_pow] at u_eq
    --                   have u_eq:= u_eq.trans inv_u_1
    --                   have u_eq:= u_eq.pow 2
    --                   simp[← pow_mul] at u_eq
    --                   have : (Field51_as_Nat constants.SQRT_M1) ^2 ≡ p-1 [MOD p] := by
    --                     unfold constants.SQRT_M1
    --                     decide
    --                   have := u_eq.trans this
    --                   apply SQRT_M1_not_square (Field51_as_Nat inv_u * (x * Field51_as_Nat v * Field51_as_Nat r_prime)) this
    --                   -- END TASK
    --                 · -- BGEIN TASK
    --                   constructor
    --                   · intro hu hv hx
    --                     constructor
    --                     · -- BGEIN TASK
    --                       rw[← Nat.ModEq]
    --                       have :=u_eq1.mul_left (Field51_as_Nat constants.SQRT_M1)
    --                       rw[← mul_assoc, (by ring :
    --                         Field51_as_Nat constants.SQRT_M1 *
    --                         Field51_as_Nat constants.SQRT_M1 =Field51_as_Nat constants.SQRT_M1 ^ 2  ),
    --                         ] at this
    --                       have eq_im:=check_eq_mod.trans this
    --                       have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
    --                         simp[Field51_as_Nat, Finset.sum_range_succ]
    --                         simp_all
    --                       have r2_eq: (Field51_as_Nat r2 )^2 ≡ (Field51_as_Nat r_prime) ^2 [MOD p] := by
    --                         rcases (mod_two_zero_or_one (Field51_as_Nat r_prime % p)) with one | zero
    --                         · -- BEGIN TASK
    --                           rw[mod_two_Eq_one_iff] at one
    --                           simp[this, one] at r_is_negative_post
    --                           simp[r_is_negative_post] at r2_post
    --                           have : Field51_as_Nat r2 = Field51_as_Nat r_neg:= by
    --                             simp[Field51_as_Nat, Finset.sum_range_succ]
    --                             simp_all
    --                           rw[← this] at r_neg_post_1
    --                           simp_all
    --                           rw[← modEq_zero_iff] at r_neg_post_1
    --                           apply nat_sq_of_add_modeq_zero
    --                           rw[add_comm]
    --                           apply  r_neg_post_1
    --                           -- END TASK
    --                         · -- BEGIN TASK
    --                           rw[modEq_zero_iff] at zero
    --                           simp[this, zero] at r_is_negative_post
    --                           simp[r_is_negative_post] at r2_post
    --                           have : Field51_as_Nat r2 = Field51_as_Nat r_prime:= by
    --                             simp[Field51_as_Nat, Finset.sum_range_succ]
    --                             simp_all
    --                           rw[this]
    --                           -- END TASK
    --                       have r2_eq:= r2_eq.mul_right (Field51_as_Nat v)
    --                       have :=(mod_sq_mod_mul (Field51_as_Nat r2) (Field51_as_Nat v) p)
    --                       apply this.trans
    --                       apply r2_eq.trans eq_im
    --                       -- END TASK
    --                     · -- BGEIN TASK
    --                       by_cases h:(r_is_negative.val = 1#u8)
    --                       · -- BGEIN TASK
    --                         simp[h] at r2_post
    --                         intro i hi
    --                         interval_cases i
    --                         all_goals (simp_all; expand r_neg_post_2 with 5;scalar_tac)
    --                         -- END TASK
    --                       · -- BGEIN TASK
    --                         simp[h] at r2_post
    --                         intro i hi
    --                         interval_cases i
    --                         all_goals (simp_all; expand r_prime_post_2 with 5;scalar_tac)
    --                         -- END TASK
    --                       -- END TASK
    --                   · exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
    --                       r_is_negative_post r_neg_post_1 r2_post -- Non-negativity
    --                   -- END TASK
    --                 -- END TASK
    --               -- END TASK
    --           -- END TASK
    --         -- END TASK
    --         -- END TASK
    --       -- END TASK
    --     · -- BEGIN TASK
    --       simp[second_choice]
    --       progress*
    --       · simp[Choice.zero] at r1_post
    --         simp_all
    --         clear check_eq_mod check_eq_v eq1_mod
    --         grind
    --       · -- BEGIN TASK
    --         have : ¬ flipped_sign_sqrt_i = Choice.one := by
    --           intro h
    --           apply second_choice
    --           exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mpr h
    --         simp[this] at flipped_sign_sqrt_i_post
    --         have :=nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1
    --         by_cases choise3 : correct_sign_sqrt.val = 1#u8
    --         · -- BEGIN TASK
    --           have : correct_sign_sqrt = Choice.one := by
    --             exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp choise3
    --           simp[this] at correct_sign_sqrt_post
    --           have check_eq_u:= eq_to_bytes_eq_Field51_as_Nat  correct_sign_sqrt_post
    --           rw[← Nat.ModEq] at check_eq_u
    --           have v_eq_u:=check_eq_mod.trans (check_eq_u.mul_left  (Field51_as_Nat constants.SQRT_M1 ^2))
    --           simp[choise3, Choice.one]
    --           simp[Choice.zero] at r1_post
    --           have : Field51_as_Nat r1 = Field51_as_Nat r := by
    --               simp[Field51_as_Nat, Finset.sum_range_succ]
    --               simp_all
    --           simp[← modEq_zero_iff]
    --           constructor
    --           · -- BEGIN TASK
    --             intro hu
    --             have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
    --             simp at this
    --             have := Nat.ModEq.trans fe2_post_1 this
    --             have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
    --             simp at this
    --             have r_eq0:= Nat.ModEq.trans r_post_1 this
    --             have : Field51_as_Nat r % p % 2 = 0 := by
    --                   simp[Nat.ModEq] at r_eq0
    --                   rw[r_eq0]
    --             have : Field51_as_Nat r2 = Field51_as_Nat r := by
    --               simp[Field51_as_Nat, Finset.sum_range_succ]
    --               simp_all
    --             rw[this]
    --             constructor
    --             · apply  r_eq0
    --             · by_cases h:Field51_as_Nat r1 % p % 2 = 1
    --               · simp_all
    --               · simp_all
    --                 clear *- r_post_2
    --                 grind

    --             -- END TASK
    --           · -- BEGIN TASK
    --             constructor
    --             · -- BEGIN TASK
    --               intro hu hv
    --               have := check_eq_u.symm.trans (check_eq_v.trans ((hv.pow  (7 * 2 ^ 253 - 35)).mul_left (Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2))))
    --               simp at this
    --               apply hu this
    --               -- END TASK
    --             · -- BEGIN TASK
    --               constructor
    --               · -- BEGIN TASK
    --                 intro hu hv xx hx
    --                 constructor
    --                 · -- BEGIN TASK
    --                   rw[← Nat.ModEq] at hx
    --                   have eq_im:=check_eq_r_v.symm.trans check_eq_u
    --                   have : Field51_as_Nat r1 = Field51_as_Nat r := by
    --                       simp[Field51_as_Nat, Finset.sum_range_succ]
    --                       simp_all
    --                   have r2_eq: (Field51_as_Nat r2 )^2 ≡ (Field51_as_Nat r) ^2 [MOD p] := by
    --                       rcases (mod_two_zero_or_one (Field51_as_Nat r % p)) with one | zero
    --                       · -- BEGIN TASK
    --                         rw[mod_two_Eq_one_iff] at one
    --                         simp[this, one] at r_is_negative_post
    --                         simp[r_is_negative_post] at r2_post
    --                         have : Field51_as_Nat r2 = Field51_as_Nat r_neg:= by
    --                           simp[Field51_as_Nat, Finset.sum_range_succ]
    --                           simp_all
    --                         rw[← this] at r_neg_post_1
    --                         simp_all
    --                         rw[← modEq_zero_iff] at r_neg_post_1
    --                         apply nat_sq_of_add_modeq_zero
    --                         rw[add_comm]
    --                         apply  r_neg_post_1
    --                         -- END TASK
    --                       · -- BEGIN TASK
    --                         rw[modEq_zero_iff] at zero
    --                         simp[this, zero] at r_is_negative_post
    --                         simp[r_is_negative_post] at r2_post
    --                         have : Field51_as_Nat r2 = Field51_as_Nat r:= by
    --                           simp[Field51_as_Nat, Finset.sum_range_succ]
    --                           simp_all
    --                         rw[this]
    --                         -- END TASK
    --                   rw[← Nat.ModEq]
    --                   apply ((mod_sq_mod_mul (Field51_as_Nat r2) (Field51_as_Nat v) p)).trans
    --                   apply (r2_eq.mul_right (Field51_as_Nat v)).trans eq_im
    --                   -- END TASK
    --                 · -- BEGIN TASK
    --                   rcases (mod_two_zero_or_one (Field51_as_Nat r % p)) with one | zero
    --                   · -- BEGIN TASK
    --                         rw[mod_two_Eq_one_iff] at one
    --                         simp[this, one] at r_is_negative_post
    --                         simp[r_is_negative_post] at r2_post
    --                         have : Field51_as_Nat r2 = Field51_as_Nat r_neg:= by
    --                           simp[Field51_as_Nat, Finset.sum_range_succ]
    --                           simp_all
    --                         rw[← this] at r_neg_post_1
    --                         simp_all
    --                         intro i hi
    --                         interval_cases i
    --                         all_goals (expand r_neg_post_2 with 5; scalar_tac)
    --                         -- END TASK
    --                   · -- BEGIN TASK
    --                         rw[modEq_zero_iff] at zero
    --                         simp[this, zero] at r_is_negative_post
    --                         simp[r_is_negative_post] at r2_post
    --                         have : Field51_as_Nat r2 = Field51_as_Nat r:= by
    --                           simp[Field51_as_Nat, Finset.sum_range_succ]
    --                           simp_all
    --                         simp_all
    --                         intro i hi
    --                         interval_cases i
    --                         all_goals (expand r_post_2 with 5; scalar_tac)
    --                         -- END TASK
    --                   -- END TASK

    --                 -- END TASK
    --               · -- BEGIN TASK
    --                 constructor
    --                 · intro hu hv
    --                   have eq_im:=check_eq_r_v.symm.trans check_eq_u
    --                   use Field51_as_Nat r
    --                   rw[← Nat.ModEq]
    --                   apply eq_im
    --                 · exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
    --                     r_is_negative_post r_neg_post_1 r2_post -- Non-negativity
    --                 -- END TASK
    --               -- END TASK
    --             -- END TASK
    --           -- END TASK
    --         · -- BEGIN TASK
    --           simp[choise3,Choice.zero]
    --           have :¬ correct_sign_sqrt = Choice.one := by
    --             intro h
    --             apply choise3
    --             simp[h, Choice.one]
    --           simp[this] at correct_sign_sqrt_post
    --           have : ¬ check = u := by
    --             intro h
    --             apply correct_sign_sqrt_post
    --             rw[h]
    --           · constructor
    --             · -- BEGIN TASK
    --               intro hu
    --               rw[← modEq_zero_iff] at hu
    --               have :=check_eq_v.trans ((hu.pow (2 + (2 ^ 252 - 3) * 2)).mul_right  (Field51_as_Nat v ^ (7 * 2 ^ 253 - 35)))
    --               simp at this
    --               have hu:=to_bytes_zero_of_Field51_as_Nat_zero hu
    --               have :=to_bytes_zero_of_Field51_as_Nat_zero this
    --               rw[← this] at hu
    --               apply correct_sign_sqrt_post hu.symm
    --               -- END TASK
    --             · -- BEGIN TASK
    --               constructor
    --               · -- BEGIN TASK
    --                 simp[← modEq_zero_iff]
    --                 intro hu hv
    --                 have :=check_eq_r_v.trans (hv.mul_left (Field51_as_Nat r ^ 2))
    --                 simp at this
    --                 simp[Choice.zero] at r1_post
    --                 have r1_eq_r: Field51_as_Nat r1 = Field51_as_Nat r := by
    --                       simp[Field51_as_Nat, Finset.sum_range_succ]
    --                       simp_all
    --                 have :=(fe2_post_1.trans ((v3_post_1.trans (hv.mul_left (Field51_as_Nat fe))).mul_left (Field51_as_Nat u))).mul_right (Field51_as_Nat fe4)
    --                 have r_eq0:= r_post_1.trans this
    --                 simp at r_eq0
    --                 rw[add_comm] at r_neg_post_1
    --                 have := nat_sqrt_m1_sq_of_add_modeq_zero r_neg_post_1
    --                 rw[r1_eq_r] at this
    --                 have x_eq0:= this.trans (r_eq0.mul_left (Field51_as_Nat constants.SQRT_M1 ^ 2))
    --                 simp at x_eq0
    --                 rcases (mod_two_zero_or_one (Field51_as_Nat r % p)) with one | zero
    --                 · -- BEGIN TASK
    --                         rw[mod_two_Eq_one_iff] at one
    --                         simp[r1_eq_r, one] at r_is_negative_post
    --                         simp[r_is_negative_post] at r2_post
    --                         have : Field51_as_Nat r2 = Field51_as_Nat r_neg:= by
    --                           simp[Field51_as_Nat, Finset.sum_range_succ]
    --                           simp_all
    --                         rw[this]
    --                         constructor
    --                         · apply x_eq0
    --                         · simp_all
    --                           intro i hi
    --                           interval_cases i
    --                           all_goals (expand r_neg_post_2 with 5 ; scalar_tac)
    --                         -- END TASK
    --                 · -- BEGIN TASK
    --                         rw[modEq_zero_iff] at zero
    --                         simp[r1_eq_r, zero] at r_is_negative_post
    --                         simp[r_is_negative_post] at r2_post
    --                         have : Field51_as_Nat r2 = Field51_as_Nat r:= by
    --                           simp[Field51_as_Nat, Finset.sum_range_succ]
    --                           simp_all
    --                         rw[this]
    --                         constructor
    --                         · apply r_eq0
    --                         · simp_all
    --                           intro i hi
    --                           interval_cases i
    --                           all_goals (expand r_post_2 with 5 ; scalar_tac)
    --                         -- END TASK
    --                 -- END TASK
    --               · -- BEGIN TASK
    --                 constructor
    --                 · -- BEGIN TASK
    --                   simp[← modEq_zero_iff]
    --                   intro hu hv xx hxx
    --                   rw[← Nat.ModEq] at hxx
    --                   have p_eq:2 + (2 ^ 252 - 3) * 2 + (7 * 2 ^ 253 - 35) = (p-1) * 2 + 1 := by unfold p; simp
    --                   have p_eq1: 2 * (2 + (2 ^ 252 - 3) * 2) = ((p-1)/2)+ 2 := by unfold p; scalar_tac
    --                   have xx_check:= ((hxx.pow (2 + (2 ^ 252 - 3) * 2)).mul_right (Field51_as_Nat v ^ (7 * 2 ^ 253 - 35))).trans check_eq_v.symm
    --                   rw[mul_pow,mul_assoc,← pow_add,p_eq,←  pow_mul, p_eq1, pow_add] at xx_check
    --                   rw[Nat.modEq_zero_iff_dvd] at hv
    --                   have := coprime_of_prime_not_dvd prime_25519 hv
    --                   have fermat:= ((Nat.ModEq.pow_card_sub_one_eq_one prime_25519 this ).pow 2).mul_right (Field51_as_Nat v)
    --                   simp[← pow_mul, pow_add_one] at fermat
    --                   have fermat:= (fermat.mul_left (xx ^ ((p - 1) / 2) * xx ^ 2)).symm.trans xx_check

    --                   by_cases h: xx ≡ 0 [MOD p]
    --                   · have := ((h.pow 2).mul_right (Field51_as_Nat v)).symm.trans hxx
    --                     simp at this
    --                     apply hu this.symm
    --                   · have :=pow_div_two_eq_neg_one_or_one h
    --                     rcases this with hl | hl
    --                     · have := hl.mul_right (xx ^ 2 * Field51_as_Nat v)
    --                       simp[← mul_assoc] at this
    --                       have:= (fermat.symm.trans this).trans hxx
    --                       obtain ⟨ru, hu, hru_mod, hru_lt⟩ := to_bytes_spec u
    --                       obtain ⟨rcheck, hrcheck, hrcheck_mod, hrcheck_lt⟩ := to_bytes_spec check
    --                       have := this.trans hru_mod.symm
    --                       have check_eq_u:= hrcheck_mod.trans this
    --                       rw[Nat.ModEq] at check_eq_u
    --                       have := Nat.mod_eq_of_lt hru_lt
    --                       rw[this] at check_eq_u
    --                       have :=Nat.mod_eq_of_lt hrcheck_lt
    --                       rw[this] at check_eq_u
    --                       have := eq_U8x32_as_Nat_eq check_eq_u
    --                       apply correct_sign_sqrt_post
    --                       rw[hrcheck, hu, this]
    --                     · have := hl.mul_right (xx ^ 2 * Field51_as_Nat v)
    --                       simp[← mul_assoc] at this
    --                       have fermat:= (fermat.symm.trans this)
    --                       have := (hxx.mul_left (p-1))
    --                       simp[← mul_assoc] at this
    --                       have fermat:= (fermat.trans this).trans (u_m.mul_left (p-1))
    --                       rw[← mul_assoc] at fermat
    --                       have : (p-1) *Field51_as_Nat constants.SQRT_M1 ^2 ≡ 1 [MOD p] := by
    --                           unfold constants.SQRT_M1
    --                           decide
    --                       have := fermat.trans (this.mul_right (Field51_as_Nat fe6))
    --                       simp at this
    --                       obtain ⟨ru, hu, hru_mod, hru_lt⟩ := to_bytes_spec fe6
    --                       obtain ⟨rcheck, hrcheck, hrcheck_mod, hrcheck_lt⟩ := to_bytes_spec check
    --                       have := this.trans hru_mod.symm
    --                       have check_eq_u:= hrcheck_mod.trans this
    --                       rw[Nat.ModEq] at check_eq_u
    --                       have := Nat.mod_eq_of_lt hru_lt
    --                       rw[this] at check_eq_u
    --                       have :=Nat.mod_eq_of_lt hrcheck_lt
    --                       rw[this] at check_eq_u
    --                       have := eq_U8x32_as_Nat_eq check_eq_u
    --                       apply flipped_sign_sqrt_post
    --                       rw[hrcheck, hu, this]
    --                   -- END TASK
    --                 · -- BEGIN TASK
    --                   refine ⟨?_, ?nonneg⟩
    --                   case nonneg =>
    --                     exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
    --                       r_is_negative_post r_neg_post_1 r2_post -- Non-negativity
    --                   intro hu hv hx
    --                   constructor
    --                   · -- BEGIN TASK
    --                     rw[← Nat.ModEq]
    --                     have eq_check:= (check_eq_v.symm.trans check_eq_r_v).symm
    --                     have :2 + (2 ^ 252 - 3) * 2 = (p-1)/4 + 1 := by unfold p; scalar_tac
    --                     rw[this,pow_add] at eq_check
    --                     have : 7 * 2 ^ 253 - 35 = 7 * ((p-1)/4) := by unfold p; scalar_tac
    --                     rw[this] at eq_check
    --                     simp[pow_mul, mul_assoc] at eq_check
    --                     simp[mul_comm (Field51_as_Nat u)] at eq_check
    --                     rw[← mul_assoc,←  mul_pow] at eq_check
    --                     have :¬ Field51_as_Nat u * Field51_as_Nat v ^ 7 ≡ 0 [MOD p] := by
    --                       intro h
    --                       have :=mul_zero_eq_or prime_25519 h
    --                       rcases this with h | h
    --                       · apply hu h
    --                       · rw[(by scalar_tac: 7 =1+6), pow_add] at h
    --                         have :=mul_zero_eq_or prime_25519 h
    --                         simp at this
    --                         rcases this with h | h
    --                         · apply hv h
    --                         · rw[(by scalar_tac: 6 =1+5), pow_add] at h
    --                           have :=mul_zero_eq_or prime_25519 h
    --                           simp at this
    --                           rcases this with h | h
    --                           · apply hv h
    --                           · rw[(by scalar_tac : 5 = 1 + 4), pow_add] at h
    --                             have :=mul_zero_eq_or prime_25519 h
    --                             simp at this
    --                             rcases this with h | h
    --                             · apply hv h
    --                             · rw[(by scalar_tac : 4 = 1 + 3), pow_add] at h
    --                               have :=mul_zero_eq_or prime_25519 h
    --                               simp at this
    --                               rcases this with h | h
    --                               · apply hv h
    --                               · rw[(by scalar_tac : 3 = 1 + 2), pow_add] at h
    --                                 have :=mul_zero_eq_or prime_25519 h
    --                                 simp at this
    --                                 rcases this with h | h
    --                                 · apply hv h
    --                                 · rw[(by scalar_tac : 2 = 1 + 1), pow_add] at h
    --                                   have :=mul_zero_eq_or prime_25519 h
    --                                   simp at this
    --                                   apply hv this


    --                     have := pow_div_four_eq_four_cases this
    --                     rcases this with h | h
    --                     · -- BEGIN TASK
    --                       have := h.mul_right (Field51_as_Nat u)
    --                       have := eq_check.trans this
    --                       simp at this
    --                       have :=hx (Field51_as_Nat r) this
    --                       apply False.elim this
    --                       -- END TASK
    --                     · rcases h with h | h
    --                       · -- BEGIN TASK
    --                         have := h.mul_right (Field51_as_Nat u)
    --                         have :=  (eq_check.trans this)
    --                         simp at this
    --                         simp[Choice.zero] at r1_post
    --                         have r1_eq_r: Field51_as_Nat r1 = Field51_as_Nat r := by
    --                           simp[Field51_as_Nat, Finset.sum_range_succ]
    --                           simp_all
    --                         have r2_eq: (Field51_as_Nat r2 )^2 ≡ (Field51_as_Nat r) ^2 [MOD p] := by
    --                           by_cases h: r_is_negative.val = 1#u8
    --                           · -- BEGIN TASK
    --                             simp[r_is_negative_post] at r2_post
    --                             have : Field51_as_Nat r2 = Field51_as_Nat r_neg:= by
    --                               simp[Field51_as_Nat, Finset.sum_range_succ]
    --                               simp_all
    --                             rw[← this] at r_neg_post_1
    --                             simp_all
    --                             rw[← modEq_zero_iff] at r_neg_post_1
    --                             apply nat_sq_of_add_modeq_zero
    --                             rw[add_comm]
    --                             apply  r_neg_post_1
    --                             -- END TASK
    --                           · -- BEGIN TASK
    --                             simp[r_is_negative_post] at r2_post
    --                             have : Field51_as_Nat r2 = Field51_as_Nat r:= by
    --                               simp[Field51_as_Nat, Finset.sum_range_succ]
    --                               simp_all
    --                             rw[this]
    --                             -- END TASK
    --                         apply ((mod_sq_mod_mul (Field51_as_Nat r2) (Field51_as_Nat v) p)).trans
    --                         apply (r2_eq.mul_right (Field51_as_Nat v)).trans this
    --                         -- END TASK
    --                       · rcases h with h | h
    --                         · -- BEGIN TASK
    --                           have := h.mul_right (Field51_as_Nat u)
    --                           have h:=  (eq_check.trans this).mul_left (Field51_as_Nat constants.SQRT_M1 ^ 2)
    --                           simp[← mul_assoc] at h
    --                           have :Field51_as_Nat constants.SQRT_M1 ^ 2 * Field51_as_Nat constants.SQRT_M1 ^ 2 ≡ 1 [MOD p] := by
    --                             unfold constants.SQRT_M1
    --                             decide
    --                           have := h.trans (this.mul_right  (Field51_as_Nat u))
    --                           simp[← mul_pow] at this
    --                           have :=hx (Field51_as_Nat constants.SQRT_M1 *Field51_as_Nat r) this
    --                           apply False.elim this
    --                           -- END TASK
    --                         · -- BEGIN TASK
    --                           have := h.mul_right (Field51_as_Nat u)
    --                           have h:=  (eq_check.trans this)
    --                           have h:= (check_eq_r_v.trans h).trans (u_m.mul_left (Field51_as_Nat constants.SQRT_M1 ^3))
    --                           rw[← mul_assoc] at h
    --                           have : Field51_as_Nat constants.SQRT_M1 ^ 3 * Field51_as_Nat constants.SQRT_M1 ^ 2
    --                             ≡ Field51_as_Nat constants.SQRT_M1 [MOD p] := by
    --                             unfold constants.SQRT_M1
    --                             decide
    --                           have := h.trans (this.mul_right  (Field51_as_Nat fe6))
    --                           rw[mul_comm] at fe7_post_1
    --                           have := this.trans fe7_post_1.symm
    --                           obtain ⟨ru, hu, hru_mod, hru_lt⟩ := to_bytes_spec fe7
    --                           obtain ⟨rcheck, hrcheck, hrcheck_mod, hrcheck_lt⟩ := to_bytes_spec check
    --                           have := this.trans hru_mod.symm
    --                           have check_eq_u:= hrcheck_mod.trans this
    --                           rw[Nat.ModEq] at check_eq_u
    --                           have := Nat.mod_eq_of_lt hru_lt
    --                           rw[this] at check_eq_u
    --                           have :=Nat.mod_eq_of_lt hrcheck_lt
    --                           rw[this] at check_eq_u
    --                           have := eq_U8x32_as_Nat_eq check_eq_u
    --                           simp[hrcheck, hu, this] at flipped_sign_sqrt_i_post
    --                           -- END TASK
    --                     -- END TASK
    --                   · -- BEGIN TASK
    --                     intro i hi
    --                     by_cases one:r_is_negative.val = 1#u8
    --                     · -- BEGIN TASK
    --                         simp_all
    --                         interval_cases i
    --                         all_goals (expand r_neg_post_2 with 5; scalar_tac)
    --                         -- END TASK
    --                     · -- BEGIN TASK
    --                         simp_all[Choice.zero]
    --                         interval_cases i
    --                         any_goals (expand r_post_2 with 5; scalar_tac)
    --                         -- END TASK
    --                     -- END TASK
    --                   -- END TASK
    --                 -- END TASK
    --               -- END TASK
    --           -- END TASK
    --         -- END TASK
    --     -- END TASK
    --     -- END TASK
    --     -- END TASK
    --     -- END TASK
    --   -- END TASK



set_option maxHeartbeats 400000 in -- heavy progress computations
@[progress]
theorem sqrt_ratio_i_spec
    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val ≤ 2 ^ 52 - 1)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 52 - 1) :
    sqrt_ratio_i u v ⦃ c =>
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat c.2 % p
    let i_nat := Field51_as_Nat backend.serial.u64.constants.SQRT_M1 % p
    (∀ i < 5,  c.2[i]!.val ≤ 2 ^ 53 - 1) ∧
    (r_nat % 2 = 0) ∧
    (u_nat = 0 →
      c.1.val = 1#u8 ∧ r_nat = 0) ∧
    (u_nat ≠ 0 ∧ v_nat = 0 →
      c.1.val = 0#u8 ∧ r_nat = 0) ∧
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
      c.1.val = 1#u8 ∧ (r_nat ^ 2 * v_nat) % p = u_nat) ∧
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (¬(∃ x : Nat, (x^2 * v_nat) % p = u_nat)) →
      c.1.val = 0#u8 ∧ (r_nat ^2 * v_nat) % p = (i_nat * u_nat) % p)
    ⦄ := by
  have ⟨c, h_ok, h1, h2, h3, h4, h_nonneg⟩ := sqrt_ratio_i_spec' u v h_u_bounds h_v_bounds
  exact exists_imp_spec ⟨c, h_ok, by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Unconditional bounds: by exhaustion over the 4 cases
      by_cases hu : Field51_as_Nat u % p = 0
      · exact (h1 hu).2.2
      · by_cases hv : Field51_as_Nat v % p = 0
        · exact (h2 ⟨hu, hv⟩).2.2
        · by_cases hqr : ∃ x : Nat, (x ^ 2 * (Field51_as_Nat v % p)) % p = Field51_as_Nat u % p
          · exact (h3 ⟨hu, hv, hqr⟩).2.2
          · exact (h4 ⟨hu, hv, hqr⟩).2.2
    · -- Non-negativity
      exact h_nonneg
    · -- Case 1
      intro hu; exact ⟨(h1 hu).1, (h1 hu).2.1⟩
    · -- Case 2
      intro ⟨hu, hv⟩; exact ⟨(h2 ⟨hu, hv⟩).1, (h2 ⟨hu, hv⟩).2.1⟩
    · -- Case 3
      intro ⟨hu, hv, hqr⟩; exact ⟨(h3 ⟨hu, hv, hqr⟩).1, (h3 ⟨hu, hv, hqr⟩).2.1⟩
    · -- Case 4
      intro ⟨hu, hv, hnqr⟩; exact ⟨(h4 ⟨hu, hv, hnqr⟩).1, (h4 ⟨hu, hv, hnqr⟩).2.1⟩⟩

end curve25519_dalek.field.FieldElement51
