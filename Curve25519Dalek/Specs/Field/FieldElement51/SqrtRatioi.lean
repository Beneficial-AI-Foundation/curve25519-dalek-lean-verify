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
      List.getElem!_eq_getElem?_getD, ne_eq, and_imp,
      Nat.mul_mod_mod, forall_exists_index, not_exists, Nat.mod_mul_mod]
      progress*
      · intro i hi
        simp only [Choice.one, ↓reduceIte] at r1_post
        rw [r1_post i hi]
        have := r_prime_post_2 i hi
        omega
      · simp only [Choice.one, ↓reduceIte] at r1_post
        simp only [Choice.one]
        have r1_eq : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
          simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
              Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
              List.Vector.length_val, UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem?_pos,
              Option.getD_some, one_mul, mul_one, Nat.one_lt_ofNat, Nat.reduceMul,
              Nat.reduceLT, Nat.lt_add_one]
          simp only [Array.getElem!_Nat_eq] at r1_post
          expand r1_post with 5
          simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
            getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
        simp only [← modEq_zero_iff]
        -- Shared: first_choice → check ≡ fe6 [MOD p]
        have h_bytes_fe6 : check.to_bytes = fe6.to_bytes :=
          flipped_sign_sqrt_post.mp ((Choice.val_eq_one_iff _).mp first_choice)
        have check_fe6 := eq_to_bytes_eq_Field51_as_Nat h_bytes_fe6
        rw [← Nat.ModEq] at check_fe6
        -- Shared: r_prime^2 * v ≡ u [MOD p]
        have r_prime_sq_v_u : Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v ≡
            Field51_as_Nat u [MOD p] :=
          (check_eq_mod.trans (check_fe6.mul_left _)).trans this.symm
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · -- case 1: u = 0
          intro hu
          refine ⟨trivial, ?_, ?_⟩
          · -- r2 ≡ 0 [MOD p]
            have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
            simp only [zero_mul] at this
            have := Nat.ModEq.trans fe2_post_1 this
            have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
            simp only [zero_mul] at this
            have := Nat.ModEq.trans r_post_1 this
            have := Nat.ModEq.mul_left (Field51_as_Nat constants.SQRT_M1) this
            have r_prime_eq0 := Nat.ModEq.trans r_prime_post_1 this
            simp only [mul_zero] at r_prime_eq0
            rw [r1_eq] at r_neg_post_1 r_is_negative_post
            have : Field51_as_Nat r_prime % p % 2 = 0 := by
              simp only [Nat.ModEq] at r_prime_eq0
              rw [r_prime_eq0]; simp only [Nat.zero_mod]
            have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
              intro h; exact absurd (r_is_negative_post.mp h) (by omega)
            simp only [h_not_neg, if_neg, not_false_eq_true] at r2_post
            have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
              simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                Finset.sum_singleton]
              expand r2_post with 5
              simp only [r2_post_0, r2_post_1, r2_post_2, r2_post_3, r2_post_4]
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
                getElem!_pos, Nat.reducePow, Nat.add_one_sub_one, Nat.reduceSub, Nat.reduceMul,
                Nat.reduceAdd, zero_ne_one, mul_zero, UScalar.neq_to_neq_val, Nat.ofNat_pos,
                Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one, pow_zero, one_mul, mul_one]
            rw [this]
            exact r_prime_eq0
          · -- bounds on r2
            intro i hi
            by_cases h : r_is_negative.val = 1#u8
            · simp only [h, ite_true] at r2_post
              have := r2_post i hi
              have := r_neg_post_2 i hi
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
                getElem!_pos, true_iff, getElem?_pos, Option.getD_some, ge_iff_le]
              have := r_neg_post_2 i hi
              omega
            · simp only [h, ite_false] at r2_post
              have := r2_post i hi
              have := r1_post i hi
              have := r_prime_post_2 i hi
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
                getElem!_pos, false_iff, Nat.mod_two_not_eq_one, UScalar.neq_to_neq_val,
                getElem?_pos, Option.getD_some, ge_iff_le]
              have := r2_post i hi; have := r_prime_post_2 i hi; omega
        · -- case 2: u ≠ 0, v = 0 → contradiction in first branch
          intro hu hv
          exfalso; apply hu
          have check0 : Field51_as_Nat check ≡ 0 [MOD p] := by
            have := hv.mul_right (Field51_as_Nat fe5)
            simp only [zero_mul] at this
            exact check_post_1.trans this
          have h_bytes : check.to_bytes = fe6.to_bytes :=
            flipped_sign_sqrt_post.mp ((Choice.val_eq_one_iff _).mp first_choice)
          have check_fe6 := eq_to_bytes_eq_Field51_as_Nat h_bytes
          rw [← Nat.ModEq] at check_fe6
          have fe6_zero := check_fe6.symm.trans check0
          have h_sum := fe6_zero.add_left (Field51_as_Nat u)
          simp only [Nat.add_zero] at h_sum
          rw [← modEq_zero_iff] at fe6_post_1
          exact h_sum.symm.trans fe6_post_1
        · -- case 3: QR exists
          intro hu hv x hx
          refine ⟨trivial, ?_, ?_⟩
          · rw [mod_sq_mod_mul_eq, ← Nat.ModEq]
            by_cases h_neg : r_is_negative.val = 1#u8
            · simp only [h_neg, ite_true] at r2_post
              have r2_eq_neg : Field51_as_Nat r2 = Field51_as_Nat r_neg := by
                simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                  Finset.sum_singleton]
                expand r2_post with 5
                simp only [r2_post_0, r2_post_1, r2_post_2, r2_post_3, r2_post_4]
              rw [r2_eq_neg]
              have h_sum : Field51_as_Nat r1 + Field51_as_Nat r_neg ≡ 0 [MOD p] := by
                rw [modEq_zero_iff]
                exact r_neg_post_1
              rw [r1_eq] at h_sum
              exact ((nat_sq_of_add_modeq_zero h_sum).symm.mul_right _).trans r_prime_sq_v_u
            · simp only [h_neg, ite_false] at r2_post
              have r2_eq_r1 : Field51_as_Nat r2 = Field51_as_Nat r1 := by
                simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                  Finset.sum_singleton]
                expand r2_post with 5
                simp only [r2_post_0, r2_post_1, r2_post_2, r2_post_3, r2_post_4]
              rw [r2_eq_r1, r1_eq]
              exact r_prime_sq_v_u
          · intro i hi
            by_cases h : r_is_negative.val = 1#u8
            · simp only [h, ite_true] at r2_post
              have := r2_post i hi
              have := r_neg_post_2 i hi
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
                getElem!_pos, true_iff, getElem?_pos, Option.getD_some, ge_iff_le]
              have := r_neg_post_2 i hi
              omega
            · simp only [h, ite_false] at r2_post
              have := r2_post i hi
              have := r1_post i hi
              have := r_prime_post_2 i hi
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNat_val_eq,
                getElem!_pos, false_iff, Nat.mod_two_not_eq_one, UScalar.neq_to_neq_val,
                getElem?_pos, Option.getD_some, ge_iff_le]
              have := r2_post i hi; have := r_prime_post_2 i hi; omega
        · -- case 4: no QR → contradiction in first branch
          intro hu hv hno_qr
          exfalso
          exact absurd r_prime_sq_v_u (hno_qr _)
        · exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
            r_is_negative_post r_neg_post_1 r2_post
    · -- second branch: first_choice = false
      have u_m := nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1
      by_cases second_choice : flipped_sign_sqrt_i.val = 1#u8
      · -- A: second_choice = true (c = Choice.one, r1 = r_prime)
        simp only [first_choice, second_choice, or_true, or_false,
          ↓reduceIte, bind_tc_ok, Array.getElem!_Nat_eq,
          List.getElem!_eq_getElem?_getD, ne_eq, and_imp,
          Nat.mul_mod_mod, forall_exists_index, not_exists, Nat.mod_mul_mod]
        progress*
        · intro i hi
          simp only [Choice.one, ↓reduceIte] at r1_post
          rw [r1_post i hi]
          have := r_prime_post_2 i hi
          omega
        · -- main block A: by_cases on correct_sign_sqrt
          by_cases choice3 : correct_sign_sqrt.val = 1#u8
          · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
            -- A1: second_choice=true, choice3=true
            -- Setup: derive check ≡ u [MOD p]
            have h_check_u := correct_sign_sqrt_post.mp
              ((Choice.val_eq_one_iff _).mp choice3)
            have check_eq_u := eq_to_bytes_eq_Field51_as_Nat h_check_u
            rw [← Nat.ModEq] at check_eq_u
            -- Derive SQRT_M1 * check ≡ u from second_choice
            have h_check_fe7 := flipped_sign_sqrt_i_post.mp
              ((Choice.val_eq_one_iff _).mp second_choice)
            have check_eq_fe7 := eq_to_bytes_eq_Field51_as_Nat h_check_fe7
            rw [← Nat.ModEq] at check_eq_fe7
            have check_eq_fe6_m := check_eq_fe7.trans fe7_post_1
            have check_1 := check_eq_fe6_m.mul_left (Field51_as_Nat constants.SQRT_M1)
            have : Field51_as_Nat constants.SQRT_M1 *
                (Field51_as_Nat fe6 * Field51_as_Nat constants.SQRT_M1) =
                Field51_as_Nat constants.SQRT_M1 ^ 2 * Field51_as_Nat fe6 := by ring
            rw [this] at check_1
            have u_eq1 := check_1.trans u_m.symm
            -- sqrt_m1_u : SQRT_M1 * u ≡ u [MOD p]
            have sqrt_m1_u :=
              (check_eq_u.mul_left (Field51_as_Nat constants.SQRT_M1)).symm.trans u_eq1
            -- Key: u ≡ 0 [MOD p]
            have h_u_zero : Field51_as_Nat u % p = 0 := by
              have hp : Nat.Prime p := Fact.out
              have h_le : Field51_as_Nat u ≤
                  Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat u :=
                le_mul_of_one_le_left (Nat.zero_le _)
                  (by unfold constants.SQRT_M1 Field51_as_Nat; decide)
              have h_dvd := (Nat.modEq_iff_dvd' h_le).mp sqrt_m1_u.symm
              have h_eq := Nat.sub_mul (Field51_as_Nat constants.SQRT_M1) 1 (Field51_as_Nat u)
              rw [one_mul] at h_eq; rw [← h_eq] at h_dvd
              rcases hp.dvd_mul.mp h_dvd with h1 | h2
              · exfalso
                exact (show ¬(p ∣ (Field51_as_Nat constants.SQRT_M1 - 1)) from by
                  unfold p constants.SQRT_M1 Field51_as_Nat; decide) h1
              · rcases h2 with ⟨k, hk⟩; rw [hk]; exact Nat.mul_mod_right p k
            -- r1 = r_prime (Choice.one since second_choice=true)
            simp only [Choice.one, ↓reduceIte] at r1_post
            have r1_eq_rprime : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
              simp only [Field51_as_Nat, Array.getElem!_Nat_eq,
                List.getElem!_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one,
                Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val,
                UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem?_pos, Option.getD_some,
                one_mul, mul_one, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
                Nat.lt_add_one]
              simp only [Array.getElem!_Nat_eq] at r1_post
              expand r1_post with 5
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                Nat.reduceLT, Nat.lt_add_one]
            -- Chain: u ≡ 0 → r ≡ 0 → r_prime ≡ 0
            have hu : Nat.ModEq p (Field51_as_Nat u) 0 := by
              rw [Nat.ModEq, Nat.zero_mod]; exact h_u_zero
            have := hu.mul_right (Field51_as_Nat v3)
            simp only [zero_mul] at this
            have := fe2_post_1.trans this
            have := this.mul_right (Field51_as_Nat fe4)
            simp only [zero_mul] at this
            have r_eq0 := r_post_1.trans this
            have := r_eq0.mul_left (Field51_as_Nat constants.SQRT_M1)
            simp only [mul_zero] at this
            have r_prime_eq0 := r_prime_post_1.trans this
            -- r_prime % p % 2 = 0 → r_is_negative = false
            have r_is_neg_rprime :
                r_is_negative.val = 1#u8 ↔ Field51_as_Nat r_prime % p % 2 = 1 := by
              rw [← r1_eq_rprime]; exact r_is_negative_post
            have h_rprime_parity : Field51_as_Nat r_prime % p % 2 = 0 := by
              simp only [Nat.ModEq] at r_prime_eq0
              rw [r_prime_eq0]; simp only [Nat.zero_mod]
            have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
              intro h; exact absurd (r_is_neg_rprime.mp h) (by omega)
            simp only [h_not_neg, if_neg, not_false_eq_true] at r2_post
            have r2_eq_rprime : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
              simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                Finset.sum_singleton]
              simp only [Array.getElem!_Nat_eq] at r2_post r1_post
              expand r2_post with 5
              expand r1_post with 5
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                Nat.reducePow, Nat.add_one_sub_one, Nat.reduceSub, Nat.reduceMul,
                Nat.reduceAdd, zero_ne_one, mul_zero, UScalar.neq_to_neq_val,
                Nat.reduceLT, Nat.lt_add_one, pow_zero, one_mul, mul_one]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- case 1: u=0
              intro _
              refine ⟨(Choice.val_eq_one_iff Choice.one).mpr rfl, ?_, ?_⟩
              · rw [r2_eq_rprime]; exact r_prime_eq0
              · intro i hi
                simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                  UScalar.ofNat_val_eq, getElem!_pos, getElem?_pos, Option.getD_some]
                have := r2_post i hi; have := r1_post i hi; have := r_prime_post_2 i hi
                omega
            · -- case 2: u≠0 → contradiction from h_u_zero
              intro hu; exfalso; exact hu h_u_zero
            · -- case 3: u≠0 → contradiction from h_u_zero
              intro hu; exfalso; exact hu h_u_zero
            · -- case 4: u≠0 → contradiction from h_u_zero
              intro hu; exfalso; exact hu h_u_zero
            · -- case 5: nonneg
              rw [r2_eq_rprime]; exact h_rprime_parity
          · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
            -- A2: second_choice=true, choice3=false
            -- Derive check ≡ fe7 ≡ fe6*SQRT_M1 from second_choice
            have h_check_fe7 := flipped_sign_sqrt_i_post.mp
              ((Choice.val_eq_one_iff _).mp second_choice)
            have check_eq_fe7 := eq_to_bytes_eq_Field51_as_Nat h_check_fe7
            rw [← Nat.ModEq] at check_eq_fe7
            have check_eq_fe6_m := check_eq_fe7.trans fe7_post_1
            -- Derive u_eq1 : SQRT_M1 * check ≡ u
            have u_eq1 := check_eq_fe6_m.mul_left (Field51_as_Nat constants.SQRT_M1)
            have : Field51_as_Nat constants.SQRT_M1 *
                (Field51_as_Nat fe6 * Field51_as_Nat constants.SQRT_M1) =
                Field51_as_Nat constants.SQRT_M1 ^ 2 * Field51_as_Nat fe6 := by ring
            rw [this] at u_eq1
            have u_eq1 := u_eq1.trans u_m.symm
            -- Derive rprime_v : r_prime²*v ≡ SQRT_M1*u
            have mul_u_eq1 := u_eq1.mul_left (Field51_as_Nat constants.SQRT_M1)
            have : Field51_as_Nat constants.SQRT_M1 *
                (Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat check) =
                Field51_as_Nat constants.SQRT_M1 ^ 2 * Field51_as_Nat check := by ring
            rw [this] at mul_u_eq1
            have rprime_v := check_eq_mod.trans mul_u_eq1
            -- Derive ¬(check.to_bytes = u.to_bytes) from choice3
            have h_check_ne_u : ¬(check.to_bytes = u.to_bytes) :=
              fun h => choice3 (by rw [correct_sign_sqrt_post.mpr h]; rfl)
            -- Simplify r1 = r_prime (Choice.one)
            simp only [Choice.one, ↓reduceIte] at r1_post
            have r1_eq_rprime : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
              simp only [Field51_as_Nat, Array.getElem!_Nat_eq,
                List.getElem!_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one,
                Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val,
                UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem?_pos, Option.getD_some,
                one_mul, mul_one, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
                Nat.lt_add_one]
              simp only [Array.getElem!_Nat_eq] at r1_post
              expand r1_post with 5
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                Nat.reduceLT, Nat.lt_add_one]
            rw [r1_eq_rprime] at r_is_negative_post r_neg_post_1
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- case 1: u = 0 → exfalso (check=0=u contradicts choice3)
              intro hu; exfalso
              rw [← modEq_zero_iff] at hu
              have := u_eq1.trans hu; rw [mul_comm] at this
              have check_zero := zero_of_mul_SQRT_M1_zero this
              rw [modEq_zero_iff] at check_zero hu
              exact h_check_ne_u
                ((to_bytes_zero_of_Field51_as_Nat_zero check_zero).trans
                 (to_bytes_zero_of_Field51_as_Nat_zero hu).symm)
            · -- case 2: u≠0, v=0
              intro hu hv
              rw [← modEq_zero_iff] at hv
              have := hv.mul_left (Field51_as_Nat fe)
              simp only [mul_zero] at this
              have := v3_post_1.trans this
              have := this.mul_left (Field51_as_Nat u)
              simp only [mul_zero] at this
              have := fe2_post_1.trans this
              have := this.mul_right (Field51_as_Nat fe4)
              simp only [zero_mul] at this
              have r_zero := r_post_1.trans this
              have := r_zero.mul_left (Field51_as_Nat constants.SQRT_M1)
              simp only [mul_zero] at this
              have rprime_zero := r_prime_post_1.trans this
              have h_rprime_parity : Field51_as_Nat r_prime % p % 2 = 0 := by
                simp only [Nat.ModEq] at rprime_zero; rw [rprime_zero]
                simp only [Nat.zero_mod]
              have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
                intro h; exact absurd (r_is_negative_post.mp h) (by omega)
              simp only [h_not_neg, if_neg, not_false_eq_true] at r2_post
              have r2_eq_rprime : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
                simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                  Finset.sum_singleton]
                simp only [Array.getElem!_Nat_eq] at r2_post r1_post
                expand r2_post with 5
                expand r1_post with 5
                simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                  UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                  Nat.reducePow, Nat.add_one_sub_one, Nat.reduceSub, Nat.reduceMul,
                  Nat.reduceAdd, zero_ne_one, mul_zero, UScalar.neq_to_neq_val,
                  Nat.reduceLT, Nat.lt_add_one, pow_zero, one_mul, mul_one]
              refine ⟨rfl, ?_, ?_⟩
              · rw [r2_eq_rprime]; exact rprime_zero
              · intro i hi
                simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                  UScalar.ofNat_val_eq, getElem!_pos, getElem?_pos, Option.getD_some]
                have := r2_post i hi; have := r1_post i hi
                have := r_prime_post_2 i hi
                omega
            · -- case 3: u≠0, v≠0, QR → exfalso via SQRT_M1_not_square
              intro hu hv x hxx; exfalso
              rw [← Nat.ModEq] at hxx
              have eq_im := hxx.mul rprime_v
              rw [(by ring : x ^ 2 * Field51_as_Nat v *
                  (Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v) =
                  (x * Field51_as_Nat v * Field51_as_Nat r_prime) ^ 2),
                (by ring : Field51_as_Nat u *
                  (Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat u) =
                  Field51_as_Nat u ^ 2 *
                  Field51_as_Nat constants.SQRT_M1)] at eq_im
              -- Get modular inverse via Fermat's little theorem
              have h_not_dvd : ¬(p ∣ Field51_as_Nat u) := by
                intro h; exact hu (Nat.dvd_iff_mod_eq_zero.mp h)
              have h_coprime := coprime_of_prime_not_dvd prime_25519 h_not_dvd
              have fermat_u :=
                Nat.ModEq.pow_card_sub_one_eq_one prime_25519 h_coprime
              have hp_sub : p - 1 = (p - 2) + 1 := by unfold p; omega
              rw [hp_sub, pow_succ] at fermat_u
              -- fermat_u : u^(p-2) * u ≡ 1 [MOD p]
              have inv_sq := (fermat_u.pow 2).mul_right
                (Field51_as_Nat constants.SQRT_M1)
              simp only [one_pow, one_mul] at inv_sq
              -- inv_sq : (u^(p-2)*u)^2 * SQRT_M1 ≡ SQRT_M1 [MOD p]
              have u_eq := eq_im.mul_left
                ((Field51_as_Nat u ^ (p - 2)) ^ 2)
              rw [← mul_pow] at u_eq
              have : (Field51_as_Nat u ^ (p - 2)) ^ 2 *
                  (Field51_as_Nat u ^ 2 *
                  Field51_as_Nat constants.SQRT_M1) =
                  (Field51_as_Nat u ^ (p - 2) *
                  Field51_as_Nat u) ^ 2 *
                  Field51_as_Nat constants.SQRT_M1 := by ring
              rw [this] at u_eq
              have u_eq := u_eq.trans inv_sq
              have u_eq := u_eq.pow 2
              simp only [← pow_mul] at u_eq
              have : (Field51_as_Nat constants.SQRT_M1) ^ 2 ≡
                  p - 1 [MOD p] := by
                unfold constants.SQRT_M1; decide
              exact SQRT_M1_not_square _ (u_eq.trans this)
            · -- case 4: u≠0, v≠0, ¬QR → r2²v ≡ SQRT_M1*u
              intro hu hv hno_qr
              refine ⟨rfl, ?_, ?_⟩
              · rw [mod_sq_mod_mul_eq, ← Nat.ModEq]
                have r2_eq_sq : Field51_as_Nat r2 ^ 2 ≡
                    Field51_as_Nat r_prime ^ 2 [MOD p] := by
                  by_cases h_neg : r_is_negative.val = 1#u8
                  · simp only [h_neg, ite_true] at r2_post
                    have r2_eq_r_neg : Field51_as_Nat r2 =
                        Field51_as_Nat r_neg := by
                      simp only [Field51_as_Nat, Finset.sum_range_succ,
                        Finset.range_one, Finset.sum_singleton]
                      expand r2_post with 5
                      simp_all only [Array.getElem!_Nat_eq,
                        List.Vector.length_val, UScalar.ofNat_val_eq,
                        getElem!_pos, iff_true, Nat.reduceMul,
                        UScalar.neq_to_neq_val, true_iff, Nat.ofNat_pos,
                        Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one,
                        mul_zero, pow_zero, one_mul, mul_one]
                    rw [r2_eq_r_neg]
                    exact nat_sq_of_add_modeq_zero
                      (by rw [add_comm]; exact r_neg_post_1)
                  · simp only [h_neg, if_neg, not_false_eq_true]
                      at r2_post
                    have r2_eq_rprime : Field51_as_Nat r2 =
                        Field51_as_Nat r_prime := by
                      simp only [Field51_as_Nat, Finset.sum_range_succ,
                        Finset.range_one, Finset.sum_singleton]
                      expand r2_post with 5
                      simp_all only [Array.getElem!_Nat_eq,
                        List.Vector.length_val, UScalar.ofNat_val_eq,
                        getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                        Nat.reduceLT, Nat.lt_add_one]
                    rw [r2_eq_rprime]
                exact r2_eq_sq.mul_right _ |>.trans rprime_v
              · intro i hi
                by_cases h : r_is_negative.val = 1#u8
                · simp only [h, ite_true] at r2_post
                  have := r2_post i hi; have := r_neg_post_2 i hi
                  simp_all only [Array.getElem!_Nat_eq,
                    List.Vector.length_val, UScalar.ofNat_val_eq,
                    getElem!_pos, UScalar.neq_to_neq_val, true_iff,
                    getElem?_pos, Option.getD_some, ge_iff_le]
                  have := r_neg_post_2 i hi; omega
                · simp only [h, if_neg, not_false_eq_true] at r2_post
                  simp_all only [Array.getElem!_Nat_eq,
                    List.Vector.length_val, UScalar.ofNat_val_eq,
                    getElem!_pos, UScalar.neq_to_neq_val, false_iff,
                    Nat.mod_two_not_eq_one, getElem?_pos, Option.getD_some]
                  have := r2_post i hi; have := r1_post i hi
                  have := r_prime_post_2 i hi; omega
            · -- case 5: nonneg
              rw [← r1_eq_rprime] at r_is_negative_post r_neg_post_1
              exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
                r_is_negative_post r_neg_post_1 r2_post
      · -- B: second_choice = false (c = Choice.zero, r1 = r)
        simp only [first_choice, second_choice, or_false,
          ↓reduceIte, bind_tc_ok, Array.getElem!_Nat_eq,
          List.getElem!_eq_getElem?_getD, ne_eq, and_imp,
          Nat.mul_mod_mod, forall_exists_index, not_exists, Nat.mod_mul_mod]
        progress*
        · intro i hi
          have h01 : ¬(0#u8 = 1#u8) := by decide
          simp only [Choice.zero, h01, ite_false] at r1_post
          rw [r1_post i hi]
          have := r_post_2 i hi
          omega
        · -- main block B: by_cases on correct_sign_sqrt
          by_cases choice3 : correct_sign_sqrt.val = 1#u8
          · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
            -- B1: second_choice=false, choice3=true
            -- check ≡ u [MOD p] from correct_sign_sqrt
            have h_check_u := correct_sign_sqrt_post.mp
              ((Choice.val_eq_one_iff _).mp choice3)
            have check_eq_u := eq_to_bytes_eq_Field51_as_Nat h_check_u
            rw [← Nat.ModEq] at check_eq_u
            -- r^2 * v ≡ u [MOD p]
            have r_sq_v_u := check_eq_r_v.symm.trans check_eq_u
            -- r1 = r (Choice.zero since second_choice=false)
            have h01 : ¬(0#u8 = 1#u8) := by decide
            simp only [Choice.zero, h01, ite_false] at r1_post
            have r1_eq_r : Field51_as_Nat r1 = Field51_as_Nat r := by
              simp only [Field51_as_Nat, Array.getElem!_Nat_eq,
                List.getElem!_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one,
                Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val,
                UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem?_pos, Option.getD_some,
                one_mul, mul_one, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
                Nat.lt_add_one]
              simp only [Array.getElem!_Nat_eq] at r1_post
              expand r1_post with 5
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                Nat.reduceLT, Nat.lt_add_one]
            rw [r1_eq_r] at r_neg_post_1 r_is_negative_post
            simp only [← modEq_zero_iff]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- case 1: u = 0
              intro hu
              refine ⟨?_, ?_, ?_⟩
              · exact (Choice.val_eq_one_iff Choice.one).mpr rfl
              · have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
                simp only [zero_mul] at this
                have := Nat.ModEq.trans fe2_post_1 this
                have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
                simp only [zero_mul] at this
                have r_eq0 := Nat.ModEq.trans r_post_1 this
                have : Field51_as_Nat r % p % 2 = 0 := by
                  simp only [Nat.ModEq] at r_eq0; rw [r_eq0]; simp only [Nat.zero_mod]
                have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
                  intro h; exact absurd (r_is_negative_post.mp h) (by omega)
                simp only [h_not_neg, if_neg, not_false_eq_true] at r2_post
                have : Field51_as_Nat r2 = Field51_as_Nat r := by
                  simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                    Finset.sum_singleton]
                  expand r2_post with 5
                  simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                    UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                    Nat.reducePow, Nat.add_one_sub_one, Nat.reduceSub, Nat.reduceMul,
                    Nat.reduceAdd, zero_ne_one, mul_zero, UScalar.neq_to_neq_val,
                    Nat.reduceLT, Nat.lt_add_one, pow_zero, one_mul, mul_one]
                rw [this]; exact r_eq0
              · intro i hi
                by_cases h : r_is_negative.val = 1#u8
                · simp only [h, ite_true] at r2_post
                  have := r2_post i hi; have := r_neg_post_2 i hi
                  simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                    UScalar.ofNat_val_eq, getElem!_pos, UScalar.neq_to_neq_val,
                    true_iff, Nat.not_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero,
                    zero_lt_one, not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq,
                    getElem?_pos, Option.getD_some, ge_iff_le]
                  have := r_neg_post_2 i hi; omega
                · simp only [h, if_neg, not_false_eq_true] at r2_post
                  simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                    getElem!_pos, UScalar.neq_to_neq_val,
                    UScalar.ofNat_val_eq, false_iff, Nat.mod_two_not_eq_one, Nat.not_eq, ne_eq, zero_ne_one,
                    not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
                    UScalar.val_not_eq_imp_not_eq, List.Vector.length_val, getElem?_pos,
                    Option.getD_some]
                  have := r2_post i hi; have := r_post_2 i hi
                  omega
            · -- case 2: u≠0, v=0 → contradiction
              intro hu hv; exfalso; apply hu
              have h_v0 := hv.mul_left (Field51_as_Nat r ^ 2)
              simp only [mul_zero] at h_v0
              exact r_sq_v_u.symm.trans h_v0
            · -- case 3: QR exists
              intro hu hv x hx
              refine ⟨?_, ?_, ?_⟩
              · exact (Choice.val_eq_one_iff Choice.one).mpr rfl
              · rw [mod_sq_mod_mul_eq, ← Nat.ModEq]
                have r2_eq_sq : Field51_as_Nat r2 ^ 2 ≡
                    Field51_as_Nat r ^ 2 [MOD p] := by
                  by_cases h_neg : r_is_negative.val = 1#u8
                  · simp only [h_neg, ite_true] at r2_post
                    have r2_eq_r_neg : Field51_as_Nat r2 = Field51_as_Nat r_neg := by
                      simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                        Finset.sum_singleton]
                      expand r2_post with 5
                      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                        UScalar.ofNat_val_eq, getElem!_pos, iff_true, Nat.reduceMul,
                        UScalar.neq_to_neq_val, true_iff, Nat.not_eq, ne_eq, zero_ne_one,
                        not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
                        UScalar.val_not_eq_imp_not_eq, Nat.ofNat_pos, Nat.one_lt_ofNat,
                        Nat.reduceLT, Nat.lt_add_one, mul_zero, pow_zero, one_mul, mul_one]
                    rw [r2_eq_r_neg]
                    exact (nat_sq_of_add_modeq_zero (by rw [add_comm]; exact r_neg_post_1))
                  · simp only [h_neg, if_neg, not_false_eq_true] at r2_post
                    have r2_eq_r : Field51_as_Nat r2 = Field51_as_Nat r := by
                      simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                        Finset.sum_singleton]
                      expand r2_post with 5
                      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                        UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos,
                        Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
                    rw [r2_eq_r]
                exact r2_eq_sq.mul_right _ |>.trans r_sq_v_u
              · intro i hi
                by_cases h : r_is_negative.val = 1#u8
                · simp only [h, ite_true] at r2_post
                  have := r2_post i hi; have := r_neg_post_2 i hi
                  simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                    UScalar.ofNat_val_eq, getElem!_pos, UScalar.neq_to_neq_val,
                    true_iff, Nat.not_eq, ne_eq, zero_ne_one, not_false_eq_true, one_ne_zero,
                    zero_lt_one, not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq,
                    getElem?_pos, Option.getD_some, ge_iff_le]
                  have := r_neg_post_2 i hi; omega
                · simp only [h, if_neg, not_false_eq_true] at r2_post
                  simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                    UScalar.ofNat_val_eq, getElem!_pos, UScalar.neq_to_neq_val,
                    false_iff, Nat.mod_two_not_eq_one, Nat.not_eq, ne_eq, zero_ne_one,
                    not_false_eq_true, one_ne_zero, zero_lt_one, not_lt_zero, or_false, or_self,
                    UScalar.val_not_eq_imp_not_eq, getElem?_pos, Option.getD_some]
                  have := r2_post i hi
                  have := r2_post i hi; have := r_post_2 i hi;
                  omega
            · -- case 4: no QR → contradiction
              intro hu hv hno_qr; exfalso
              exact absurd r_sq_v_u (hno_qr _)
            · rw [← r1_eq_r] at r_is_negative_post r_neg_post_1
              exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
                r_is_negative_post r_neg_post_1 r2_post
          · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
            -- B2: second_choice=false, choice3=false
            -- r1 = r (Choice.zero)
            have h01 : ¬(0#u8 = 1#u8) := by decide
            simp only [Choice.zero, h01, ite_false] at r1_post
            have r1_eq_r : Field51_as_Nat r1 = Field51_as_Nat r := by
              simp only [Field51_as_Nat, Array.getElem!_Nat_eq,
                List.getElem!_eq_getElem?_getD, Finset.sum_range_succ, Finset.range_one,
                Finset.sum_singleton, mul_zero, pow_zero, List.Vector.length_val,
                UScalar.ofNat_val_eq, Nat.ofNat_pos, getElem?_pos, Option.getD_some,
                one_mul, mul_one, Nat.one_lt_ofNat, Nat.reduceMul, Nat.reduceLT,
                Nat.lt_add_one]
              simp only [Array.getElem!_Nat_eq] at r1_post
              expand r1_post with 5
              simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                Nat.reduceLT, Nat.lt_add_one]
            -- Derive ¬(check.to_bytes = _) from the three false choices
            have h_check_ne_u : ¬(check.to_bytes = u.to_bytes) :=
              fun h => choice3 (by rw [correct_sign_sqrt_post.mpr h]; rfl)
            have h_check_ne_fe6 : ¬(check.to_bytes = fe6.to_bytes) :=
              fun h => first_choice (by rw [flipped_sign_sqrt_post.mpr h]; rfl)
            have h_check_ne_fe7 : ¬(check.to_bytes = fe7.to_bytes) :=
              fun h => second_choice (by rw [flipped_sign_sqrt_i_post.mpr h]; rfl)
            rw [r1_eq_r] at r_is_negative_post r_neg_post_1
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- case 1: u = 0 → exfalso (check=0=u contradicts choice3)
              intro hu; exfalso
              rw [← modEq_zero_iff] at hu
              have := check_eq_v.trans
                ((hu.pow (2 + (2 ^ 252 - 3) * 2)).mul_right
                 (Field51_as_Nat v ^ (7 * 2 ^ 253 - 35)))
              simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, ne_eq,
                OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
              rw [modEq_zero_iff] at hu this
              exact h_check_ne_u
                ((to_bytes_zero_of_Field51_as_Nat_zero this).trans
                 (to_bytes_zero_of_Field51_as_Nat_zero hu).symm)
            · -- case 2: u≠0, v=0
              intro hu hv
              rw [← modEq_zero_iff] at hv
              have := hv.mul_left (Field51_as_Nat fe)
              simp only [mul_zero] at this
              have := v3_post_1.trans this
              have := this.mul_left (Field51_as_Nat u)
              simp only [mul_zero] at this
              have := fe2_post_1.trans this
              have := this.mul_right (Field51_as_Nat fe4)
              simp only [zero_mul] at this
              have r_zero := r_post_1.trans this
              have : Field51_as_Nat r % p % 2 = 0 := by
                simp only [Nat.ModEq] at r_zero; rw [r_zero]
                simp only [Nat.zero_mod]
              have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
                intro h; exact absurd (r_is_negative_post.mp h) (by omega)
              simp only [h_not_neg, if_neg, not_false_eq_true] at r2_post
              have r2_eq_r : Field51_as_Nat r2 = Field51_as_Nat r := by
                simp only [Field51_as_Nat, Finset.sum_range_succ, Finset.range_one,
                  Finset.sum_singleton]
                simp only [Array.getElem!_Nat_eq] at r2_post r1_post
                expand r2_post with 5
                expand r1_post with 5
                simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                  UScalar.ofNat_val_eq, getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                  Nat.reducePow, Nat.add_one_sub_one, Nat.reduceSub, Nat.reduceMul,
                  Nat.reduceAdd, zero_ne_one, mul_zero, UScalar.neq_to_neq_val,
                  Nat.reduceLT, Nat.lt_add_one, pow_zero, one_mul, mul_one]
              refine ⟨rfl, ?_, ?_⟩
              · rw [r2_eq_r]; exact r_zero
              · intro i hi
                simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
                  UScalar.ofNat_val_eq, getElem!_pos, getElem?_pos, Option.getD_some]
                have := r2_post i hi; have := r1_post i hi
                have := r_post_2 i hi
                omega
            · -- case 3: u≠0, v≠0, QR → exfalso
              intro hu hv xx hxx; exfalso
              rw [← Nat.ModEq] at hxx
              -- Derive eq_check relating check to xx via Fermat
              have p_eq : 2 + (2 ^ 252 - 3) * 2 + (7 * 2 ^ 253 - 35) =
                  (p - 1) * 2 + 1 := by unfold p; simp
              have p_eq1 : 2 * (2 + (2 ^ 252 - 3) * 2) =
                  (p - 1) / 2 + 2 := by unfold p; omega
              have xx_check :=
                ((hxx.pow (2 + (2 ^ 252 - 3) * 2)).mul_right
                  (Field51_as_Nat v ^ (7 * 2 ^ 253 - 35))).trans
                check_eq_v.symm
              rw [mul_pow, mul_assoc, ← pow_add, p_eq,
                ← pow_mul, p_eq1, pow_add] at xx_check
              -- Use Fermat's little theorem on v
              have h_not_dvd_v : ¬(p ∣ Field51_as_Nat v) := by
                intro h; exact hv (Nat.dvd_iff_mod_eq_zero.mp h)
              have h_coprime_v :=
                coprime_of_prime_not_dvd prime_25519 h_not_dvd_v
              have fermat :=
                ((Nat.ModEq.pow_card_sub_one_eq_one prime_25519
                  h_coprime_v).pow 2).mul_right (Field51_as_Nat v)
              simp only [← pow_mul, pow_add_one, one_pow, one_mul] at fermat
              have fermat :=
                (fermat.mul_left
                  (xx ^ ((p - 1) / 2) * xx ^ 2)).symm.trans xx_check
              -- Case split on xx
              by_cases hxx0 : xx ≡ 0 [MOD p]
              · have := ((hxx0.pow 2).mul_right
                    (Field51_as_Nat v)).symm.trans hxx
                simp at this
                exact hu this.symm
              · -- xx ≠ 0 → Euler criterion on xx
                have := pow_div_two_eq_neg_one_or_one hxx0
                rcases this with hl | hl
                · -- xx^((p-1)/2) ≡ 1 → check ≡ u
                  have := hl.mul_right (xx ^ 2 * Field51_as_Nat v)
                  simp only [← mul_assoc, one_mul] at this
                  have := (fermat.symm.trans this).trans hxx
                  -- this : check ≡ u → check.to_bytes = u.to_bytes
                  obtain ⟨ru, hu_tb, hru_mod, hru_lt⟩ :=
                    spec_imp_exists (to_bytes_spec u)
                  obtain ⟨rcheck, hcheck_tb, hrcheck_mod, hrcheck_lt⟩ :=
                    spec_imp_exists (to_bytes_spec check)
                  have := this.trans hru_mod.symm
                  have check_eq_u := hrcheck_mod.trans this
                  rw [Nat.ModEq] at check_eq_u
                  have := Nat.mod_eq_of_lt hru_lt
                  rw [this] at check_eq_u
                  have := Nat.mod_eq_of_lt hrcheck_lt
                  rw [this] at check_eq_u
                  have := eq_U8x32_as_Nat_eq check_eq_u
                  exact h_check_ne_u (by rw [hcheck_tb, hu_tb, this])
                · -- xx^((p-1)/2) ≡ p-1 → check ≡ fe6
                  have := hl.mul_right (xx ^ 2 * Field51_as_Nat v)
                  simp only [← mul_assoc] at this
                  have fermat := fermat.symm.trans this
                  have := hxx.mul_left (p - 1)
                  simp only [← mul_assoc] at this
                  have fermat :=
                    (fermat.trans this).trans (u_m.mul_left (p - 1))
                  rw [← mul_assoc] at fermat
                  have : (p - 1) * Field51_as_Nat constants.SQRT_M1 ^ 2 ≡
                      1 [MOD p] := by
                    unfold constants.SQRT_M1; decide
                  have := fermat.trans (this.mul_right (Field51_as_Nat fe6))
                  simp at this
                  obtain ⟨ru, hu_tb, hru_mod, hru_lt⟩ :=
                    spec_imp_exists (to_bytes_spec fe6)
                  obtain ⟨rcheck, hcheck_tb, hrcheck_mod, hrcheck_lt⟩ :=
                    spec_imp_exists (to_bytes_spec check)
                  have := this.trans hru_mod.symm
                  have check_eq_fe6 := hrcheck_mod.trans this
                  rw [Nat.ModEq] at check_eq_fe6
                  have := Nat.mod_eq_of_lt hru_lt
                  rw [this] at check_eq_fe6
                  have := Nat.mod_eq_of_lt hrcheck_lt
                  rw [this] at check_eq_fe6
                  have := eq_U8x32_as_Nat_eq check_eq_fe6
                  exact h_check_ne_fe6
                    (by rw [hcheck_tb, hu_tb, this])
            · -- case 4: u≠0, v≠0, ¬QR
              intro hu hv hx
              refine ⟨rfl, ?_, ?_⟩
              · rw [mod_sq_mod_mul_eq, ← Nat.ModEq]
                -- Derive eq_check relating check to (u*v^7)^((p-1)/4) * u
                have eq_check :=
                  (check_eq_v.symm.trans check_eq_r_v).symm
                have : 2 + (2 ^ 252 - 3) * 2 = (p - 1) / 4 + 1 := by
                  unfold p; omega
                rw [this, pow_add] at eq_check
                have : 7 * 2 ^ 253 - 35 = 7 * ((p - 1) / 4) := by
                  unfold p; omega
                rw [this] at eq_check
                simp only [pow_mul, mul_assoc, pow_one] at eq_check
                rw [mul_comm (Field51_as_Nat u) ((Field51_as_Nat v ^ 7) ^ ((p - 1) / 4))] at eq_check
                rw [← mul_assoc, ← mul_pow] at eq_check
                -- eq_check : r²v ≡ (u*v^7)^((p-1)/4) * u [MOD p]
                have h_uv7_ne : ¬ Field51_as_Nat u *
                    Field51_as_Nat v ^ 7 ≡ 0 [MOD p] := by
                  intro h
                  have := mul_zero_eq_or prime_25519 h
                  rcases this with h | h
                  · exact hu ((modEq_zero_iff _ _).mp h)
                  · have : Field51_as_Nat v ≡ 0 [MOD p] := by
                      have hp : Nat.Prime p := Fact.out
                      rw [show (7 : ℕ) = 1 + 6 from rfl, pow_add] at h
                      rcases mul_zero_eq_or prime_25519 h with h1 | h1
                      · simp only [pow_one] at h1; exact h1
                      · rw [show (6 : ℕ) = 1 + 5 from rfl, pow_add] at h1
                        rcases mul_zero_eq_or prime_25519 h1 with h2 | h2
                        · simp only [pow_one] at h2; exact h2
                        · rw [show (5 : ℕ) = 1 + 4 from rfl, pow_add] at h2
                          rcases mul_zero_eq_or prime_25519 h2 with h3 | h3
                          · simp only [pow_one] at h3; exact h3
                          · rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add] at h3
                            rcases mul_zero_eq_or prime_25519 h3 with h4 | h4
                            · simp only [pow_one] at h4; exact h4
                            · rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add] at h4
                              rcases mul_zero_eq_or prime_25519 h4 with h5 | h5
                              · simp only [pow_one] at h5; exact h5
                              · rw [show (2 : ℕ) = 1 + 1 from rfl, pow_add] at h5
                                rcases mul_zero_eq_or prime_25519 h5 with h6 | h6
                                · simp only [pow_one] at h6; exact h6
                                · simp only [pow_one] at h6; exact h6
                    exact hv ((modEq_zero_iff _ _).mp this)
                have := pow_div_four_eq_four_cases h_uv7_ne
                rcases this with h | h
                · -- sub-case 1: ≡ 1 → r²v ≡ u → QR → contradiction
                  have := h.mul_right (Field51_as_Nat u)
                  have := eq_check.trans this
                  simp only [one_mul] at this
                  exact absurd this (hx (Field51_as_Nat r))
                · rcases h with h | h
                  · -- sub-case 2: ≡ SQRT_M1 → r2²v ≡ SQRT_M1*u (desired)
                    have := h.mul_right (Field51_as_Nat u)
                    have := eq_check.trans this
                    simp only at this
                    -- this : r²v ≡ SQRT_M1 * u [MOD p]
                    have r2_eq_sq : Field51_as_Nat r2 ^ 2 ≡
                        Field51_as_Nat r ^ 2 [MOD p] := by
                      by_cases h_neg : r_is_negative.val = 1#u8
                      · simp only [h_neg, ite_true] at r2_post
                        have r2_eq_r_neg : Field51_as_Nat r2 =
                            Field51_as_Nat r_neg := by
                          simp only [Field51_as_Nat, Finset.sum_range_succ,
                            Finset.range_one, Finset.sum_singleton]
                          expand r2_post with 5
                          simp_all only [Array.getElem!_Nat_eq,
                            List.Vector.length_val, UScalar.ofNat_val_eq,
                            getElem!_pos, Nat.reduceMul,
                            UScalar.neq_to_neq_val, true_iff, Nat.not_eq,
                            ne_eq, zero_ne_one, not_false_eq_true,
                            one_ne_zero, zero_lt_one, not_lt_zero, or_false,
                            or_self, UScalar.val_not_eq_imp_not_eq,
                            Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.reduceLT,
                            Nat.lt_add_one, mul_zero, pow_zero, one_mul,
                            mul_one]
                        rw [r2_eq_r_neg]
                        exact nat_sq_of_add_modeq_zero
                          (by rw [add_comm]; exact r_neg_post_1)
                      · simp only [h_neg, if_neg, not_false_eq_true]
                          at r2_post
                        have r2_eq_r : Field51_as_Nat r2 =
                            Field51_as_Nat r := by
                          simp only [Field51_as_Nat, Finset.sum_range_succ,
                            Finset.range_one, Finset.sum_singleton]
                          expand r2_post with 5
                          simp_all only [Array.getElem!_Nat_eq,
                            List.Vector.length_val, UScalar.ofNat_val_eq,
                            getElem!_pos, Nat.ofNat_pos, Nat.one_lt_ofNat,
                            Nat.reduceLT, Nat.lt_add_one]
                        rw [r2_eq_r]
                    exact (r2_eq_sq.mul_right (Field51_as_Nat v)).trans this
                  · rcases h with h | h
                    · -- sub-case 3: ≡ SQRT_M1² → QR → contradiction
                      have := h.mul_right (Field51_as_Nat u)
                      have h := eq_check.trans this
                      have h := h.mul_left
                        (Field51_as_Nat constants.SQRT_M1 ^ 2)
                      simp only [← mul_assoc] at h
                      have : Field51_as_Nat constants.SQRT_M1 ^ 2 *
                          Field51_as_Nat constants.SQRT_M1 ^ 2 ≡
                          1 [MOD p] := by
                        unfold constants.SQRT_M1; decide
                      have := h.trans (this.mul_right (Field51_as_Nat u))
                      simp only [← mul_pow, one_mul] at this
                      exact absurd this
                        (hx (Field51_as_Nat constants.SQRT_M1 *
                          Field51_as_Nat r))
                    · -- sub-case 4: ≡ SQRT_M1³ → check ≡ fe7 → contradiction
                      have := h.mul_right (Field51_as_Nat u)
                      have h := eq_check.trans this
                      have h := (check_eq_r_v.trans h).trans
                        (u_m.mul_left
                          (Field51_as_Nat constants.SQRT_M1 ^ 3))
                      rw [← mul_assoc] at h
                      have : Field51_as_Nat constants.SQRT_M1 ^ 3 *
                          Field51_as_Nat constants.SQRT_M1 ^ 2 ≡
                          Field51_as_Nat constants.SQRT_M1 [MOD p] := by
                        unfold constants.SQRT_M1; decide
                      have := h.trans
                        (this.mul_right (Field51_as_Nat fe6))
                      rw [mul_comm] at fe7_post_1
                      have := this.trans fe7_post_1.symm
                      obtain ⟨ru, hu_tb, hru_mod, hru_lt⟩ :=
                        spec_imp_exists (to_bytes_spec fe7)
                      obtain ⟨rcheck, hcheck_tb, hrcheck_mod,
                        hrcheck_lt⟩ :=
                        spec_imp_exists (to_bytes_spec check)
                      have := this.trans hru_mod.symm
                      have check_eq_fe7 := hrcheck_mod.trans this
                      rw [Nat.ModEq] at check_eq_fe7
                      have := Nat.mod_eq_of_lt hru_lt
                      rw [this] at check_eq_fe7
                      have := Nat.mod_eq_of_lt hrcheck_lt
                      rw [this] at check_eq_fe7
                      have := eq_U8x32_as_Nat_eq check_eq_fe7
                      exact False.elim (h_check_ne_fe7
                        (by rw [hcheck_tb, hu_tb, this]))
              · intro i hi
                by_cases h : r_is_negative.val = 1#u8
                · simp only [h, ite_true] at r2_post
                  have := r2_post i hi; have := r_neg_post_2 i hi
                  simp_all only [Array.getElem!_Nat_eq,
                    List.Vector.length_val, UScalar.ofNat_val_eq,
                    getElem!_pos, UScalar.neq_to_neq_val, true_iff,
                    Nat.not_eq, ne_eq, zero_ne_one, not_false_eq_true,
                    one_ne_zero, zero_lt_one, not_lt_zero, or_false,
                    or_self, UScalar.val_not_eq_imp_not_eq,
                    getElem?_pos, Option.getD_some, ge_iff_le]
                  have := r_neg_post_2 i hi; omega
                · simp only [h, if_neg, not_false_eq_true] at r2_post
                  simp_all only [Array.getElem!_Nat_eq,
                    List.Vector.length_val, UScalar.ofNat_val_eq,
                    getElem!_pos, UScalar.neq_to_neq_val, false_iff,
                    Nat.mod_two_not_eq_one, Nat.not_eq, ne_eq,
                    zero_ne_one, not_false_eq_true, one_ne_zero,
                    zero_lt_one, not_lt_zero, or_false, or_self,
                    UScalar.val_not_eq_imp_not_eq, getElem?_pos,
                    Option.getD_some]
                  have := r2_post i hi; have := r1_post i hi
                  have := r_post_2 i hi; omega
            · -- case 5: nonneg
              rw [← r1_eq_r] at r_is_negative_post r_neg_post_1
              exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
                r_is_negative_post r_neg_post_1 r2_post


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
