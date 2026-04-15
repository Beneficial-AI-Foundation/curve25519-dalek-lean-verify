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
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SqrtM1
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero
/-! # Spec Theorem for `FieldElement51::sqrt_ratio_i`

Specification and proof for `FieldElement51::sqrt_ratio_i`.

This function computes a nonnegative square root of u/v or i*u/v,
(where i = sqrt(-1) = SQRT_M1 constant), returning a flag indicating which case occurred and
handling zero inputs specially.

**Source**: curve25519-dalek/src/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.math
namespace curve25519_dalek.field.FieldElement51

/-- The SQRT_M1 constant as a plain FieldElement51 (alias for `constants.SQRT_M1_raw`). -/
def SQRT_M1_val := backend.serial.u64.constants.SQRT_M1_raw

theorem SQRT_M1_val_spec : (Field51_as_Nat SQRT_M1_val)^2 % p = p - 1 := by
  unfold SQRT_M1_val constants.SQRT_M1_raw; decide

private theorem modEq_zero_of_pow_modEq_zero {a k : ℕ}
    (h : a ^ k ≡ 0 [MOD p]) :
    a ≡ 0 [MOD p] := by
  rw [Nat.modEq_zero_iff_dvd] at h ⊢
  exact prime_25519.dvd_of_dvd_pow h

private theorem sqrt_m1_sq_modEq :
    Field51_as_Nat SQRT_M1_val ^ 2 ≡ p - 1 [MOD p] := by
  simp [Nat.ModEq, SQRT_M1_val_spec]

theorem nat_sqrt_m1_sq_of_add_modeq_zero {a b : ℕ}
  (h : a + b ≡ 0 [MOD p]) :
  a ≡ (Field51_as_Nat SQRT_M1_val) ^ 2 * b [MOD p] := by
  have h_sqrt_eq : (Field51_as_Nat SQRT_M1_val) ^ 2 % p = p - 1 :=
    SQRT_M1_val_spec
  have h_sqrt_mod : (Field51_as_Nat SQRT_M1_val) ^ 2 ≡ p - 1 [MOD p] := by
    exact sqrt_m1_sq_modEq
  have h1 : (Field51_as_Nat SQRT_M1_val) ^ 2 * b ≡ (p - 1) * b [MOD p] := by
    exact h_sqrt_mod.mul_right b
  have hp_pos : 1 ≤ p := by unfold p; simp
  have h2 : (p - 1) * b = p * b - b := by
      rw [Nat.sub_mul _ _ _, Nat.one_mul]
  have h3 : 0 ≡ p * b  [MOD p] := by
    simp only [Nat.ModEq, Nat.zero_mod, Nat.mul_mod_right]
  have : p *b =  b + (p-1) *b  := by unfold p; omega
  rw[this] at h3
  have h4:=h3.add_left a
  have : a + (b + (p - 1) * b) =(a + b) + (p - 1) * b := by omega
  simp only [add_zero, this] at h4
  have h5:=h.add_right ((p - 1) * b)
  have h6:=h4.trans h5
  simp only [zero_add] at h6
  exact h6.trans (h1.symm)

theorem eq_to_bytes_eq_Field51_as_Nat
    {u v : backend.serial.u64.field.FieldElement51}
    (h : u.to_bytes = v.to_bytes) :
  Field51_as_Nat u % p = Field51_as_Nat v % p := by
  classical
  obtain ⟨ru, hu, hru_mod, _⟩ := spec_imp_exists (to_bytes_spec u)
  obtain ⟨rv, hv, hrv_mod, _⟩ := spec_imp_exists (to_bytes_spec v)
  have hrr : ru = rv := by
    have : ok ru = ok rv := by simpa only [ok.injEq, hu, hv] using h
    cases this
    rfl
  have huv_mod : Nat.ModEq p (Field51_as_Nat u) (Field51_as_Nat v) := by
    have h1 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat u) := by
      simpa only [hrr] using hru_mod
    have h2 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat v) := hrv_mod
    exact (Nat.ModEq.symm h1).trans h2
  simpa only [Nat.ModEq] using huv_mod

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
   u.to_bytes = ok (Array.repeat 32#usize 0#u8)  := by
  classical
  obtain ⟨ru, hu, hru_mod, hru_lt⟩ := spec_imp_exists (to_bytes_spec u)
  rw[← modEq_zero_iff] at h
  have := hru_mod.trans h
  have h_bytes_zero:= zero_mod_lt_zero hru_lt this
  obtain ⟨c, c_ok, hc ⟩  := spec_imp_exists (is_zero_spec u)
  have hru_eq : ru = Array.repeat 32#usize 0#u8 := by
    unfold U8x32_as_Nat at h_bytes_zero
    simp_all only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Finset.sum_eq_zero_iff,
      Finset.mem_range, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem?_pos,
      Option.getD_some, mul_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_or,
      false_and]
    apply Subtype.ext
    apply List.ext_getElem
    repeat simp only [List.Vector.length_val, UScalar.ofNatCore_val_eq]
    intro i hi _
    have hi_val := h_bytes_zero i hi
    interval_cases i
    all_goals simp only [Array.repeat, UScalar.ofNatCore_val_eq, List.replicate,
      List.getElem_cons_succ, List.getElem_cons_zero]; grind only [= UScalar.ofNatCore_val_eq]
  rw [← hru_eq]
  exact hu

theorem SQRT_M1_not_square (x : ℕ) :
  ¬ (x ^ 4 ≡ p - 1 [MOD p]) := by
  intro hx
  have hx_z : ((x : ZMod p) ^ 4) = (-1 : ZMod p) := by
    have hcast : (((x ^ 4 : ℕ)) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (by simpa [Nat.ModEq] using hx)
    push_cast at hcast
    rwa [_root_.curve25519_dalek.math.p_sub_one_cast] at hcast
  have hx_sq :
      (((x : ZMod p) ^ 2) ^ 2) = _root_.curve25519_dalek.math.sqrt_m1 ^ 2 := by
    calc
      (((x : ZMod p) ^ 2) ^ 2) = ((x : ZMod p) ^ 4) := by
        rw [show 4 = 2 * 2 by norm_num, pow_mul]
      _ = (-1 : ZMod p) := hx_z
      _ = _root_.curve25519_dalek.math.sqrt_m1 ^ 2 := by
        rw [_root_.curve25519_dalek.math.sqrt_m1_sq]
  have hsquare : IsSquare (_root_.curve25519_dalek.math.sqrt_m1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx_sq with hroot | hroot
    · refine ⟨(x : ZMod p), ?_⟩
      simpa [pow_two] using hroot.symm
    · refine ⟨(x : ZMod p) * _root_.curve25519_dalek.math.sqrt_m1, ?_⟩
      calc
        _root_.curve25519_dalek.math.sqrt_m1 =
            (-_root_.curve25519_dalek.math.sqrt_m1) * (-1 : ZMod p) := by
          ring
        _ = ((x : ZMod p) ^ 2) * (_root_.curve25519_dalek.math.sqrt_m1 ^ 2) := by
          rw [hroot, _root_.curve25519_dalek.math.sqrt_m1_sq]
        _ = ((x : ZMod p) * _root_.curve25519_dalek.math.sqrt_m1) *
              ((x : ZMod p) * _root_.curve25519_dalek.math.sqrt_m1) := by
          ring
  exact _root_.curve25519_dalek.math.sqrt_m1_not_square hsquare

lemma zero_of_mul_SQRT_M1_zero {a : ℕ} (ha : a * Field51_as_Nat SQRT_M1_val ≡ 0 [MOD p]) :
  a ≡ 0 [MOD p] := by
  have eq:= ha.mul_right (Field51_as_Nat SQRT_M1_val)
  simp only [mul_assoc, zero_mul] at eq
  have : Field51_as_Nat SQRT_M1_val * Field51_as_Nat SQRT_M1_val ≡ p-1 [MOD p] := by
    simpa only [pow_two] using sqrt_m1_sq_modEq
  have eq:= ((this.mul_left a).symm.trans eq).add_right a
  rw[(by simp : 0 +a =a)] at eq
  have : a * (p - 1) + a= p * a := by
    unfold p
    omega
  rw[this] at eq
  have : p * a ≡ 0  [MOD p] := by
    rw[Nat.ModEq]
    simp
  apply eq.symm.trans this

theorem pow_div_two_eq_neg_one_or_one {a : ℕ} (ha : ¬ a ≡ 0 [MOD p]) :
    a ^ ((p -1) / 2) ≡ 1 [MOD p]∨ a ^ ((p-1) / 2) ≡ p - 1 [MOD p] := by
    have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1) ≡ 0 [MOD p] := by
      have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1)
        = a ^ ((p -1) ) + p * a ^ ((p -1) / 2) + (p-1) := by
        rw[mul_add, add_mul, (fun a => by ring : ∀ a, a * a = a^2), ← pow_mul]
        simp only [mul_one, ← add_assoc, Nat.add_right_cancel_iff]
        simp only [add_assoc,
          (by ring :
              (p - 1) * a ^ ((p - 1) / 2) + a ^ ((p - 1) / 2) = ((p - 1) + 1) * a ^ ((p - 1) / 2))]
        have : p-1 +1 =p := by unfold p; omega
        rw[this]
        have : (p-1)/2 *2 =p-1 := by unfold p; omega
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
      have : 1 + 0 + (p - 1) =p := by unfold p; omega
      rw[this]
      rw[Nat.modEq_zero_iff_dvd]
    have := mul_zero_eq_or (hp := prime_25519) this
    rcases this with r | l
    · have r:= r.add_right 1
      rw[add_assoc] at r
      have : p-1 +1 =p := by unfold p; omega
      simp[this] at r
      simp[r]
    · have r:= l.add_right (p-1)
      rw[add_assoc] at r
      have :  1 + (p-1) =p := by unfold p; omega
      simp[this] at r
      simp[r]

theorem pow_div_four_eq_four_cases {a : ℕ} (ha : ¬ a ≡ 0 [MOD p]) :
    a ^ ((p -1) / 4) ≡ 1 [MOD p] ∨
    a ^ ((p-1) / 4) ≡ Field51_as_Nat SQRT_M1_val [MOD p] ∨
    a ^ ((p-1) / 4) ≡ (Field51_as_Nat SQRT_M1_val)^2 [MOD p] ∨
    a ^ ((p-1) / 4) ≡ (Field51_as_Nat SQRT_M1_val)^3 [MOD p] := by
  have eq1:  (a ^ ((p -1) / 4) + (p-1)) *
          (a ^ ((p -1) / 4) + 1)
           =
          a ^ ((p -1)/2 ) + p * a ^ ((p -1) / 4) + (p-1)
           := by
        rw[mul_add, add_mul, (fun a => by ring : ∀ a, a * a = a^2), ← pow_mul]
        simp only [mul_one, ← add_assoc, Nat.add_right_cancel_iff]
        simp only [add_assoc,
          (by ring :
              (p - 1) * a ^ ((p - 1) / 4) + a ^ ((p - 1) / 4) = ((p - 1) + 1) * a ^ ((p - 1) / 4))]
        have : p-1 +1 =p := by unfold p; omega
        rw[this]
        have : (p-1)/4 *2 =(p-1)/2 := by unfold p; omega
        rw[this]
  have eq2:  (a ^ ((p -1) / 4) + (p-1)* (Field51_as_Nat SQRT_M1_val)) * (a ^ ((p -1) / 4)
          + Field51_as_Nat SQRT_M1_val) = a ^ ((p -1)/2 ) + p * a ^ ((p -1) / 4)
          * (Field51_as_Nat SQRT_M1_val) + (p-1) *
          Field51_as_Nat SQRT_M1_val * Field51_as_Nat SQRT_M1_val := by
        rw[mul_add, add_mul,add_mul, (fun a => by ring : ∀ a, a * a = a^2), ← pow_mul]
        rw[← add_assoc]
        simp only [add_assoc,
          (by ring :
              (p - 1) * (Field51_as_Nat SQRT_M1_val) * a ^ ((p - 1) / 4) +
                  a ^ ((p - 1) / 4) * Field51_as_Nat SQRT_M1_val =
                ((p - 1) + 1) * a ^ ((p - 1) / 4) * Field51_as_Nat SQRT_M1_val)]
        have : p-1 +1 =p := by unfold p; omega
        rw [this]
        have : (p-1)/4 *2 =(p-1)/2 := by unfold p; omega
        rw[this, ← add_assoc]
  have : (a ^ ((p -1) / 4) + (p-1)) *
          (a ^ ((p -1) / 4) + 1) *
          (a ^ ((p -1) / 4) + (p-1)* (Field51_as_Nat SQRT_M1_val)) *
          (a ^ ((p -1) / 4) + Field51_as_Nat SQRT_M1_val)
          ≡ 0 [MOD p] := by
          simp only [eq1, mul_assoc, eq2]
          have eq1:a ^ ((p -1)/2 ) + p * a ^ ((p -1) / 4) + (p-1) ≡
            a ^ ((p -1)/2 ) + (p-1)
            [MOD p] := by
            simp[Nat.modEq_iff_dvd]
          have : a ^ ((p - 1) / 2) + p * (a ^ ((p - 1) / 4) * Field51_as_Nat SQRT_M1_val) +
            (p - 1) * (Field51_as_Nat SQRT_M1_val * Field51_as_Nat SQRT_M1_val) ≡
            a ^ ((p -1)/2 ) + 1
            [MOD p] := by
            have :(p - 1) * (Field51_as_Nat SQRT_M1_val * Field51_as_Nat SQRT_M1_val)
              ≡ 1 [MOD p]:= by
              unfold SQRT_M1_val
              decide
            have :=this.add_left (a ^ ((p - 1) / 2) + p *
              (a ^ ((p - 1) / 4) * Field51_as_Nat SQRT_M1_val))
            apply Nat.ModEq.trans this
            simp[Nat.modEq_iff_dvd]
          apply (eq1.mul this).trans
          have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1) ≡ 0 [MOD p] := by
            have : (a ^ ((p -1) / 2) + (p -1)) * (a ^ ((p-1) / 2) +1)
              = a ^ ((p -1) ) + p * a ^ ((p -1) / 2) + (p-1) := by
              rw[mul_add, add_mul, (fun a => by ring : ∀ a, a * a = a^2), ← pow_mul]
              simp only [mul_one, ← add_assoc, Nat.add_right_cancel_iff]
              simp only [add_assoc,
                (by ring :
                    (p - 1) * a ^ ((p - 1) / 2) + a ^ ((p - 1) / 2) =
                      ((p - 1) + 1) * a ^ ((p - 1) / 2))]
              have : p-1 +1 =p := by unfold p; omega
              rw[this]
              have : (p-1)/2 *2 =p-1 := by unfold p; omega
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
            have : 1 + 0 + (p - 1) =p := by unfold p; omega
            rw[this]
            rw[Nat.modEq_zero_iff_dvd]
          apply this
  have := mul_zero_eq_or (hp := prime_25519) this
  rcases this with hl | hl
  · have := mul_zero_eq_or (hp := prime_25519) hl
    rcases this with hl | hl
    · have := mul_zero_eq_or (hp := prime_25519) hl
      rcases this with hl | hl
      · have r:= hl.add_right 1
        rw[add_assoc] at r
        have : p-1 +1 =p := by unfold p; omega
        simp[this] at r
        simp[r]
      · have r:= hl.add_right (p-1)
        rw[add_assoc] at r
        have :  1 + (p-1) =p := by unfold p; omega
        simp only [this, zero_add, Nat.add_modulus_modEq_iff] at r
        have :p - 1  ≡Field51_as_Nat SQRT_M1_val ^2  [MOD p]:= by
              exact sqrt_m1_sq_modEq.symm
        have r:= r.trans this
        simp[r]
    · have r:= hl.add_right (Field51_as_Nat SQRT_M1_val)
      rw[add_assoc] at r
      have : (p-1) * Field51_as_Nat SQRT_M1_val + Field51_as_Nat SQRT_M1_val =
        p * (Field51_as_Nat SQRT_M1_val) := by unfold p; omega
      simp[this] at r
      simp[r]
  · have r:= hl.add_right ((p-1)*Field51_as_Nat SQRT_M1_val)
    rw[add_assoc] at r
    have :  Field51_as_Nat SQRT_M1_val + (p-1) * Field51_as_Nat SQRT_M1_val
      = p * (Field51_as_Nat SQRT_M1_val) := by unfold p; omega
    simp only [this, zero_add, Nat.add_modulus_mul_modEq_iff] at r
    have : (p - 1) * (Field51_as_Nat SQRT_M1_val)  ≡Field51_as_Nat SQRT_M1_val ^3  [MOD p]:= by
              unfold SQRT_M1_val
              decide
    have r:= r.trans this
    simp [r]

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

/-- Whole-element `Field51_as_Nat` equality from pointwise limb-value equality. -/
private theorem field51_as_Nat_eq_of_pointwise_eq
    {x y : backend.serial.u64.field.FieldElement51}
    (hxy : ∀ i < 5, x[i]!.val = y[i]!.val) :
    Field51_as_Nat x = Field51_as_Nat y := by
  unfold Field51_as_Nat
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun t => 2 ^ (51 * i) * t) (hxy i (by simpa only [Finset.mem_range] using hi))

/-- Whole-element consequence of a limbwise `conditional_assign` postcondition. -/
private theorem field51_as_Nat_conditional_assign
    (x y z : backend.serial.u64.field.FieldElement51)
    (c : subtle.Choice)
    (z_post : ∀ i < 5, z[i]! = if c.val = 1#u8 then y[i]! else x[i]!) :
    Field51_as_Nat z =
      if c.val = 1#u8 then Field51_as_Nat y else Field51_as_Nat x := by
  by_cases h : c.val = 1#u8
  · simp only [h, ↓reduceIte]
    refine field51_as_Nat_eq_of_pointwise_eq ?_
    intro i hi
    have hz := z_post i hi
    simp only [h, ↓reduceIte] at hz
    simpa only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using
      congrArg UScalar.val hz
  · simp only [h, ↓reduceIte]
    refine field51_as_Nat_eq_of_pointwise_eq ?_
    intro i hi
    have hz := z_post i hi
    simp only [h, ↓reduceIte] at hz
    simpa only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using
      congrArg UScalar.val hz

/-- Whole-element consequence of taking the right branch in `conditional_assign`. -/
private theorem field51_as_Nat_conditional_assign_eq_right
    (x y z : backend.serial.u64.field.FieldElement51)
    (c : subtle.Choice)
    (hc : c.val = 1#u8)
    (z_post : ∀ i < 5, z[i]! = if c.val = 1#u8 then y[i]! else x[i]!) :
    Field51_as_Nat z = Field51_as_Nat y := by
  simpa only [hc, ↓reduceIte] using
    field51_as_Nat_conditional_assign x y z c z_post

/-- Whole-element consequence of taking the left branch in `conditional_assign`. -/
private theorem field51_as_Nat_conditional_assign_eq_left
    (x y z : backend.serial.u64.field.FieldElement51)
    (c : subtle.Choice)
    (hc : c.val ≠ 1#u8)
    (z_post : ∀ i < 5, z[i]! = if c.val = 1#u8 then y[i]! else x[i]!) :
    Field51_as_Nat z = Field51_as_Nat x := by
  simpa only [hc, ↓reduceIte] using
    field51_as_Nat_conditional_assign x y z c z_post

/-- Convert a pointwise postcondition into whole-element equality on `Field51_as_Nat`. -/
private theorem field51_as_Nat_eq_of_post
    (base x : backend.serial.u64.field.FieldElement51)
    (x_post : ∀ i < 5, x[i]! = base[i]!) :
    Field51_as_Nat x = Field51_as_Nat base := by
  refine field51_as_Nat_eq_of_pointwise_eq ?_
  intro i hi
  simpa only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using
    congrArg UScalar.val (x_post i hi)

/-- `conditional_negate` preserves the represented square modulo `p`. -/
private theorem conditional_negate_sq
    (r1 x r2 : backend.serial.u64.field.FieldElement51)
    (r_is_negative : subtle.Choice)
    (x_post_1 : Field51_as_Nat r1 + Field51_as_Nat x ≡ 0 [MOD p])
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then x[i]! else r1[i]!) :
    Field51_as_Nat r2 ^ 2 ≡ Field51_as_Nat r1 ^ 2 [MOD p] := by
  have hr2 :=
    field51_as_Nat_conditional_assign r1 x r2 r_is_negative r2_post
  by_cases h : r_is_negative.val = 1#u8
  · have hr2x : Field51_as_Nat r2 = Field51_as_Nat x := by
      simpa only [h] using hr2
    rw [hr2x]
    exact (nat_sq_of_add_modeq_zero x_post_1).symm
  · have hr2r1 : Field51_as_Nat r2 = Field51_as_Nat r1 := by
      simpa only [h] using hr2
    rw [hr2r1]

/-- After `conditional_negate`, the result `r2` is always non-negative (even mod p). -/
private theorem conditional_negate_nonneg
    (r1 x r2 : backend.serial.u64.field.FieldElement51)
    (r_is_negative : subtle.Choice)
    (r_is_negative_post : r_is_negative.val = 1#u8 ↔ Field51_as_Nat r1 % p % 2 = 1)
    (x_post_1 : Field51_as_Nat r1 + Field51_as_Nat x ≡ 0 [MOD p])
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then x[i]! else r1[i]!) :
    Field51_as_Nat r2 % p % 2 = 0 := by
  have hr2 :=
    field51_as_Nat_conditional_assign r1 x r2 r_is_negative r2_post
  by_cases h : r_is_negative.val = 1#u8
  · have hr2x : Field51_as_Nat r2 = Field51_as_Nat x := by
      simpa only [h] using hr2
    rw [hr2x]
    exact nonneg_of_neg_mod_p (Field51_as_Nat r1) (Field51_as_Nat x)
      ((modEq_zero_iff _ _).mp x_post_1) (r_is_negative_post.mp h)
  · have hr2r1 : Field51_as_Nat r2 = Field51_as_Nat r1 := by
      simpa only [h] using hr2
    rw [hr2r1]
    have := Nat.mod_two_eq_zero_or_one (Field51_as_Nat r1 % p)
    have := mt r_is_negative_post.mpr h
    omega

/-- Limb bounds after `conditional_negate`: either the negated value or the original value. -/
private theorem conditional_negate_bounds_of_eq
    (base r1 x r2 : backend.serial.u64.field.FieldElement51)
    (r_is_negative : subtle.Choice)
    (r1_post : ∀ i < 5, r1[i]! = base[i]!)
    (base_bounds : ∀ i < 5, base[i]!.val < 2 ^ 52)
    (x_bounds : ∀ i < 5, x[i]!.val ≤ 2 ^ 52)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then x[i]! else r1[i]!) :
    ∀ i < 5, r2[i]!.val ≤ 2 ^ 53 - 1 := by
  intro i hi
  by_cases h : r_is_negative.val = 1#u8
  · have hr2x : r2[i]!.val = x[i]!.val := by
      simpa only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h, ↓reduceIte] using
        congrArg UScalar.val (r2_post i hi)
    rw [hr2x]
    have hx := x_bounds i hi
    omega
  · have hr2r1 : r2[i]!.val = r1[i]!.val := by
      simpa only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, h, ↓reduceIte] using
        congrArg UScalar.val (r2_post i hi)
    have hr1base : r1[i]!.val = base[i]!.val := by
      simpa only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using
        congrArg UScalar.val (r1_post i hi)
    have hbase := base_bounds i hi
    omega

/-- Common square-preservation branch pattern after `conditional_negate`. -/
private theorem conditional_negate_sq_mul_eq_of_modeq
    (base r1 x r2 : backend.serial.u64.field.FieldElement51)
    (r_is_negative : subtle.Choice)
    (b rhs : ℕ)
    (r1_eq : Field51_as_Nat r1 = Field51_as_Nat base)
    (x_post_1 : Field51_as_Nat r1 + Field51_as_Nat x ≡ 0 [MOD p])
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then x[i]! else r1[i]!)
    (hbase : Field51_as_Nat base ^ 2 * b ≡ rhs [MOD p]) :
    ((Field51_as_Nat r2 % p) ^ 2 * b) % p = rhs % p := by
  rw [mod_sq_mod_mul_eq, ← Nat.ModEq]
  have r2_eq_sq := conditional_negate_sq r1 x r2 r_is_negative x_post_1 r2_post
  rw [r1_eq] at r2_eq_sq
  exact r2_eq_sq.mul_right b |>.trans hbase

/-- If `conditional_negate` does not negate, the output still represents the base element. -/
private theorem conditional_negate_eq_of_not_negative
    (base r1 x r2 : backend.serial.u64.field.FieldElement51)
    (r_is_negative : subtle.Choice)
    (h_not_neg : r_is_negative.val ≠ 1#u8)
    (r1_eq : Field51_as_Nat r1 = Field51_as_Nat base)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then x[i]! else r1[i]!) :
    Field51_as_Nat r2 = Field51_as_Nat base := by
  calc
    Field51_as_Nat r2 = Field51_as_Nat r1 := by
      exact field51_as_Nat_conditional_assign_eq_left r1 x r2 r_is_negative h_not_neg r2_post
    _ = Field51_as_Nat base := r1_eq

/-- Main algebraic bridge before the branch split in `sqrt_ratio_i`. -/
private theorem check_eq_v_of_sqrt_ratio_data
    (u v fe v3 fe1 v7 fe2 fe3 fe4 r fe5 check :
      backend.serial.u64.field.FieldElement51)
    (check_post1 :
      Field51_as_Nat check ≡ Field51_as_Nat v * Field51_as_Nat fe5 [MOD p])
    (fe5_post1 :
      Field51_as_Nat fe5 ≡ Field51_as_Nat r ^ 2 [MOD p])
    (r_post1 :
      Field51_as_Nat r ≡ Field51_as_Nat fe2 * Field51_as_Nat fe4 [MOD p])
    (fe4_post1 :
      Field51_as_Nat fe4 % p = Field51_as_Nat fe3 ^ (2 ^ 252 - 3) % p)
    (fe3_post1 :
      Field51_as_Nat fe3 ≡ Field51_as_Nat u * Field51_as_Nat v7 [MOD p])
    (fe2_post1 :
      Field51_as_Nat fe2 ≡ Field51_as_Nat u * Field51_as_Nat v3 [MOD p])
    (v7_post1 :
      Field51_as_Nat v7 ≡ Field51_as_Nat fe1 * Field51_as_Nat v [MOD p])
    (fe1_post1 :
      Field51_as_Nat fe1 ≡ Field51_as_Nat v3 ^ 2 [MOD p])
    (v3_post1 :
      Field51_as_Nat v3 ≡ Field51_as_Nat fe * Field51_as_Nat v [MOD p])
    (fe_post1 :
      Field51_as_Nat fe ≡ Field51_as_Nat v ^ 2 [MOD p]) :
    Field51_as_Nat check ≡
      Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) *
        Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) [MOD p] := by
  apply check_post1.trans
  have := fe5_post1.mul_left (Field51_as_Nat v)
  apply this.trans
  have := r_post1.pow 2
  rw [mul_pow] at this
  have := this.mul_left (Field51_as_Nat v)
  apply this.trans
  rw [← Nat.ModEq] at fe4_post1
  have eq1 := Nat.ModEq.pow 2 fe4_post1
  rw [← pow_mul] at eq1
  have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) fe3_post1
  have eq2 := Nat.ModEq.trans eq1 this
  rw [mul_pow] at eq2
  have := Nat.ModEq.mul_right (Field51_as_Nat v) fe_post1
  have eq_v3 := Nat.ModEq.trans v3_post1 this
  rw [← pow_succ] at eq_v3
  have := Nat.ModEq.pow 2 eq_v3
  rw [← pow_mul] at this
  have := Nat.ModEq.trans fe1_post1 this
  have := Nat.ModEq.mul_right (Field51_as_Nat v) this
  rw [← pow_succ] at this
  have := Nat.ModEq.trans v7_post1 this
  have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) this
  rw [← pow_mul] at this
  have := Nat.ModEq.mul_left (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2)) this
  have eq3 := Nat.ModEq.trans eq2 this
  have := Nat.ModEq.mul_left (Field51_as_Nat u) eq_v3
  have := Nat.ModEq.trans fe2_post1 this
  have eq4 := Nat.ModEq.pow 2 this
  rw [mul_pow] at eq4
  have := Nat.ModEq.mul eq4 eq3
  have := Nat.ModEq.mul_left (Field51_as_Nat v) this
  apply Nat.ModEq.trans this
  have :
      Field51_as_Nat v *
        (Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
          (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) *
            Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2)))) =
      Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) *
        Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) := by
    simp only [Nat.reduceAdd, Nat.reduceMul]
    ring
  rw [this]

/-- Main algebraic bridge before the branch split in `sqrt_ratio_i`. -/
private theorem check_eq_mod_of_sqrt_ratio_data
    (u v fe v3 fe1 v7 fe2 fe3 fe4 r fe5 check r_prime :
      backend.serial.u64.field.FieldElement51)
    (r_prime_post1 :
      Field51_as_Nat r_prime ≡
        Field51_as_Nat SQRT_M1_val * Field51_as_Nat r [MOD p])
    (check_post1 :
      Field51_as_Nat check ≡ Field51_as_Nat v * Field51_as_Nat fe5 [MOD p])
    (fe5_post1 :
      Field51_as_Nat fe5 ≡ Field51_as_Nat r ^ 2 [MOD p])
    (r_post1 :
      Field51_as_Nat r ≡ Field51_as_Nat fe2 * Field51_as_Nat fe4 [MOD p])
    (fe4_post1 :
      Field51_as_Nat fe4 % p = Field51_as_Nat fe3 ^ (2 ^ 252 - 3) % p)
    (fe3_post1 :
      Field51_as_Nat fe3 ≡ Field51_as_Nat u * Field51_as_Nat v7 [MOD p])
    (fe2_post1 :
      Field51_as_Nat fe2 ≡ Field51_as_Nat u * Field51_as_Nat v3 [MOD p])
    (v7_post1 :
      Field51_as_Nat v7 ≡ Field51_as_Nat fe1 * Field51_as_Nat v [MOD p])
    (fe1_post1 :
      Field51_as_Nat fe1 ≡ Field51_as_Nat v3 ^ 2 [MOD p])
    (v3_post1 :
      Field51_as_Nat v3 ≡ Field51_as_Nat fe * Field51_as_Nat v [MOD p])
    (fe_post1 :
      Field51_as_Nat fe ≡ Field51_as_Nat v ^ 2 [MOD p]) :
    Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v ≡
      Field51_as_Nat SQRT_M1_val ^ 2 * Field51_as_Nat check [MOD p] := by
  have eq1_mod :
      Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v ≡
        Field51_as_Nat SQRT_M1_val ^ 2 *
          (Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) *
            Field51_as_Nat v ^ (7 * 2 ^ 253 - 35)) [MOD p] := by
    have := r_prime_post1.pow 2
    rw [mul_pow] at this
    have := this.mul_right (Field51_as_Nat v)
    apply this.trans
    rw [mul_assoc]
    apply Nat.ModEq.mul_left
    have := Nat.ModEq.pow 2 r_post1
    rw [mul_pow] at this
    have := this.mul_right (Field51_as_Nat v)
    apply this.trans
    rw [← Nat.ModEq] at fe4_post1
    have eq1 := fe4_post1.pow 2
    rw [← pow_mul] at eq1
    have := fe3_post1.pow ((2 ^ 252 - 3) * 2)
    have eq2 := eq1.trans this
    rw [mul_pow] at eq2
    have := fe_post1.mul_right (Field51_as_Nat v)
    have eq_v3 := v3_post1.trans this
    rw [← pow_succ] at eq_v3
    have := eq_v3.pow 2
    rw [← pow_mul] at this
    have := fe1_post1.trans this
    have := this.mul_right (Field51_as_Nat v)
    rw [← pow_succ] at this
    have := v7_post1.trans this
    have := this.pow ((2 ^ 252 - 3) * 2)
    rw [← pow_mul] at this
    have := this.mul_left (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2))
    have eq3 := eq2.trans this
    have := eq_v3.mul_left (Field51_as_Nat u)
    have := fe2_post1.trans this
    have eq4 := this.pow 2
    rw [mul_pow] at eq4
    have := eq4.mul eq3
    have := this.mul_right (Field51_as_Nat v)
    apply this.trans
    have :
        Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
          (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) *
            Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2))) *
          Field51_as_Nat v =
        (Field51_as_Nat u ^ 2 * Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2)) *
          ((Field51_as_Nat v ^ (2 + 1)) ^ 2 *
            Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2)) *
            Field51_as_Nat v) := by
      simp
      ring
    rw [this]
    rw [← pow_add, ← pow_mul, ← pow_add, ← pow_succ,
      (by
        omega :
          (2 + 1) * 2 + ((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2) + 1 =
            7 * 2 ^ 253 - 35)]
  have check_eq_v :=
    check_eq_v_of_sqrt_ratio_data u v fe v3 fe1 v7 fe2 fe3 fe4 r fe5 check
      check_post1 fe5_post1 r_post1 fe4_post1 fe3_post1 fe2_post1
      v7_post1 fe1_post1 v3_post1 fe_post1
  have := Nat.ModEq.mul_left (Field51_as_Nat SQRT_M1_val ^ 2) check_eq_v
  exact eq1_mod.trans this.symm

private theorem modEq_zero_of_sqrt_m1_mul_self {a : ℕ}
    (h : Field51_as_Nat SQRT_M1_val * a ≡ a [MOD p]) :
    a % p = 0 := by
  have hp : Nat.Prime p := Fact.out
  have h_le : a ≤ Field51_as_Nat SQRT_M1_val * a :=
    le_mul_of_one_le_left (Nat.zero_le _)
      (by unfold SQRT_M1_val Field51_as_Nat; decide)
  have h_dvd := (Nat.modEq_iff_dvd' h_le).mp h.symm
  have h_eq := Nat.sub_mul (Field51_as_Nat SQRT_M1_val) 1 a
  rw [one_mul] at h_eq
  rw [← h_eq] at h_dvd
  rcases hp.dvd_mul.mp h_dvd with h1 | h2
  · exfalso
    exact (show ¬(p ∣ (Field51_as_Nat SQRT_M1_val - 1)) from by
      unfold p SQRT_M1_val Field51_as_Nat
      decide) h1
  · rcases h2 with ⟨k, hk⟩
    rw [hk]
    exact Nat.mul_mod_right p k

/-- Bundled postcondition for a fully normalized `sqrt_ratio_i` result. -/
private abbrev sqrt_ratio_i_cases
    (u v r2 : backend.serial.u64.field.FieldElement51)
    (c : subtle.Choice) : Prop :=
  (Field51_as_Nat u % p = 0 →
      c.val = 1#u8 ∧ Field51_as_Nat r2 % p = 0 ∧
        (∀ i < 5, r2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    (Field51_as_Nat u % p ≠ 0 ∧ Field51_as_Nat v % p = 0 →
      c.val = 0#u8 ∧ Field51_as_Nat r2 % p = 0 ∧
        (∀ i < 5, r2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    (Field51_as_Nat u % p ≠ 0 ∧ Field51_as_Nat v % p ≠ 0 ∧
        (∃ x : Nat, (x ^ 2 * (Field51_as_Nat v % p)) % p = Field51_as_Nat u % p) →
      c.val = 1#u8 ∧
        ((Field51_as_Nat r2 % p) ^ 2 * (Field51_as_Nat v % p)) % p =
          Field51_as_Nat u % p ∧
        (∀ i < 5, r2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    ((Field51_as_Nat u % p ≠ 0 ∧ Field51_as_Nat v % p ≠ 0 ∧
        ¬∃ x : Nat, (x ^ 2 * (Field51_as_Nat v % p)) % p = Field51_as_Nat u % p) →
      c.val = 0#u8 ∧
        ((Field51_as_Nat r2 % p) ^ 2 * (Field51_as_Nat v % p)) % p =
          ((Field51_as_Nat SQRT_M1_val % p) * (Field51_as_Nat u % p)) % p ∧
        (∀ i < 5, r2[i]!.val ≤ 2 ^ 53 - 1)) ∧
    (Field51_as_Nat r2 % p % 2 = 0)

section sqrt_ratio_i_branch_solvers

variable
  {u v fe v3 fe2 fe4 r fe5 check fe6 fe7 r_prime r1 r_neg r2 :
    backend.serial.u64.field.FieldElement51}
  {r_is_negative : subtle.Choice}

/-- Solves the branch where `check = -u`, so `r_prime` is the square root candidate. -/
private theorem solve_first_choice_true
    (check_fe6 : Field51_as_Nat check ≡ Field51_as_Nat fe6 [MOD p])
    (r_prime_sq_v_u : Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v ≡
      Field51_as_Nat u [MOD p])
    (check_post1 : Field51_as_Nat check ≡ Field51_as_Nat v * Field51_as_Nat fe5 [MOD p])
    (fe6_post1 : Field51_as_Nat u + Field51_as_Nat fe6 ≡ 0 [MOD p])
    (fe2_post1 : Field51_as_Nat fe2 ≡ Field51_as_Nat u * Field51_as_Nat v3 [MOD p])
    (r_post1 : Field51_as_Nat r ≡ Field51_as_Nat fe2 * Field51_as_Nat fe4 [MOD p])
    (r_prime_post1 : Field51_as_Nat r_prime ≡
      Field51_as_Nat SQRT_M1_val * Field51_as_Nat r [MOD p])
    (r1_post : ∀ i < 5, r1[i]! = r_prime[i]!)
    (r_prime_post2 : ∀ i < 5, r_prime[i]!.val < 2 ^ 52)
    (r_neg_post1 : Field51_as_Nat r1 + Field51_as_Nat r_neg ≡ 0 [MOD p])
    (r_neg_post2 : ∀ i < 5, r_neg[i]!.val ≤ 2 ^ 52)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then r_neg[i]! else r1[i]!)
    (r_is_negative_post : r_is_negative.val = 1#u8 ↔ Field51_as_Nat r1 % p % 2 = 1) :
    sqrt_ratio_i_cases u v r2 Choice.one := by
  have r1_eq : Field51_as_Nat r1 = Field51_as_Nat r_prime :=
    field51_as_Nat_eq_of_post r_prime r1 r1_post
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hu
    rw [← modEq_zero_iff] at hu
    refine ⟨(Choice.val_eq_one_iff Choice.one).mpr rfl, ?_, ?_⟩
    · have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
      simp only [zero_mul] at this
      have := Nat.ModEq.trans fe2_post1 this
      have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
      simp only [zero_mul] at this
      have := Nat.ModEq.trans r_post1 this
      have := Nat.ModEq.mul_left (Field51_as_Nat SQRT_M1_val) this
      have r_prime_eq0 := Nat.ModEq.trans r_prime_post1 this
      simp only [mul_zero] at r_prime_eq0
      rw [r1_eq] at r_neg_post1 r_is_negative_post
      have : Field51_as_Nat r_prime % p % 2 = 0 := by
        simp only [Nat.ModEq] at r_prime_eq0
        rw [r_prime_eq0]
        simp only [Nat.zero_mod]
      have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
        intro h
        exact absurd (r_is_negative_post.mp h) (by omega)
      have r2_eq_rprime : Field51_as_Nat r2 = Field51_as_Nat r_prime :=
        conditional_negate_eq_of_not_negative r_prime r1 r_neg r2 r_is_negative
          h_not_neg r1_eq r2_post
      rw [r2_eq_rprime]
      exact r_prime_eq0
    · exact conditional_negate_bounds_of_eq r_prime r1 r_neg r2 r_is_negative
        r1_post r_prime_post2 r_neg_post2 r2_post
  · intro huv
    rcases huv with ⟨hu, hv⟩
    exfalso
    apply hu
    rw [← modEq_zero_iff] at hv
    have check0 : Field51_as_Nat check ≡ 0 [MOD p] := by
      have := hv.mul_right (Field51_as_Nat fe5)
      simp only [zero_mul] at this
      exact check_post1.trans this
    have fe6_zero := check_fe6.symm.trans check0
    have h_sum := fe6_zero.add_left (Field51_as_Nat u)
    simp only [Nat.add_zero] at h_sum
    exact h_sum.symm.trans fe6_post1
  · intro huv
    rcases huv with ⟨hu, hv, x, hx⟩
    refine ⟨(Choice.val_eq_one_iff Choice.one).mpr rfl, ?_, ?_⟩
    · exact conditional_negate_sq_mul_eq_of_modeq
        r_prime r1 r_neg r2 r_is_negative
        (Field51_as_Nat v % p)
        (Field51_as_Nat u)
        r1_eq
        (by simpa only [r1_eq] using r_neg_post1)
        r2_post
        (by
          simpa [Nat.ModEq, Nat.mul_mod, Nat.mod_mod] using r_prime_sq_v_u)
    · exact conditional_negate_bounds_of_eq r_prime r1 r_neg r2 r_is_negative
        r1_post r_prime_post2 r_neg_post2 r2_post
  · intro huv
    rcases huv with ⟨hu, hv, hno_qr⟩
    exfalso
    exact hno_qr ⟨Field51_as_Nat r_prime, by
      simpa [Nat.ModEq, Nat.mul_mod, Nat.mod_mod] using r_prime_sq_v_u⟩
  · exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
      r_is_negative_post r_neg_post1 r2_post

/-- Solves the branch where `check = u` and `check = -u*i`, forcing `u = 0`. -/
private theorem solve_second_choice_true_choice3_true
    (sqrt_m1_u : Field51_as_Nat SQRT_M1_val * Field51_as_Nat u ≡
      Field51_as_Nat u [MOD p])
    (fe2_post1 : Field51_as_Nat fe2 ≡ Field51_as_Nat u * Field51_as_Nat v3 [MOD p])
    (r_post1 : Field51_as_Nat r ≡ Field51_as_Nat fe2 * Field51_as_Nat fe4 [MOD p])
    (r_prime_post1 : Field51_as_Nat r_prime ≡
      Field51_as_Nat SQRT_M1_val * Field51_as_Nat r [MOD p])
    (r1_post : ∀ i < 5, r1[i]! = r_prime[i]!)
    (r_prime_post2 : ∀ i < 5, r_prime[i]!.val < 2 ^ 52)
    (r_neg_post2 : ∀ i < 5, r_neg[i]!.val ≤ 2 ^ 52)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then r_neg[i]! else r1[i]!)
    (r_is_negative_post : r_is_negative.val = 1#u8 ↔ Field51_as_Nat r1 % p % 2 = 1) :
    sqrt_ratio_i_cases u v r2 Choice.one := by
  have h_u_zero : Field51_as_Nat u % p = 0 :=
    modEq_zero_of_sqrt_m1_mul_self sqrt_m1_u
  have r1_eq_rprime : Field51_as_Nat r1 = Field51_as_Nat r_prime :=
    field51_as_Nat_eq_of_post r_prime r1 r1_post
  have hu : Nat.ModEq p (Field51_as_Nat u) 0 := by
    rw [Nat.ModEq, Nat.zero_mod]
    exact h_u_zero
  have := hu.mul_right (Field51_as_Nat v3)
  simp only [zero_mul] at this
  have := fe2_post1.trans this
  have := this.mul_right (Field51_as_Nat fe4)
  simp only [zero_mul] at this
  have r_eq0 := r_post1.trans this
  have := r_eq0.mul_left (Field51_as_Nat SQRT_M1_val)
  simp only [mul_zero] at this
  have r_prime_eq0 := r_prime_post1.trans this
  have r_is_neg_rprime :
      r_is_negative.val = 1#u8 ↔ Field51_as_Nat r_prime % p % 2 = 1 := by
    rw [← r1_eq_rprime]
    exact r_is_negative_post
  have h_rprime_parity : Field51_as_Nat r_prime % p % 2 = 0 := by
    simp only [Nat.ModEq] at r_prime_eq0
    rw [r_prime_eq0]
    simp only [Nat.zero_mod]
  have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
    intro h
    exact absurd (r_is_neg_rprime.mp h) (by omega)
  have r2_eq_rprime : Field51_as_Nat r2 = Field51_as_Nat r_prime :=
    conditional_negate_eq_of_not_negative r_prime r1 r_neg r2 r_is_negative
      h_not_neg r1_eq_rprime r2_post
  have hr2_bounds : ∀ i < 5, r2[i]!.val ≤ 2 ^ 53 - 1 :=
    conditional_negate_bounds_of_eq r_prime r1 r_neg r2 r_is_negative
      r1_post r_prime_post2 r_neg_post2 r2_post
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _
    refine ⟨(Choice.val_eq_one_iff Choice.one).mpr rfl, ?_, ?_⟩
    · rw [r2_eq_rprime]
      exact r_prime_eq0
    · exact hr2_bounds
  · intro huv
    rcases huv with ⟨hu, _hv⟩
    exfalso
    exact hu h_u_zero
  · intro huv
    rcases huv with ⟨hu, _hv, _hx⟩
    exfalso
    exact hu h_u_zero
  · intro huv
    rcases huv with ⟨hu, _hv, _hno_qr⟩
    exfalso
    exact hu h_u_zero
  · rw [r2_eq_rprime]
    exact h_rprime_parity

/-- Solves the nonsquare `r_prime` branch, proving the `i*u` output case. -/
private theorem solve_second_choice_true_choice3_false
    (u_eq1 : Field51_as_Nat SQRT_M1_val * Field51_as_Nat check ≡
      Field51_as_Nat u [MOD p])
    (rprime_v : Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v ≡
      Field51_as_Nat SQRT_M1_val * Field51_as_Nat u [MOD p])
    (h_check_ne_u : ¬(check.to_bytes = u.to_bytes))
    (v3_post1 : Field51_as_Nat v3 ≡ Field51_as_Nat fe * Field51_as_Nat v [MOD p])
    (fe2_post1 : Field51_as_Nat fe2 ≡ Field51_as_Nat u * Field51_as_Nat v3 [MOD p])
    (r_post1 : Field51_as_Nat r ≡ Field51_as_Nat fe2 * Field51_as_Nat fe4 [MOD p])
    (r_prime_post1 : Field51_as_Nat r_prime ≡
      Field51_as_Nat SQRT_M1_val * Field51_as_Nat r [MOD p])
    (r1_post : ∀ i < 5, r1[i]! = r_prime[i]!)
    (r_prime_post2 : ∀ i < 5, r_prime[i]!.val < 2 ^ 52)
    (r_neg_post1 : Field51_as_Nat r1 + Field51_as_Nat r_neg ≡ 0 [MOD p])
    (r_neg_post2 : ∀ i < 5, r_neg[i]!.val ≤ 2 ^ 52)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then r_neg[i]! else r1[i]!)
    (r_is_negative_post : r_is_negative.val = 1#u8 ↔ Field51_as_Nat r1 % p % 2 = 1) :
    sqrt_ratio_i_cases u v r2 Choice.zero := by
  have r1_eq_rprime : Field51_as_Nat r1 = Field51_as_Nat r_prime :=
    field51_as_Nat_eq_of_post r_prime r1 r1_post
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hu
    exfalso
    rw [← modEq_zero_iff] at hu
    have := u_eq1.trans hu
    rw [mul_comm] at this
    have check_zero := zero_of_mul_SQRT_M1_zero this
    rw [modEq_zero_iff] at check_zero hu
    exact h_check_ne_u
      ((to_bytes_zero_of_Field51_as_Nat_zero check_zero).trans
       (to_bytes_zero_of_Field51_as_Nat_zero hu).symm)
  · intro huv
    rcases huv with ⟨hu, hv⟩
    rw [← modEq_zero_iff] at hv
    have := hv.mul_left (Field51_as_Nat fe)
    simp only [mul_zero] at this
    have := v3_post1.trans this
    have := this.mul_left (Field51_as_Nat u)
    simp only [mul_zero] at this
    have := fe2_post1.trans this
    have := this.mul_right (Field51_as_Nat fe4)
    simp only [zero_mul] at this
    have r_zero := r_post1.trans this
    have := r_zero.mul_left (Field51_as_Nat SQRT_M1_val)
    simp only [mul_zero] at this
    have rprime_zero := r_prime_post1.trans this
    have h_rprime_parity : Field51_as_Nat r_prime % p % 2 = 0 := by
      simp only [Nat.ModEq] at rprime_zero
      rw [rprime_zero]
      simp only [Nat.zero_mod]
    have r_is_neg_rprime :
        r_is_negative.val = 1#u8 ↔ Field51_as_Nat r_prime % p % 2 = 1 := by
      simpa [r1_eq_rprime] using r_is_negative_post
    have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
      intro h
      exact absurd (r_is_neg_rprime.mp h) (by omega)
    have r2_eq_rprime : Field51_as_Nat r2 = Field51_as_Nat r_prime :=
      conditional_negate_eq_of_not_negative r_prime r1 r_neg r2 r_is_negative
        h_not_neg r1_eq_rprime r2_post
    refine ⟨rfl, ?_, ?_⟩
    · rw [r2_eq_rprime]
      exact rprime_zero
    · exact conditional_negate_bounds_of_eq r_prime r1 r_neg r2 r_is_negative
        r1_post r_prime_post2 r_neg_post2 r2_post
  · intro huv
    rcases huv with ⟨hu, hv, x, hxx⟩
    exfalso
    rw [← Nat.ModEq] at hxx
    have hxxv : x ^ 2 * Field51_as_Nat v ≡ Field51_as_Nat u [MOD p] := by
      simpa [Nat.ModEq, Nat.mul_mod, Nat.mod_mod] using hxx
    have eq_im := hxxv.mul rprime_v
    rw [(by ring : x ^ 2 * Field51_as_Nat v *
        (Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v) =
        (x * Field51_as_Nat v * Field51_as_Nat r_prime) ^ 2),
      (by ring : Field51_as_Nat u *
        (Field51_as_Nat SQRT_M1_val * Field51_as_Nat u) =
        Field51_as_Nat u ^ 2 *
        Field51_as_Nat SQRT_M1_val)] at eq_im
    have h_not_dvd : ¬(p ∣ Field51_as_Nat u) := by
      intro h
      exact hu (Nat.dvd_iff_mod_eq_zero.mp h)
    have h_coprime := coprime_of_prime_not_dvd prime_25519 h_not_dvd
    have fermat_u := Nat.ModEq.pow_card_sub_one_eq_one prime_25519 h_coprime
    have hp_sub : p - 1 = (p - 2) + 1 := by
      unfold p
      omega
    rw [hp_sub, pow_succ] at fermat_u
    have inv_sq := (fermat_u.pow 2).mul_right (Field51_as_Nat SQRT_M1_val)
    simp only [one_pow, one_mul] at inv_sq
    have u_eq := eq_im.mul_left ((Field51_as_Nat u ^ (p - 2)) ^ 2)
    rw [← mul_pow] at u_eq
    have : (Field51_as_Nat u ^ (p - 2)) ^ 2 *
        (Field51_as_Nat u ^ 2 *
        Field51_as_Nat SQRT_M1_val) =
        (Field51_as_Nat u ^ (p - 2) *
        Field51_as_Nat u) ^ 2 *
        Field51_as_Nat SQRT_M1_val := by
      ring
    rw [this] at u_eq
    have u_eq := u_eq.trans inv_sq
    have u_eq := u_eq.pow 2
    simp only [← pow_mul] at u_eq
    have : (Field51_as_Nat SQRT_M1_val) ^ 2 ≡ p - 1 [MOD p] := sqrt_m1_sq_modEq
    exact SQRT_M1_not_square _ (u_eq.trans this)
  · intro huv
    rcases huv with ⟨hu, hv, hno_qr⟩
    refine ⟨rfl, ?_, ?_⟩
    · simpa [Nat.mul_mod, Nat.mod_mod] using conditional_negate_sq_mul_eq_of_modeq
        r_prime r1 r_neg r2 r_is_negative
        (Field51_as_Nat v % p)
        (Field51_as_Nat SQRT_M1_val * Field51_as_Nat u)
        r1_eq_rprime
        (by simpa [r1_eq_rprime] using r_neg_post1)
        r2_post
        (by
          simpa [Nat.ModEq, Nat.mul_mod, Nat.mod_mod] using rprime_v)
    · exact conditional_negate_bounds_of_eq r_prime r1 r_neg r2 r_is_negative
        r1_post r_prime_post2 r_neg_post2 r2_post
  · exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
      r_is_negative_post r_neg_post1 r2_post

/-- Solves the square `r` branch, where the unmodified candidate already works. -/
private theorem solve_second_choice_false_choice3_true
    (r_sq_v_u : Field51_as_Nat r ^ 2 * Field51_as_Nat v ≡ Field51_as_Nat u [MOD p])
    (fe2_post1 : Field51_as_Nat fe2 ≡ Field51_as_Nat u * Field51_as_Nat v3 [MOD p])
    (r_post1 : Field51_as_Nat r ≡ Field51_as_Nat fe2 * Field51_as_Nat fe4 [MOD p])
    (r1_post : ∀ i < 5, r1[i]! = r[i]!)
    (r_post2 : ∀ i < 5, r[i]!.val < 2 ^ 52)
    (r_neg_post1 : Field51_as_Nat r1 + Field51_as_Nat r_neg ≡ 0 [MOD p])
    (r_neg_post2 : ∀ i < 5, r_neg[i]!.val ≤ 2 ^ 52)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then r_neg[i]! else r1[i]!)
    (r_is_negative_post : r_is_negative.val = 1#u8 ↔ Field51_as_Nat r1 % p % 2 = 1) :
    sqrt_ratio_i_cases u v r2 Choice.one := by
  have r1_eq_r : Field51_as_Nat r1 = Field51_as_Nat r :=
    field51_as_Nat_eq_of_post r r1 r1_post
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hu
    rw [← modEq_zero_iff] at hu
    refine ⟨(Choice.val_eq_one_iff Choice.one).mpr rfl, ?_, ?_⟩
    · have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
      simp only [zero_mul] at this
      have := Nat.ModEq.trans fe2_post1 this
      have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
      simp only [zero_mul] at this
      have r_eq0 := Nat.ModEq.trans r_post1 this
      have : Field51_as_Nat r % p % 2 = 0 := by
        simp only [Nat.ModEq] at r_eq0
        rw [r_eq0]
        simp only [Nat.zero_mod]
      have r_is_neg_r :
          r_is_negative.val = 1#u8 ↔ Field51_as_Nat r % p % 2 = 1 := by
        simpa [r1_eq_r] using r_is_negative_post
      have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
        intro h
        exact absurd (r_is_neg_r.mp h) (by omega)
      have r2_eq_r : Field51_as_Nat r2 = Field51_as_Nat r :=
        conditional_negate_eq_of_not_negative r r1 r_neg r2 r_is_negative
          h_not_neg r1_eq_r r2_post
      rw [r2_eq_r]
      exact r_eq0
    · exact conditional_negate_bounds_of_eq r r1 r_neg r2 r_is_negative
        r1_post r_post2 r_neg_post2 r2_post
  · intro huv
    rcases huv with ⟨hu, hv⟩
    exfalso
    apply hu
    rw [← modEq_zero_iff] at hv
    have h_v0 := hv.mul_left (Field51_as_Nat r ^ 2)
    simp only [mul_zero] at h_v0
    exact r_sq_v_u.symm.trans h_v0
  · intro huv
    rcases huv with ⟨hu, hv, x, hx⟩
    refine ⟨(Choice.val_eq_one_iff Choice.one).mpr rfl, ?_, ?_⟩
    · exact conditional_negate_sq_mul_eq_of_modeq
        r r1 r_neg r2 r_is_negative
        (Field51_as_Nat v % p)
        (Field51_as_Nat u)
        r1_eq_r
        (by simpa [r1_eq_r] using r_neg_post1)
        r2_post
        (by
          simpa [Nat.ModEq, Nat.mul_mod, Nat.mod_mod] using r_sq_v_u)
    · exact conditional_negate_bounds_of_eq r r1 r_neg r2 r_is_negative
        r1_post r_post2 r_neg_post2 r2_post
  · intro huv
    rcases huv with ⟨hu, hv, hno_qr⟩
    exfalso
    exact hno_qr ⟨Field51_as_Nat r, by
      simpa [Nat.ModEq, Nat.mul_mod, Nat.mod_mod] using r_sq_v_u⟩
  · exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
      r_is_negative_post r_neg_post1 r2_post

/-- Solves the nonsquare `r` branch where no matching signature is found for check. -/
private theorem solve_second_choice_false_choice3_false
    (check_eq_v : Field51_as_Nat check ≡
      Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) *
        Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) [MOD p])
    (check_eq_r_v : Field51_as_Nat check ≡
      Field51_as_Nat r ^ 2 * Field51_as_Nat v [MOD p])
    (u_m : Field51_as_Nat u ≡
      Field51_as_Nat SQRT_M1_val ^ 2 * Field51_as_Nat fe6 [MOD p])
    (v3_post1 : Field51_as_Nat v3 ≡ Field51_as_Nat fe * Field51_as_Nat v [MOD p])
    (fe2_post1 : Field51_as_Nat fe2 ≡ Field51_as_Nat u * Field51_as_Nat v3 [MOD p])
    (r_post1 : Field51_as_Nat r ≡ Field51_as_Nat fe2 * Field51_as_Nat fe4 [MOD p])
    (fe7_post1 : Field51_as_Nat fe7 ≡
      Field51_as_Nat fe6 * Field51_as_Nat SQRT_M1_val [MOD p])
    (r1_post : ∀ i < 5, r1[i]! = r[i]!)
    (r_post2 : ∀ i < 5, r[i]!.val < 2 ^ 52)
    (r_neg_post1 : Field51_as_Nat r1 + Field51_as_Nat r_neg ≡ 0 [MOD p])
    (r_neg_post2 : ∀ i < 5, r_neg[i]!.val ≤ 2 ^ 52)
    (r2_post : ∀ i < 5, r2[i]! = if r_is_negative.val = 1#u8 then r_neg[i]! else r1[i]!)
    (r_is_negative_post : r_is_negative.val = 1#u8 ↔ Field51_as_Nat r1 % p % 2 = 1)
    (h_check_ne_u : ¬(check.to_bytes = u.to_bytes))
    (h_check_ne_fe6 : ¬(check.to_bytes = fe6.to_bytes))
    (h_check_ne_fe7 : ¬(check.to_bytes = fe7.to_bytes)) :
    sqrt_ratio_i_cases u v r2 Choice.zero := by
  have r1_eq_r : Field51_as_Nat r1 = Field51_as_Nat r :=
    field51_as_Nat_eq_of_post r r1 r1_post
  rw [r1_eq_r] at r_is_negative_post r_neg_post1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hu; exfalso
    rw [← modEq_zero_iff] at hu
    let E := 2 + (2 ^ 252 - 3) * 2
    have huPow : Field51_as_Nat u ^ E ≡ 0 [MOD p] := by
      calc
        Field51_as_Nat u ^ E ≡ (0 : Nat) ^ E [MOD p] := hu.pow E
        _ = 0 := by
          have hEpos : 0 < E := by
            dsimp only [E]
            positivity
          exact zero_pow (Nat.ne_of_gt hEpos)
    have this : Field51_as_Nat check ≡ 0 [MOD p] := by
      calc
        Field51_as_Nat check ≡
            Field51_as_Nat u ^ E * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) [MOD p] :=
          check_eq_v
        _ ≡ 0 * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) [MOD p] :=
          huPow.mul_right _
        _ ≡ 0 [MOD p] := by
          rw [zero_mul]
    have hcheck0 : Field51_as_Nat check % p = 0 := (modEq_zero_iff _ _).1 this
    exact h_check_ne_u
      ((to_bytes_zero_of_Field51_as_Nat_zero hcheck0).trans
       (to_bytes_zero_of_Field51_as_Nat_zero hu).symm)
  · intro ⟨hu, hv⟩
    rw [← modEq_zero_iff] at hv
    have := hv.mul_left (Field51_as_Nat fe)
    simp only [mul_zero] at this
    have := v3_post1.trans this
    have := this.mul_left (Field51_as_Nat u)
    simp only [mul_zero] at this
    have := fe2_post1.trans this
    have := this.mul_right (Field51_as_Nat fe4)
    simp only [zero_mul] at this
    have r_zero := r_post1.trans this
    have : Field51_as_Nat r % p % 2 = 0 := by
      simp only [Nat.ModEq] at r_zero; rw [r_zero]
      simp only [Nat.zero_mod]
    have h_not_neg : ¬(r_is_negative.val = 1#u8) := by
      intro h; exact absurd (r_is_negative_post.mp h) (by omega)
    have r2_eq_r : Field51_as_Nat r2 = Field51_as_Nat r := by
      calc
        Field51_as_Nat r2 = Field51_as_Nat r1 := by
          simpa [h_not_neg] using
            field51_as_Nat_conditional_assign r1 r_neg r2 r_is_negative r2_post
        _ = Field51_as_Nat r := r1_eq_r
    have hr2_bounds : ∀ i < 5, r2[i]!.val ≤ 2 ^ 53 - 1 :=
      conditional_negate_bounds_of_eq r r1 r_neg r2 r_is_negative
        r1_post r_post2 r_neg_post2 r2_post
    refine ⟨rfl, ?_, ?_⟩
    · rw [r2_eq_r]; exact r_zero
    · exact hr2_bounds
  · intro ⟨hu, hv, xx, hxx⟩; exfalso
    simp only [Nat.mul_mod_mod] at hxx
    rw [← Nat.ModEq] at hxx
    have p_eq : 2 + (2 ^ 252 - 3) * 2 + (7 * 2 ^ 253 - 35) =
        (p - 1) * 2 + 1 := by unfold p; omega
    have p_eq1 : 2 * (2 + (2 ^ 252 - 3) * 2) =
        (p - 1) / 2 + 2 := by unfold p; omega
    have xx_check :=
      ((hxx.pow (2 + (2 ^ 252 - 3) * 2)).mul_right
        (Field51_as_Nat v ^ (7 * 2 ^ 253 - 35))).trans
      check_eq_v.symm
    rw [mul_pow, mul_assoc, ← pow_add, p_eq,
      ← pow_mul, p_eq1, pow_add] at xx_check
    have h_not_dvd_v : ¬(p ∣ Field51_as_Nat v) := by
      intro h; exact hv (Nat.dvd_iff_mod_eq_zero.mp h)
    have h_coprime_v :=
      coprime_of_prime_not_dvd prime_25519 h_not_dvd_v
    have fermat :=
      ((Nat.ModEq.pow_card_sub_one_eq_one prime_25519
        h_coprime_v).pow 2).mul_right (Field51_as_Nat v)
    simp only [← pow_mul, ← pow_succ, one_pow, one_mul] at fermat
    have fermat :=
      (fermat.mul_left
        (xx ^ ((p - 1) / 2) * xx ^ 2)).symm.trans xx_check
    by_cases hxx0 : xx ≡ 0 [MOD p]
    · have := ((hxx0.pow 2).mul_right
          (Field51_as_Nat v)).symm.trans hxx
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
      exact hu this.symm
    · have := pow_div_two_eq_neg_one_or_one hxx0
      rcases this with hl | hl
      · have := hl.mul_right (xx ^ 2 * Field51_as_Nat v)
        simp only [← mul_assoc, one_mul] at this
        have := (fermat.symm.trans this).trans hxx
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
        have := U8x32_as_Nat_injective check_eq_u
        exact h_check_ne_u (by rw [hcheck_tb, hu_tb, this])
      · have := hl.mul_right (xx ^ 2 * Field51_as_Nat v)
        simp only [← mul_assoc] at this
        have fermat := fermat.symm.trans this
        have := hxx.mul_left (p - 1)
        simp only [← mul_assoc] at this
        have fermat :=
          (fermat.trans this).trans (u_m.mul_left (p - 1))
        rw [← mul_assoc] at fermat
        have : (p - 1) * Field51_as_Nat SQRT_M1_val ^ 2 ≡
            1 [MOD p] := by
          unfold SQRT_M1_val; decide
        have := fermat.trans (this.mul_right (Field51_as_Nat fe6))
        simp only [one_mul] at this
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
        have := U8x32_as_Nat_injective check_eq_fe6
        exact h_check_ne_fe6
          (by rw [hcheck_tb, hu_tb, this])
  · intro ⟨hu, hv, hx⟩
    simp only [not_exists, Nat.mul_mod_mod] at hx
    refine ⟨rfl, ?_, ?_⟩
    · rw [mod_sq_mod_mul_eq]
      simp only [Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [← Nat.ModEq]
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
      have h_uv7_ne : ¬ Field51_as_Nat u *
          Field51_as_Nat v ^ 7 ≡ 0 [MOD p] := by
        intro h
        have := mul_zero_eq_or (hp := prime_25519) h
        rcases this with h | h
        · exact hu ((modEq_zero_iff _ _).mp h)
        · have : Field51_as_Nat v ≡ 0 [MOD p] :=
              modEq_zero_of_pow_modEq_zero h
          exact hv ((modEq_zero_iff _ _).mp this)
      have := pow_div_four_eq_four_cases h_uv7_ne
      rcases this with h | h
      · have := h.mul_right (Field51_as_Nat u)
        have := eq_check.trans this
        simp only [one_mul] at this
        exact absurd this (hx (Field51_as_Nat r))
      · rcases h with h | h
        · have := h.mul_right (Field51_as_Nat u)
          have := eq_check.trans this
          simp only at this
          have r2_eq_sq := conditional_negate_sq r1 r_neg r2 r_is_negative
            (by simpa only [r1_eq_r] using r_neg_post1) r2_post
          rw [r1_eq_r] at r2_eq_sq
          exact (r2_eq_sq.mul_right (Field51_as_Nat v)).trans this
        · rcases h with h | h
          · have := h.mul_right (Field51_as_Nat u)
            have h := eq_check.trans this
            have h := h.mul_left
              (Field51_as_Nat SQRT_M1_val ^ 2)
            simp only [← mul_assoc] at h
            have : Field51_as_Nat SQRT_M1_val ^ 2 *
                Field51_as_Nat SQRT_M1_val ^ 2 ≡
                1 [MOD p] := by
              unfold SQRT_M1_val; decide
            have := h.trans (this.mul_right (Field51_as_Nat u))
            simp only [← mul_pow, one_mul] at this
            exact absurd this
              (hx (Field51_as_Nat SQRT_M1_val *
                Field51_as_Nat r))
          · have := h.mul_right (Field51_as_Nat u)
            have h := eq_check.trans this
            have h := (check_eq_r_v.trans h).trans
              (u_m.mul_left
                (Field51_as_Nat SQRT_M1_val ^ 3))
            rw [← mul_assoc] at h
            have : Field51_as_Nat SQRT_M1_val ^ 3 *
                Field51_as_Nat SQRT_M1_val ^ 2 ≡
                Field51_as_Nat SQRT_M1_val [MOD p] := by
              unfold SQRT_M1_val; decide
            have := h.trans
              (this.mul_right (Field51_as_Nat fe6))
            rw [mul_comm] at fe7_post1
            have := this.trans fe7_post1.symm
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
            have := U8x32_as_Nat_injective check_eq_fe7
            exact False.elim (h_check_ne_fe7
              (by rw [hcheck_tb, hu_tb, this]))
    · exact conditional_negate_bounds_of_eq r r1 r_neg r2 r_is_negative
        r1_post r_post2 r_neg_post2 r2_post
  · rw [← r1_eq_r] at r_is_negative_post r_neg_post1
    exact conditional_negate_nonneg r1 r_neg r2 r_is_negative
      r_is_negative_post r_neg_post1 r2_post

end sqrt_ratio_i_branch_solvers

set_option maxHeartbeats 400000 in -- the proof works even with 230k heartbeats, but not much less.
/-- Spec for `FieldElement51::sqrt_ratio_i`: computes a nonnegative square root of u/v or
i*u/v (where i = sqrt(-1) = SQRT_M1), returning a flag indicating which case occurred.

Returns `(Choice(1), +sqrt(u/v))` if u/v is square, `(Choice(1), 0)` if u=0,
`(Choice(0), 0)` if v=0 and u≠0, `(Choice(0), +sqrt(i*u/v))` if u/v is nonsquare.

Postconditions (4 mutually exclusive cases + non-negativity):
1. u ≡ 0 → c=1, r≡0
2. u≢0, v≡0 → c=0, r≡0
3. u≢0, v≢0, ∃x, x²v≡u → c=1, r²v≡u
4. u≢0, v≢0, ¬∃x, x²v≡u → c=0, r²v≡SQRT_M1·u
5. r is non-negative (r % p % 2 = 0)
-/
theorem sqrt_ratio_i_spec'
    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val < 2 ^ 54)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val < 2 ^ 54) :
    ∃ c, sqrt_ratio_i u v = ok c ∧
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat c.2 % p
    let i_nat := Field51_as_Nat SQRT_M1_val % p
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
  simp only [step_simps]
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ← square_spec
  let* ⟨ v3, v3_post1, v3_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ← square_spec
  let* ⟨ v7, v7_post1, v7_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe4, fe4_post1, fe4_post2 ⟩ ← pow_p58_spec
  let* ⟨ r, r_post1, r_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ fe5, fe5_post1, fe5_post2 ⟩ ← square_spec
  let* ⟨ check, check_post1, check_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ i, i_post1, i_post2, i_post3 ⟩ ← constants.SQRT_M1_spec
  let* ⟨ correct_sign_sqrt, correct_sign_sqrt_post ⟩ ← Insts.SubtleConstantTimeEq.ct_eq_spec
  let* ⟨ fe6, fe6_post1, fe6_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg_spec
  let* ⟨ flipped_sign_sqrt, flipped_sign_sqrt_post ⟩ ← Insts.SubtleConstantTimeEq.ct_eq_spec
  let* ⟨ fe7, fe7_post1, fe7_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ flipped_sign_sqrt_i, flipped_sign_sqrt_i_post ⟩ ← Insts.SubtleConstantTimeEq.ct_eq_spec
  let* ⟨ r_prime, r_prime_post1, r_prime_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  -- Bridge: i = SQRT_M1_raw, fold back to SQRT_M1_val
  rw [i_post1] at r_prime_post1 fe7_post1
  rw [show constants.SQRT_M1_raw = SQRT_M1_val from rfl] at r_prime_post1 fe7_post1
  have check_eq_v :=
    check_eq_v_of_sqrt_ratio_data u v fe v3 fe1 v7 fe2 fe3 fe4 r fe5 check
      check_post1 fe5_post1 r_post1 fe4_post1 fe3_post1 fe2_post1
      v7_post1 fe1_post1 v3_post1 fe_post1
  have check_eq_mod :=
    check_eq_mod_of_sqrt_ratio_data u v fe v3 fe1 v7 fe2 fe3 fe4 r fe5 check r_prime
      r_prime_post1 check_post1 fe5_post1 r_post1 fe4_post1 fe3_post1 fe2_post1
      v7_post1 fe1_post1 v3_post1 fe_post1
  have u_m := nat_sqrt_m1_sq_of_add_modeq_zero fe6_post1
  have check_eq_r_v:= check_post1.trans (fe5_post1.mul_left (Field51_as_Nat v))
  rw[mul_comm] at check_eq_r_v
  by_cases first_choice :  flipped_sign_sqrt.val = 1#u8
  · simp only [show flipped_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt_i.val = 1#u8 from
        Or.inl first_choice, show correct_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt.val = 1#u8 from
        Or.inr first_choice, if_true, bind_tc_ok]
    let* ⟨ r1, r1_post ⟩ ← Insts.SubtleConditionallySelectable.conditional_assign_spec
    let* ⟨ r_is_negative, r_is_negative_post ⟩ ← is_negative_spec
    let* ⟨ r_neg, r_neg_post1, r_neg_post2 ⟩ ←
      Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg_spec
    · intro i hi
      simp only [Choice.one, ↓reduceIte] at r1_post
      rw [r1_post i hi]
      have := r_prime_post2 i hi
      omega
    let* ⟨ r2, r2_post ⟩ ← Insts.SubtleConditionallySelectable.conditional_assign_spec
    · simp only [Choice.one, ↓reduceIte] at r1_post
      have h_bytes_fe6 : check.to_bytes = fe6.to_bytes :=
        flipped_sign_sqrt_post.mp ((Choice.val_eq_one_iff _).mp first_choice)
      have check_fe6 := eq_to_bytes_eq_Field51_as_Nat h_bytes_fe6
      rw [← Nat.ModEq] at check_fe6
      have r_prime_sq_v_u : Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v ≡
          Field51_as_Nat u [MOD p] :=
        (check_eq_mod.trans (check_fe6.mul_left _)).trans u_m.symm
      exact solve_first_choice_true
          check_fe6 r_prime_sq_v_u check_post1 fe6_post1 fe2_post1 r_post1
          r_prime_post1 r1_post r_prime_post2 r_neg_post1 r_neg_post2
          r2_post r_is_negative_post
  · -- second branch: first_choice = false
    by_cases second_choice : flipped_sign_sqrt_i.val = 1#u8
    · -- A: second_choice = true (c = Choice.one, r1 = r_prime)
      simp only [first_choice, false_or, or_false, if_pos second_choice, bind_tc_ok]
      let* ⟨ r1, r1_post ⟩ ← Insts.SubtleConditionallySelectable.conditional_assign_spec
      let* ⟨ r_is_negative, r_is_negative_post ⟩ ← is_negative_spec
      let* ⟨ r_neg, r_neg_post1, r_neg_post2 ⟩ ←
        Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg_spec
      · intro i hi
        simp only [Choice.one, ↓reduceIte] at r1_post
        rw [r1_post i hi]
        have := r_prime_post2 i hi
        omega
      let* ⟨ r2, r2_post ⟩ ← Insts.SubtleConditionallySelectable.conditional_assign_spec
      · -- main block A: by_cases on correct_sign_sqrt
        by_cases choice3 : correct_sign_sqrt.val = 1#u8
        · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
          -- A1: second_choice=true, choice3=true
          have h_check_u := correct_sign_sqrt_post.mp
            ((Choice.val_eq_one_iff _).mp choice3)
          have check_eq_u := eq_to_bytes_eq_Field51_as_Nat h_check_u
          rw [← Nat.ModEq] at check_eq_u
          have h_check_fe7 := flipped_sign_sqrt_i_post.mp
            ((Choice.val_eq_one_iff _).mp second_choice)
          have check_eq_fe7 := eq_to_bytes_eq_Field51_as_Nat h_check_fe7
          rw [← Nat.ModEq] at check_eq_fe7
          have check_eq_fe6_m := check_eq_fe7.trans fe7_post1
          have check_1 := check_eq_fe6_m.mul_left (Field51_as_Nat SQRT_M1_val)
          have : Field51_as_Nat SQRT_M1_val *
              (Field51_as_Nat fe6 * Field51_as_Nat SQRT_M1_val) =
              Field51_as_Nat SQRT_M1_val ^ 2 * Field51_as_Nat fe6 := by ring
          rw [this] at check_1
          have sqrt_m1_u :=
            (check_eq_u.mul_left (Field51_as_Nat SQRT_M1_val)).symm.trans
              (check_1.trans u_m.symm)
          simp only [Choice.one, ↓reduceIte] at r1_post
          exact solve_second_choice_true_choice3_true
              sqrt_m1_u fe2_post1 r_post1 r_prime_post1 r1_post
              r_prime_post2 r_neg_post2 r2_post r_is_negative_post
        · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
          -- A2: second_choice=true, choice3=false
          have h_check_fe7 := flipped_sign_sqrt_i_post.mp
            ((Choice.val_eq_one_iff _).mp second_choice)
          have check_eq_fe7 := eq_to_bytes_eq_Field51_as_Nat h_check_fe7
          rw [← Nat.ModEq] at check_eq_fe7
          have check_eq_fe6_m := check_eq_fe7.trans fe7_post1
          have u_eq1 := check_eq_fe6_m.mul_left (Field51_as_Nat SQRT_M1_val)
          have : Field51_as_Nat SQRT_M1_val *
              (Field51_as_Nat fe6 * Field51_as_Nat SQRT_M1_val) =
              Field51_as_Nat SQRT_M1_val ^ 2 * Field51_as_Nat fe6 := by ring
          rw [this] at u_eq1
          have u_eq1 := u_eq1.trans u_m.symm
          have mul_u_eq1 := u_eq1.mul_left (Field51_as_Nat SQRT_M1_val)
          have : Field51_as_Nat SQRT_M1_val *
              (Field51_as_Nat SQRT_M1_val * Field51_as_Nat check) =
              Field51_as_Nat SQRT_M1_val ^ 2 * Field51_as_Nat check := by ring
          rw [this] at mul_u_eq1
          have rprime_v := check_eq_mod.trans mul_u_eq1
          have h_check_ne_u : ¬(check.to_bytes = u.to_bytes) :=
            fun h => choice3 (by rw [correct_sign_sqrt_post.mpr h]; rfl)
          simp only [Choice.one, ↓reduceIte] at r1_post
          exact solve_second_choice_true_choice3_false
              u_eq1 rprime_v h_check_ne_u v3_post1 fe2_post1 r_post1
              r_prime_post1 r1_post r_prime_post2 r_neg_post1 r_neg_post2
              r2_post r_is_negative_post
    · -- B: second_choice = false (c = Choice.zero, r1 = r)
      simp only [if_neg second_choice, first_choice, false_or, or_false, bind_tc_ok]
      let* ⟨ r1, r1_post ⟩ ← Insts.SubtleConditionallySelectable.conditional_assign_spec
      let* ⟨ r_is_negative, r_is_negative_post ⟩ ← is_negative_spec
      let* ⟨ r_neg, r_neg_post1, r_neg_post2 ⟩ ←
        Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51.neg_spec
      · intro i hi
        have h01 : ¬(0#u8 = 1#u8) := by decide
        simp only [Choice.zero, h01, ite_false] at r1_post
        rw [r1_post i hi]
        have := r_post2 i hi
        omega
      let* ⟨ r2, r2_post ⟩ ← Insts.SubtleConditionallySelectable.conditional_assign_spec
      · -- main block B: by_cases on correct_sign_sqrt
        by_cases choice3 : correct_sign_sqrt.val = 1#u8
        · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
          -- B1: second_choice=false, choice3=true
          have h_check_u := correct_sign_sqrt_post.mp
            ((Choice.val_eq_one_iff _).mp choice3)
          have check_eq_u := eq_to_bytes_eq_Field51_as_Nat h_check_u
          rw [← Nat.ModEq] at check_eq_u
          have r_sq_v_u := check_eq_r_v.symm.trans check_eq_u
          have h01 : ¬(0#u8 = 1#u8) := by decide
          simp only [Choice.zero, h01, ite_false] at r1_post
          exact solve_second_choice_false_choice3_true
              r_sq_v_u fe2_post1 r_post1 r1_post r_post2 r_neg_post1
              r_neg_post2 r2_post r_is_negative_post
        · simp only [choice3, ↓reduceIte, bind_tc_ok, Aeneas.Std.WP.spec_ok]
          -- B2: second_choice=false, choice3=false
          have h01 : ¬(0#u8 = 1#u8) := by decide
          simp only [Choice.zero, h01, ite_false] at r1_post
          have h_check_ne_u : ¬(check.to_bytes = u.to_bytes) :=
            fun h => choice3 (by rw [correct_sign_sqrt_post.mpr h]; rfl)
          have h_check_ne_fe6 : ¬(check.to_bytes = fe6.to_bytes) :=
            fun h => first_choice (by rw [flipped_sign_sqrt_post.mpr h]; rfl)
          have h_check_ne_fe7 : ¬(check.to_bytes = fe7.to_bytes) :=
            fun h => second_choice (by rw [flipped_sign_sqrt_i_post.mpr h]; rfl)
          exact solve_second_choice_false_choice3_false
              check_eq_v check_eq_r_v u_m v3_post1 fe2_post1 r_post1
              fe7_post1 r1_post r_post2 r_neg_post1 r_neg_post2
              r2_post r_is_negative_post
              h_check_ne_u h_check_ne_fe6 h_check_ne_fe7


@[step]
theorem sqrt_ratio_i_spec
    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val < 2 ^ 54)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val < 2 ^ 54) :
    sqrt_ratio_i u v ⦃ c =>
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat c.2 % p
    let i_nat := Field51_as_Nat SQRT_M1_val % p
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
