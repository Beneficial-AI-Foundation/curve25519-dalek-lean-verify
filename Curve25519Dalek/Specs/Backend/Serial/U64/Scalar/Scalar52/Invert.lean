/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryInvert
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromMontgomery
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Zero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR
/-! # Spec Theorem for `Scalar52::invert`

Specification and proof for `Scalar52::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.scalar curve25519_dalek.backend.serial.u64.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar52

set_option exponentiation.threshold 260

/-
natural language description:

    • Takes as input an UnpackedScalar u and returns another UnpackedScalar u’ that
      represents the multiplicative inverse of u within the underlying
      field \mathbb{Z} / \ell \mathbb{Z}. This is done by first
      converting u into Montgomery form, then inverting with
      montgomery_invert, and then converting back into UnpackedScalar.

natural language specs:

    • \forall UnpackedScalars u with u ≠ 0:
      scalar_to_nat(u) * scalar_to_nat(u') is congruent to 1 (mod \ell)
-/

/-- **Spec and proof concerning `scalar.Scalar52.invert`**:
- Precondition: The unpacked input scalar u must be non-zero (inverting zero has undefined behavior)
- No panic (returns successfully for non-zero input)
- The result u' satisfies the multiplicative inverse property:
  Scalar52_as_Nat(u) * Scalar52_as_Nat(u') ≡ 1 (mod L)
-/





lemma coprime_pow_left {a b : ℕ} :
    ∀ n, Nat.Coprime a b → Nat.Coprime (a ^ n) b
  | 0, _ => by simp
  | n + 1, h => by
    simp [pow_succ]
    exact Nat.Coprime.mul_left (coprime_pow_left n h) h


theorem coprimeRL : Nat.Coprime R L:= by
  unfold R L Nat.Coprime
  simp

theorem cancelRR {a b : ℕ}
    (h : a * R ^ 2 ≡ b * R ^ 2 [MOD L])
    :a ≡ b [MOD L] := by
  have hcoprime : Nat.Coprime R L := by
    unfold R L Nat.Coprime
    simp
  have h1 : Nat.Coprime (R ^ 2) L := coprime_pow_left 2 hcoprime
  have h1' := Nat.Coprime.symm h1
  -- rewrite both sides so the common factor is on the left
  have h' : R ^ 2 * a ≡ R ^ 2 * b [MOD L] := by simpa [Nat.mul_comm] using h
  exact Nat.ModEq.cancel_left_of_coprime h1' h'




theorem ZERO_mod (u : Scalar52) (h : Scalar52_as_Nat u  ≡ 0 [MOD L]) : u = ZERO := by
  sorry







@[progress]
theorem invert_spec (u : Scalar52) (h : u ≠ ZERO) :
    ∃ u',
    invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') ≡ 1 [MOD L]
    := by
  unfold invert backend.serial.u64.scalar.Scalar52.as_montgomery
  obtain ⟨s, hs_ok,hs_val⟩ := montgomery_mul_spec u backend.serial.u64.constants.RR
  simp only [hs_ok, bind_tc_ok]
  have n_zero: s ≠ ZERO :=by
    intro hz
    rw[hz,backend.serial.u64.scalar.Scalar52.ZERO_spec] at hs_val
    apply h
    have hr:=backend.serial.u64.RR_spec
    rw[← Nat.ModEq] at hr
    have hrm:= Nat.ModEq.mul_left (Scalar52_as_Nat u) hr
    have hmr:= Nat.ModEq.symm hrm
    have ur:= Nat.ModEq.trans hmr hs_val
    set su:=Scalar52_as_Nat u with hu
    have ca:=@cancelRR su 0
    simp at ca
    simp at ur
    have ca:= ca ur
    rw[hu] at ca
    apply ZERO_mod
    exact ca

  obtain ⟨r, hr_ok,hr_val⟩ := montgomery_invert_spec s n_zero
  simp only [hr_ok, bind_tc_ok]
  obtain ⟨s1, hs1_ok,hs1_val⟩ := from_montgomery_spec r
  simp only [hs1_ok]
  use s1
  simp
  rw[← Nat.ModEq] at hr_val
  rw[← Nat.ModEq] at hs1_val
  have hrm:= Nat.ModEq.mul_left (Scalar52_as_Nat s) hs1_val
  have ur:= Nat.ModEq.trans hrm hr_val
  have hr:=backend.serial.u64.RR_spec
  rw[← Nat.ModEq] at hr
  have eq: Scalar52_as_Nat s * ((Scalar52_as_Nat s1) * R)
  = (Scalar52_as_Nat s * R) * Scalar52_as_Nat s1:= by
   ring
  rw[eq] at ur
  have hrm1:= Nat.ModEq.mul_right (Scalar52_as_Nat s1) hs_val
  have ur1:= Nat.ModEq.trans hrm1 ur
  set su:=Scalar52_as_Nat u with hu
  set ss1:=Scalar52_as_Nat s1 with hs1
  set R2:=Scalar52_as_Nat backend.serial.u64.constants.RR with hss


  have eq1: su * R2 * ss1  =  (su* ss1)*R2  := by
   ring
  rw[eq1] at ur1
  have hsu1:= Nat.ModEq.mul_left (su * ss1) hr
  have hus1:= Nat.ModEq.symm hsu1
  have husr:= Nat.ModEq.trans hus1 ur1
  apply  cancelRR
  simp
  have : R * R = R^2:= by ring
  rw[this] at husr
  exact husr



















end curve25519_dalek.scalar.Scalar52
