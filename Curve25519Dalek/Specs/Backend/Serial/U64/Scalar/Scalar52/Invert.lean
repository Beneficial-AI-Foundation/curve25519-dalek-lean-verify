/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.AsMontgomery
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryInvert
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromMontgomery
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Zero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR
/-! # Spec Theorem for `Scalar52::invert`

Specification and proof for `Scalar52::invert`.

This function computes the multiplicative inverse.

**Source**: curve25519-dalek/src/scalar.rs

-/

open Aeneas.Std Result curve25519_dalek.backend.serial.u64.scalar curve25519_dalek.backend.serial.u64.scalar.Scalar52
namespace curve25519_dalek.scalar.Scalar52

set_option linter.style.commandStart false
set_option exponentiation.threshold 260

<<<<<<< HEAD

=======
>>>>>>> upstream/master
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

theorem cancelR {a b : ℕ} (h : a * R ≡ b * R [MOD L]) : a ≡ b [MOD L] := by
  -- prove that R and L are coprime
  have hcoprime : Nat.Coprime R L := by
    unfold R L Nat.Coprime
    simp
  have h1 := Nat.Coprime.symm hcoprime

  -- use the standard lemma for cancelling a factor modulo L
  exact Nat.ModEq.cancel_right_of_coprime h1 h

theorem as_montgomery_ne_zero (u : Scalar52) (h : u ≠ ZERO) :
    ∃ m, as_montgomery u = ok m ∧
    Scalar52_as_Nat m ≡ (Scalar52_as_Nat u * R) [MOD L] ∧ m ≠ ZERO := by
  sorry

@[progress]
theorem invert_spec (u : Scalar52) (h : u ≠ ZERO) :
    ∃ u',
    invert u = ok u' ∧
    (Scalar52_as_Nat u * Scalar52_as_Nat u') ≡ 1 [MOD L]
    := by
  unfold invert
  obtain ⟨s, hs_ok,hs_val,ne_zero⟩ := as_montgomery_ne_zero   u h
  simp only [hs_ok, bind_tc_ok]
  obtain ⟨r, hr_ok,hr_val⟩ := montgomery_invert_spec s ne_zero
  simp only [hr_ok, bind_tc_ok]
  obtain ⟨s1, hs1_ok,hs1_val⟩ := from_montgomery_spec r
  simp only [hs1_ok]
  use s1
  simp
  rw[← Nat.ModEq] at hr_val
  rw[← Nat.ModEq] at hs1_val
  have hrm:= Nat.ModEq.mul_left (Scalar52_as_Nat s) hs1_val
  have ur:= Nat.ModEq.trans hrm hr_val
  have hrm1:= Nat.ModEq.mul_right (Scalar52_as_Nat s1 * R) hs_val
  have hmr1:= Nat.ModEq.symm hrm1
  have ur1  := Nat.ModEq.trans hmr1 ur
  have eq:  Scalar52_as_Nat u * R * (Scalar52_as_Nat s1 * R)  = (Scalar52_as_Nat u * Scalar52_as_Nat s1) * (R * R):= by ring
  rw[eq] at ur1
  apply  cancelRR
  simp
  have : R * R = R^2:= by ring
  rw[this] at ur1
  exact ur1

end curve25519_dalek.scalar.Scalar52
