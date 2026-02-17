/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SQRT_M1

/-! # Spec Theorem for `FieldElement51::invsqrt`

Specification and proof for `FieldElement51::invsqrt`.

This function inputs (1, v) for a field element v into sqrt_ratio_i.
It computes

- the nonnegative square root of 1/v              when v is a nonzero square,
- returns zero                                    when v is zero, and
- returns the nonnegative square root of i/v      when v is a nonzero nonsquare.

Here i = sqrt(-1) = SQRT_M1 constant

Source: curve25519-dalek/src/field.rs
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.constants
namespace curve25519_dalek.field.FieldElement51

/-
Natural language description:

    This function takes a field element v and returns

    - (Choice(1), +sqrt(1/v))    if v is a nonzero square;
    - (Choice(0), zero)          if v is zero;
    - (Choice(0), +sqrt(i/v))    if v is a nonzero nonsquare.

Here i represents a square root of -1 in the field (mod p) and is stored as the constant SQRT_M1.
Every returned square root is nonnegative.

Natural language specs:

    • The function succeeds (no panic) for all field element inputs

    • The result (c, r) satisfies three mutually exclusive cases:

      - If v = 0 (mod p), then (c, r) = (Choice(0), 0)

      - If v ≠ 0 (mod p) and v is a square, then (c, r) = (Choice(1), sqrt(1/v))

      - If v ≠ 0 (mod p) and v is not a square, then (c, r) = (Choice(0), sqrt(i/v))

    • In all cases, r is non-negative
-/

/-- **Auxiliary technical lemma: v is square iff 1/v is square**:
For nonzero v in the field mod p, v is a square iff 1/v is a square.
In modular arithmetic: (∃ x, x² ≡ v) ↔ (∃ y, y² * v ≡ 1)
-/
lemma square_iff_inv_square (v_nat : Nat) (hv : v_nat % p ≠ 0) :
    (∃ x : Nat, x^2 % p = v_nat % p) ↔ (∃ y : Nat, (y^2 * v_nat) % p = 1) := by
  let v : ZMod p := v_nat
  have hvZ : v ≠ 0 := by
    intro h0
    have hp_dvd : p ∣ v_nat := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h0
    have : v_nat % p = 0 := Nat.mod_eq_zero_of_dvd hp_dvd
    exact hv this
  have lhs_iff : (∃ x : Nat, x^2 % p = v_nat % p) ↔ IsSquare v := by
    constructor
    · intro ⟨x, hx⟩
      use (x : ZMod p)
      have h_cast : (Nat.cast (x^2) : ZMod p) = (Nat.cast v_nat : ZMod p) := by
        rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]
        exact hx
      calc v = (v_nat : ZMod p) := rfl
        _ = Nat.cast (x^2) := h_cast.symm
        _ = (x : ZMod p)^2 := by simp only [Nat.cast_pow]
        _ = (x : ZMod p) * (x : ZMod p) := sq (x : ZMod p)
    · intro ⟨xZ, hxZ⟩
      use xZ.val
      have h1 : (xZ.val : ZMod p) = xZ := ZMod.natCast_zmod_val xZ
      have h2 : (xZ.val : ZMod p)^2 = xZ^2 := by
        rw [h1]
      have h3 : xZ^2 = v := by
        rw [sq]
        exact hxZ.symm
      have h4 : (xZ.val : ZMod p)^2 = (v_nat : ZMod p) := by
        rw [h2, h3]
      have h5 : Nat.cast (xZ.val^2) = (Nat.cast v_nat : ZMod p) := by
        rw [Nat.cast_pow, h4]
      have h6 : xZ.val^2 ≡ v_nat [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        exact h5
      rw [Nat.ModEq] at h6
      exact h6
  have rhs_iff : (∃ y : Nat, (y^2 * v_nat) % p = 1) ↔ IsSquare v⁻¹ := by
    constructor
    · intro ⟨y, hy⟩
      use (y : ZMod p)
      have h : (y : ZMod p)^2 * v = 1 := by
        have : (y^2 * v_nat) ≡ 1 [MOD p] := by
          rw [Nat.ModEq, hy]; simp [Nat.mod_eq_of_lt (by decide : 1 < p)]
        rw [← ZMod.natCast_eq_natCast_iff] at this
        calc (y : ZMod p)^2 * v
            = (y : ZMod p)^2 * (v_nat : ZMod p) := rfl
          _ = (Nat.cast (y^2) : ZMod p) * (Nat.cast v_nat : ZMod p) := by simp
          _ = Nat.cast (y^2 * v_nat) := by rw [← Nat.cast_mul]
          _ = 1 := by simpa using this
      rw [← sq]
      calc v⁻¹ = 1 * v⁻¹ := (one_mul _).symm
        _ = (y : ZMod p)^2 * v * v⁻¹ := by rw [← h]
        _ = (y : ZMod p)^2 * (v * v⁻¹) := by rw [mul_assoc]
        _ = (y : ZMod p)^2 * 1 := by rw [mul_inv_cancel₀ hvZ]
        _ = (y : ZMod p)^2 := mul_one _
    · intro ⟨yZ, hyZ⟩
      use yZ.val
      have h1 : yZ^2 * v = 1 := by
        calc yZ^2 * v
            = (yZ * yZ) * v   := by rw [sq]
          _ = v⁻¹ * v         := by rw [hyZ]
          _ = 1               := inv_mul_cancel₀ hvZ
      have h_val : (yZ.val : ZMod p) = yZ := ZMod.natCast_zmod_val yZ
      have h2 : Nat.cast (yZ.val^2 * v_nat) = (1 : ZMod p) := by
        calc Nat.cast (yZ.val^2 * v_nat)
            = (Nat.cast (yZ.val^2) : ZMod p) * (Nat.cast v_nat : ZMod p) := by rw [Nat.cast_mul]
          _ = (yZ.val : ZMod p)^2 * v         := by rw [Nat.cast_pow]
          _ = yZ^2 * v                         := by rw [h_val]
          _ = 1                                := h1
      have h3 : (yZ.val^2 * v_nat) ≡ 1 [MOD p] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        exact h2
      rw [Nat.ModEq] at h3
      simpa using h3
  have sqInv : IsSquare v⁻¹ ↔ IsSquare v := by
    constructor <;> (intro ⟨r, hr⟩; use r⁻¹; rw [← mul_inv, ← hr])
    · rw [inv_inv]
  calc (∃ x : Nat, x^2 % p = v_nat % p)
      ↔ IsSquare v              := lhs_iff
    _ ↔ IsSquare v⁻¹            := sqInv.symm
    _ ↔ (∃ y : Nat, (y^2 * v_nat) % p = 1) := rhs_iff.symm

/-- **Spec and proof concerning `field.FieldElement51.invsqrt`**:
- No panic for field element inputs v (always returns (c, r) successfully)
- The result satisfies exactly one of three mutually exclusive cases:
  1. If v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
  2. If v ≢ 0 (mod p) and ∃ x, x^2 ≡ v (mod p), then c.val = 1 and r^2 * v ≡ 1 (mod p)
  3. If v ≢ 0 (mod p) and ¬∃ x, x^2 ≡ v (mod p), then c.val = 0 and r^2 * v ≡ SQRT_M1 (mod p)
-/
@[progress]
theorem invsqrt_spec
    (v : backend.serial.u64.field.FieldElement51)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 52 - 1) :
    ∃ res, invsqrt v = ok res ∧
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat res.snd % p
    let i_nat := Field51_as_Nat SQRT_M1 % p
    -- Case 1: If v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
    (v_nat = 0 → res.fst.val = 0#u8 ∧ r_nat = 0) ∧
    -- Case 2: If v ≢ 0 (mod p) and ∃ x, x^2 ≡ v (mod p), then c.val = 1 and r^2 * v ≡ 1 (mod p)
    (v_nat ≠ 0 ∧ (∃ x : Nat, x^2 % p = v_nat) → res.fst.val = 1#u8 ∧ (r_nat^2 * v_nat) % p = 1) ∧
    -- Case 3: If v ≢ 0 (mod p) and ¬∃ x, x^2 ≡ v (mod p), then c.val = 0 and r^2 * v ≡ SQRT_M1 (mod p)
    (v_nat ≠ 0 ∧ ¬(∃ x : Nat, x^2 % p = v_nat) →
      res.fst.val = 0#u8 ∧ (r_nat^2 * v_nat) % p = i_nat) := by
  unfold invsqrt
  progress*
  · -- BEGIN TASK
    intro i _
    unfold ONE
    interval_cases i; all_goals decide
    --- END TASK
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
    · -- BEGIN TASK
      rename_i res_1
      have := res_1 ?_
      · constructor
        · simp[this]
        · simp[this]
      · simp_all[ONE]
        decide
      --- END TASK
    · -- BEGIN TASK
      have := res ?_
      · simp_all [ONE]; decide
      · refine ⟨?_, ?_, ?_⟩
        · simp [ONE_spec, show ¬p = 1 by decide]
        · grind
        · have v_nonzero : Field51_as_Nat v % p ≠ 0 := h.1
          rw [ONE_spec]
          obtain ⟨y, hy⟩ := (square_iff_inv_square (Field51_as_Nat v) v_nonzero).mp h.2
          use y
          have : (y ^ 2 * (Field51_as_Nat v % p)) % p = (y ^ 2 * Field51_as_Nat v) % p := by
            rw [Nat.mul_mod, Nat.mul_mod]
            simp only [Nat.mod_mod]
            rw [← Nat.mul_mod]
          rw [this]
          exact hy
      --- END TASK
    · -- BEGIN TASK
      have := res_post ?_
      · simp_all [ONE_spec]
      · refine ⟨?_, ?_, ?_⟩
        · simp [ONE_spec, show ¬p = 1 by decide]
        · exact h.1
        · intro hx
          obtain ⟨x, hx⟩ := hx
          rw [ONE_spec, ne_eq, not_exists] at *
          obtain ⟨z, hz⟩ : ∃ z : Nat, z^2 % p = Field51_as_Nat v % p := by
            rw [square_iff_inv_square (Field51_as_Nat v) h.1]
            use x
            calc x ^ 2 * Field51_as_Nat v % p
              = x ^ 2 * (Field51_as_Nat v % p) % p := by simp [Nat.mul_mod]
            _ = 1 % p := hx
          exact h.2 z hz
      --- END TASK

end curve25519_dalek.field.FieldElement51
