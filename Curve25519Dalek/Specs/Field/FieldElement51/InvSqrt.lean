/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
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
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 52 - 1)
    (pow : Field51_as_Nat v * Field51_as_Nat v ≡ Field51_as_Nat ONE [MOD p]) :
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
        · obtain ⟨x, hx⟩ := h.2
          use x
          rw [Nat.ModEq, ONE_spec] at pow
          rw [ONE_spec, Nat.mul_mod, Nat.mul_mod]
          simpa [hx, Nat.mod_mul, ← Nat.mul_mod]
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
          apply h.2 x
          have eq1 := Nat.ModEq.mul_right (Field51_as_Nat v % p) hx
          have eq2 := Nat.ModEq.mul_left (x ^2) pow
          rw [mul_one] at eq2
          have v_mod : Field51_as_Nat v % p ≡ Field51_as_Nat v [MOD p] := by simp [Nat.ModEq]
          have key := Nat.ModEq.mul_left (x ^2) (Nat.ModEq.mul v_mod v_mod)
          have : x ^ 2 * (Field51_as_Nat v % p) * (Field51_as_Nat v % p) =
            x ^ 2 * ((Field51_as_Nat v % p) * (Field51_as_Nat v % p)) := by ring
          rw [this] at eq1
          have step : 1 % p * (Field51_as_Nat v % p) ≡ Field51_as_Nat v % p [MOD p] := by
            simp [Nat.ModEq]
          refine Nat.ModEq.trans ?_ v_mod
          refine Nat.ModEq.trans ?_ step
          refine Nat.ModEq.trans ?_ eq1
          exact (Nat.ModEq.symm (Nat.ModEq.trans key eq2))
      --- END TASK

end curve25519_dalek.field.FieldElement51
