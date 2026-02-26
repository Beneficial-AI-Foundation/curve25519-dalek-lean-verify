/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
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

open Aeneas Aeneas.Std Aeneas.Std.WP Result
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
- Output limbs bounded by 2^53 - 1
- Result r is non-negative (r_nat % 2 = 0)
- The result satisfies exactly one of three mutually exclusive cases:
  1. If v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
  2. If v ≢ 0 and ∃ x, x^2 * v ≡ 1 (mod p), then c.val = 1 and r^2 * v ≡ 1 (mod p)
  3. If v ≢ 0 and ¬∃ x, x^2 * v ≡ 1 (mod p), then c.val = 0 and r^2 * v ≡ SQRT_M1 (mod p)
-/
@[progress]
theorem invsqrt_spec
    (v : backend.serial.u64.field.FieldElement51)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 52 - 1) :
    invsqrt v ⦃ res =>
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat res.snd % p
    let i_nat := Field51_as_Nat SQRT_M1 % p
    -- Unconditional bounds
    (∀ i < 5, res.snd[i]!.val ≤ 2 ^ 53 - 1) ∧
    -- Non-negativity
    (r_nat % 2 = 0) ∧
    -- Case 1: If v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
    (v_nat = 0 → res.fst.val = 0#u8 ∧ r_nat = 0) ∧
    -- Case 2: If v ≢ 0 and ∃ x, x^2 * v ≡ 1 (mod p), then c.val = 1 and r^2 * v ≡ 1 (mod p)
    (v_nat ≠ 0 ∧ (∃ x : Nat, (x ^ 2 * v_nat) % p = 1) →
      res.fst.val = 1#u8 ∧ (r_nat ^ 2 * v_nat) % p = 1) ∧
    -- Case 3: If v ≢ 0 and ¬∃ x, x^2 * v ≡ 1 (mod p), then c.val = 0 and r^2 * v ≡ i (mod p)
    (v_nat ≠ 0 ∧ ¬(∃ x : Nat, (x ^ 2 * v_nat) % p = 1) →
      res.fst.val = 0#u8 ∧ (r_nat ^ 2 * v_nat) % p = i_nat) ⦄ := by
  unfold invsqrt
  progress as ⟨c, h_bounds, h_nonneg, h_case1, h_case2, h_case3, h_case4⟩
  · intro i _; unfold ONE; interval_cases i; all_goals decide
  · -- Rewrite Field51_as_Nat ONE % p to 1 in all case hypotheses
    have h_one : Field51_as_Nat ONE % p = 1 := by simp [ONE_spec]; decide
    simp only [h_one] at h_case1 h_case2 h_case3 h_case4
    refine ⟨h_bounds, h_nonneg, ?_, ?_, ?_⟩
    · -- Case 1: v = 0 → Choice(0) ∧ r = 0
      intro hv
      exact h_case2 ⟨by decide, hv⟩
    · -- Case 2: v ≠ 0, 1/v is a square → Choice(1) ∧ r^2 * v ≡ 1
      intro ⟨hv, hx⟩
      exact h_case3 ⟨by decide, hv, hx⟩
    · -- Case 3: v ≠ 0, 1/v is not a square → Choice(0) ∧ r^2 * v ≡ i
      intro ⟨hv, hx⟩
      have h := h_case4 ⟨by decide, hv, hx⟩
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [mul_one, Nat.mod_mod_of_dvd _ (dvd_refl p)] at h2
      exact h2

end curve25519_dalek.field.FieldElement51
