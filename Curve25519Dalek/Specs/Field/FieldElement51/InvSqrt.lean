/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SqrtM1

/-!
# Spec theorem for `curve25519_dalek::field::FieldElement51::invsqrt`

This function takes a field element `v` and returns its (nonnegative) inverse square root
by feeding `(1, v)` into `sqrt_ratio_i`. Concretely it returns:

- `(Choice(1), +sqrt(1/v))` if `v` is a nonzero square;
- `(Choice(0), 0)`          if `v` is zero;
- `(Choice(0), +sqrt(i/v))` if `v` is a nonzero nonsquare.

Here `i` represents a square root of `-1` in the field (mod `p`) and is stored as the
constant `SQRT_M1`. Every returned square root is nonnegative.

Source: "curve25519-dalek/src/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.constants
namespace curve25519_dalek.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::field::FieldElement51::invsqrt`**
• The function succeeds (no panic) for field element inputs `v` with limbs bounded by `2^52 - 1`
• Output limbs are bounded by `2^53 - 1`
• The result `r` is non-negative (`r_nat % 2 = 0`)
• If `v ≡ 0 (mod p)`, then `c.val = 0` and `r ≡ 0 (mod p)`
• If `v ≢ 0 (mod p)` and `v` is a square, then `c.val = 1` and `r^2 * v ≡ 1 (mod p)`
• If `v ≢ 0 (mod p)` and `v` is not a square, then `c.val = 0` and `r^2 * v ≡ i (mod p)`
-/
@[step]
theorem invsqrt_spec
    (v : backend.serial.u64.field.FieldElement51)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 52 - 1) :
    invsqrt v ⦃ (result : subtle.Choice × backend.serial.u64.field.FieldElement51) =>
      let v_nat := Field51_as_Nat v % p
      let r_nat := Field51_as_Nat result.snd % p
      let i_nat := Field51_as_Nat SQRT_M1_val % p
      -- Output limb bounds
      (∀ i < 5, result.snd[i]!.val ≤ 2 ^ 53 - 1) ∧
      -- Non-negativity
      (r_nat % 2 = 0) ∧
      -- Case 1: If v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
      (v_nat = 0 → result.fst.val = 0#u8 ∧ r_nat = 0) ∧
      -- Case 2: If v ≢ 0 and ∃ x, x^2 * v ≡ 1 (mod p), then c.val = 1 and r^2 * v ≡ 1 (mod p)
      (v_nat ≠ 0 ∧ (∃ x : Nat, (x ^ 2 * v_nat) % p = 1) →
        result.fst.val = 1#u8 ∧ (r_nat ^ 2 * v_nat) % p = 1) ∧
      -- Case 3: If v ≢ 0 and ¬∃ x, x^2 * v ≡ 1 (mod p), then c.val = 0 and r^2 * v ≡ i (mod p)
      (v_nat ≠ 0 ∧ ¬(∃ x : Nat, (x ^ 2 * v_nat) % p = 1) →
        result.fst.val = 0#u8 ∧ (r_nat ^ 2 * v_nat) % p = i_nat) ⦄ := by
  unfold invsqrt ONE from_limbs
  simp only [bind_tc_ok]
  step as ⟨c, h_bounds, h_nonneg, h_case1, h_case2, h_case3, h_case4⟩
  · intro i _; interval_cases i; all_goals decide
  -- Rewrite Field51_as_Nat of literal ONE to 1 in all case hypotheses
  have h_one : Field51_as_Nat (Array.make 5#usize [1#u64, 0#u64, 0#u64, 0#u64, 0#u64]) % p = 1 :=
    by decide
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
