/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi

/-! # Spec Theorem for `FieldElement51::invsqrt`

Specification and proof for `FieldElement51::invsqrt`.

This function inputs (1, v) for a field element v into sqrt_ratio_i.
It computes

- the nonnegative square root of 1/v              when v is a nonzero square,
- returns zero                                    when v is zero, and
- returns the nonnegative square root of i/v      when v is a nonzero nonsquare.

Here i = sqrt(-1) = SQRT_M1 constant

**Source**: curve25519-dalek/src/field.rs

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
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 51 - 1)
    (pow : Field51_as_Nat v * Field51_as_Nat v ≡ Field51_as_Nat ONE [MOD p]) :
    ∃ c r, invsqrt v = ok (c, r) ∧
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat r % p
    let i_nat := Field51_as_Nat SQRT_M1 % p

    -- Case 1: If v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
    (v_nat = 0 →
    c.val = 0#u8 ∧ r_nat = 0) ∧

    -- Case 2: If v ≢ 0 (mod p) and ∃ x, x^2 ≡ v (mod p), then c.val = 1 and r^2 * v ≡ 1 (mod p)
    (v_nat ≠ 0 ∧ (∃ x : Nat, x^2 % p = v_nat) →
    c.val = 1#u8 ∧ (r_nat^2 * v_nat) % p = 1) ∧

    -- Case 3: If v ≢ 0 (mod p) and ¬∃ x, x^2 ≡ v (mod p), then c.val = 0 and r^2 * v ≡ SQRT_M1 (mod p)
    (v_nat ≠ 0 ∧ ¬(∃ x : Nat, x^2 % p = v_nat) →
    c.val = 0#u8 ∧ (r_nat^2 * v_nat) % p = i_nat)

    := by
    unfold invsqrt
    progress as ⟨ u, one, h1, h2, h3, h4⟩
    · unfold ONE ONE_body
      decide
    use u
    use one
    simp
    constructor
    · intro h5
      apply h2
      simp[h5]
      unfold ONE ONE_body
      decide
    constructor
    · intro h5 x hx
      have : ¬Field51_as_Nat ONE % p = 0 := by
        unfold ONE ONE_body
        decide
      simp[this, h5] at h3
      have h3:= h3 x
      rw[← Nat.ModEq] at h3
      rw[← Nat.ModEq] at hx
      have : Field51_as_Nat ONE % p =1 :=by
        unfold ONE ONE_body
        decide
      rw[this] at h3
      apply h3
      have := Nat.ModEq.mul_right (Field51_as_Nat v) hx
      apply Nat.ModEq.trans this
      exact pow
    · intro h5 hx
      have : Field51_as_Nat ONE % p =1 :=by
        unfold ONE ONE_body
        decide
      simp[this] at h4
      apply h4
      ·  exact h5
      · intro x hx1
        apply hx x
        rw[← Nat.ModEq]
        have : 1 = 1 % p:= by decide
        rw [this, ← Nat.ModEq] at hx1
        have eq1:= Nat.ModEq.mul_right (Field51_as_Nat v) hx1
        have eq2:= Nat.ModEq.mul_left (x ^2) pow
        rw[← mul_assoc] at eq2
        have eq3: Field51_as_Nat ONE % p =1 :=by
          unfold ONE ONE_body
          decide
        have : 1 = 1 % p:= by decide
        rw [this, ← Nat.ModEq] at eq3
        have eq4:= Nat.ModEq.mul_left (x ^2) eq3
        have := Nat.ModEq.trans eq2 eq4
        have := Nat.ModEq.trans (Nat.ModEq.symm eq1) this
        simp at this
        exact (Nat.ModEq.symm this)

end curve25519_dalek.field.FieldElement51
