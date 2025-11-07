/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::sqrt_ratio_i`

Specification and proof for `FieldElement51::sqrt_ratio_i`.

This function computes a nonnegative square root of u/v or i*u/v (where i = sqrt(-1) = SQRT_M1 constant),
returning a flag indicating which case occurred and handling zero inputs specially.

**Source**: curve25519-dalek/src/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.field.FieldElement51

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

/-- **Spec and proof concerning `field.FieldElement51.sqrt_ratio_i`**:
- No panic for field element inputs u and v (always returns (c, r) successfully)
- The result satisfies exactly one of four mutually exclusive cases:
  1. If u ≡ 0 (mod p), then c.val = 1 and r ≡ 0 (mod p)
  2. If u ≢ 0 (mod p) and v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
  3. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 1 and r^2 ≡ u * v^(-1) (mod p)
  4. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ¬∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 0 and r^2 ≡ SQRT_M1 * u * v^(-1) (mod p)
-/
@[progress]
theorem sqrt_ratio_i_spec

    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val ≤ 2 ^ 51 - 1)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 51 - 1) :

    ∃ c r, sqrt_ratio_i u v = ok (c, r) ∧
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat r % p
    let i_nat := Field51_as_Nat backend.serial.u64.constants.SQRT_M1 % p

    -- Case 1: u is zero
    (u_nat = 0 →
    c.val = 1#u8 ∧ r_nat = 0) ∧

    -- Case 2: u is nonzero and v is zero
    (u_nat ≠ 0 ∧ v_nat = 0 →
    c.val = 0#u8 ∧ r_nat = 0) ∧

    -- Case 3: u and v are nonzero and u/v is a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.val = 1#u8 ∧ (r_nat^2 * v_nat) % p = u_nat) ∧

    -- Case 4: u and v are nonzero and u/v is not a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ ¬(∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.val = 0#u8 ∧ (r_nat^2 * v_nat) % p = (i_nat * u_nat) % p)

    := by
    sorry

end curve25519_dalek.field.FieldElement51
