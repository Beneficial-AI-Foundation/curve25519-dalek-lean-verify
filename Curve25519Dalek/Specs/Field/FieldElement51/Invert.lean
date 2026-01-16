/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Field.FieldElement51.Pow22501
import Curve25519Dalek.Defs.Edwards.Curve
/-! # Spec Theorem for `FieldElement51::invert`

Specification and proof for `FieldElement51::invert`.

This function computes the multiplicative inverse of a field element r in 𝔽_p where p = 2^255 - 19.
The inverse is computed as r^(p-2), since r^(p-2) * r = r^(p-1) = 1 (mod p) by Fermat's Little Theorem.

This function returns zero on input zero.

**Source**: curve25519-dalek/src/field.rs

-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.field.FieldElement51

/-
Natural language description:

    • Computes the multiplicative inverse r^(-1) of a field element r in 𝔽_p where p = 2^255 - 19
    • The inverse is computed as r^(p-2) = r^(2^255-21) using the identity r^(p-2) * r = r^(p-1) = 1 (mod p)
    • The field element is represented in radix 2^51 form with five u64 limbs
    • Returns zero when the input is zero

Natural language specs:

    • The function succeeds (no panic)
    • For any nonzero field element r, the result r' satisfies:
      - Field51_as_Nat(r') * Field51_as_Nat(r) ≡ 1 (mod p)
    • For zero input, the result is zero:
      - Field51_as_Nat(r) ≡ 0 (mod p) → Field51_as_Nat(r') ≡ 0 (mod p)
-/

/-- **Spec and proof concerning `field.FieldElement51.invert`**:
- No panic for field element inputs r (always returns r' successfully)
- If r ≢ 0 (mod p), then Field51_as_Nat(r') * Field51_as_Nat(r) ≡ 1 (mod p)
- If r ≡ 0 (mod p), then Field51_as_Nat(r') ≡ 0 (mod p)
-/

theorem prime_25519 : Nat.Prime p := by
  have h : Fact (Nat.Prime p) := by infer_instance
  exact h.out



lemma coprime_of_prime_not_dvd {a p : ℕ}
(hp : p.Prime) (hpa : ¬ p ∣ a) : Nat.Coprime a p := by
  have hgp_div_p : gcd a p ∣ p := gcd_dvd_right a p
  rcases (Nat.dvd_prime hp).1 hgp_div_p with hgp1 | hgp2
  · simpa [Nat.Coprime, hgp1]
  · have : p ∣ a := by simpa [hgp2] using gcd_dvd_left a p
    exact (hpa this).elim

@[progress]
theorem invert_spec (r : backend.serial.u64.field.FieldElement51) (h_bounds : ∀ i, i < 5 → (r[i]!).val < 2 ^ 54) :
    invert r ⦃ r' =>
      let r_nat := Field51_as_Nat r % p
      let r'_nat := Field51_as_Nat r' % p
      (r_nat ≠ 0 → (r'_nat * r_nat) % p = 1) ∧
      (r_nat = 0 → r'_nat = 0) ∧
      (∀ i, i < 5 → (r'[i]!).val < 2 ^ 52) ⦄ := by
  sorry

end curve25519_dalek.field.FieldElement51
