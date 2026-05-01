/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Field.FieldElement51.Pow22501

/-!
# Spec theorem for `curve25519_dalek::field::FieldElement51::invert`

This function computes the multiplicative inverse of a field element r in 𝔽_p
where p = 2^255 - 19.
The inverse is r^(p-2), since r^(p-2) * r = r^(p-1) = 1 (mod p) by Fermat's Little Theorem.
The field element is represented in radix 2^51 form with five u64 limbs.

Source: "curve25519-dalek/src/field.rs"
-/

-- Allow kernel reduction of the large numerical exponent `p - 2 = 2^255 - 21`
-- (and `p - 1` from Fermat's Little Theorem) when typechecking the proof below.
set_option exponentiation.threshold 100000

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
  (mul_spec)

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

namespace curve25519_dalek.field.FieldElement51

/-- **Spec theorem for `curve25519_dalek::field::FieldElement51::invert`**
• No panic when each input limb of r satisfies `r[i].val < 2 ^ 54`
  (always returns r' successfully)
• If r ≢ 0 (mod p), then Field51_as_Nat(r') * Field51_as_Nat(r) ≡ 1 (mod p)
• If r ≡ 0 (mod p), then Field51_as_Nat(r') ≡ 0 (mod p)
• The output limbs satisfy `r'[i].val < 2^52` for all `i < 5`
-/
@[step]
theorem invert_spec (r : backend.serial.u64.field.FieldElement51)
    (h_bounds : ∀ i, i < 5 → (r[i]!).val < 2 ^ 54) :
    invert r ⦃ (r' : backend.serial.u64.field.FieldElement51) =>
      (Field51_as_Nat r % p ≠ 0 →
        (Field51_as_Nat r' % p * (Field51_as_Nat r % p)) % p = 1) ∧
      (Field51_as_Nat r % p = 0 → Field51_as_Nat r' % p = 0) ∧
      (∀ i, i < 5 → (r'[i]!).val < 2 ^ 52) ⦄ := by
  unfold invert
  -- invert = pow22501 → pow2k(t19, 5) → mul(t20, t3)
  step with pow22501_spec as ⟨ t19, ht19_mod, ht3_mod, ht19b, ht3b ⟩
  step with pow2k_spec as ⟨ t20, ht20, ht20b ⟩
  step with mul_spec as ⟨ res, hres, hresb ⟩
  -- Chain: t20 ≡ r^((2^250-1)*32), res ≡ r^((2^250-1)*32 + 11) = r^(p-2)
  -- The exponent (2^250-1)*2^5 + 11 = 2^255-21 = p-2 is verified by kernel reduction.
  have hpow : Field51_as_Nat res ≡ Field51_as_Nat r ^ (p - 2) [MOD p] :=
    chain_mul (chain_pow2k ht19_mod ht20) ht3_mod hres
  refine ⟨fun hne => ?_, fun h0 => ?_, hresb⟩
  · -- Nonzero case: res * r ≡ r^(p-2) * r = r^(p-1) ≡ 1 (mod p) by Fermat
    rw [Nat.ModEq] at hpow
    rw [hpow, ← Nat.mul_mod, ← pow_succ,
      show p - 2 + 1 = p - 1 from by unfold p; omega]
    have := Nat.ModEq.pow_card_sub_one_eq_one prime_25519
      (coprime_of_prime_not_dvd prime_25519 (fun h => hne (Nat.dvd_iff_mod_eq_zero.mp h)))
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by unfold p; omega : (1 : ℕ) < p)] at this
  · -- Zero case: r ≡ 0 (mod p) means p ∣ r, hence p ∣ r^(p-2), so r^(p-2) % p = 0
    rw [Nat.ModEq] at hpow
    rw [hpow]
    exact Nat.dvd_iff_mod_eq_zero.mp
      (dvd_pow (Nat.dvd_of_mod_eq_zero h0) (by unfold p; omega))

end curve25519_dalek.field.FieldElement51
