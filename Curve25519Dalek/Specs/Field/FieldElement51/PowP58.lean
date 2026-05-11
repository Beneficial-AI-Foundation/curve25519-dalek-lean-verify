/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Field.FieldElement51.Pow22501
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul

/-!
# Spec theorem for `curve25519_dalek::field::FieldElement51::pow_p58`

This function computes `r^((p-5)/8)` for a field element `r` in `𝔽_p` where `p = 2^255 - 19`,
and thus `(p-5)/8 = 2^252 - 3`.

Source: "curve25519-dalek/src/field.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
  (mul_spec)
namespace curve25519_dalek.field.FieldElement51

/-- The exponent `(p-5)/8 = 2^252 - 3`, used in the pow_p58 computation. -/
def pow_p58_exp : Nat := 2 ^ 252 - 3

/-- Unfolding lemma for `pow_p58_exp`, exposing its underlying value `2^252 - 3`.
Needed because `pow_p58_exp` is marked irreducible below, which blocks definitional
unfolding in tactics such as `rw`. -/
theorem pow_p58_exp_def : pow_p58_exp = 2 ^ 252 - 3 := rfl

attribute [irreducible] pow_p58_exp

/-- **Spec theorem for `curve25519_dalek::field::FieldElement51::pow_p58`**
• The function never panics, given that each limb of `self` is bounded by `2^52 - 1`
• `Field51_as_Nat(result) ≡ Field51_as_Nat(self) ^ (2^252 - 3) (mod p)`
• Each limb of the result is bounded by `2^52`
-/
@[step]
theorem pow_p58_spec (self : FieldElement51) (h_bounds : ∀ i, i < 5 → (self[i]!).val ≤ 2 ^ 52 - 1) :
    pow_p58 self ⦃ (result : FieldElement51) =>
      Field51_as_Nat result % p = (Field51_as_Nat self ^ pow_p58_exp) % p ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by
  unfold pow_p58
  step with pow22501_spec as ⟨ t19, ht19_mod, _, ht19b, _ ⟩
  step with pow2k_spec as ⟨ t20, ht20, ht20b ⟩
  step with mul_spec as ⟨ res, hres, hresb ⟩
  have exp_r : Field51_as_Nat self ≡ (Field51_as_Nat self) ^ 1 [MOD p] := by rw [pow_one]
  have exp_t20 := chain_pow2k ht19_mod ht20
  rw [pow_p58_exp_def]
  exact ⟨chain_mul exp_r exp_t20 hres, hresb⟩

end curve25519_dalek.field.FieldElement51
