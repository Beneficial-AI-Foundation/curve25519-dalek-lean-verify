/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Pow2K
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
/-! # Spec Theorem for `FieldElement51::pow22501`

Specification and proof for `FieldElement51::pow22501`.

This function computes (r^(2^250-1), r^11) for a field element r in 𝔽_p where p = 2^255 - 19.

**Source**: curve25519-dalek/src/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51
  (mul_spec)
namespace curve25519_dalek.field.FieldElement51

set_option exponentiation.threshold 100000

/-! ### Helper lemmas for exponent chain reasoning

These compose `Nat.ModEq` steps for square, multiply, and power-of-two chains.
Used here and re-used by `PowP58` and `Invert` which import this file. -/

lemma chain_sq {a r b e m : ℕ}
    (ha : a ≡ r ^ e [MOD m]) (hb : b ≡ a ^ 2 [MOD m]) :
    b ≡ r ^ (2 * e) [MOD m] :=
  hb.trans ((ha.pow 2).trans (by rw [← pow_mul, mul_comm]))

lemma chain_mul {r a b c ea eb m : ℕ}
    (ha : a ≡ r ^ ea [MOD m]) (hb : b ≡ r ^ eb [MOD m]) (hc : c ≡ a * b [MOD m]) :
    c ≡ r ^ (ea + eb) [MOD m] :=
  hc.trans ((ha.mul hb).trans (by rw [← pow_add]))

lemma chain_pow2k {r a b e k m : ℕ}
    (ha : a ≡ r ^ e [MOD m]) (hb : b ≡ a ^ (2 ^ k) [MOD m]) :
    b ≡ r ^ (e * 2 ^ k) [MOD m] :=
  hb.trans ((ha.pow (2 ^ k)).trans (by rw [← pow_mul]))

/-- **Spec and proof concerning `field.FieldElement51.pow22501`**:
- No panic (always returns (r1, r2) successfully)
- Field51_as_Nat(r1) ≡ Field51_as_Nat(r)^(2^250-1) (mod p)
  Field51_as_Nat(r2) ≡ Field51_as_Nat(r)^11 (mod p)
-/
@[progress]
theorem pow22501_spec (r : backend.serial.u64.field.FieldElement51)
    (h_bounds : ∀ i, i < 5 → (r[i]!).val < 2 ^ 54) :
    pow22501 r ⦃ result =>
    let r1 := result.1
    let r2 := result.2
    Field51_as_Nat r1 % p = (Field51_as_Nat r ^ (2 ^ 250 - 1)) % p ∧
    Field51_as_Nat r2 % p = (Field51_as_Nat r ^ 11) % p ∧
    (∀ i, i < 5 → (r1[i]!).val < 2 ^ 52) ∧
    (∀ i, i < 5 → (r2[i]!).val < 2 ^ 52) ⦄ := by
  unfold pow22501
  -- Step through the 21 field operations with explicit spec theorems.
  -- Bounds preconditions are auto-solved by progress.
  progress with square_spec as ⟨ t0, ht0, ht0b ⟩
  progress with square_spec as ⟨ fe, hfe, hfeb ⟩
  progress with square_spec as ⟨ t1, ht1, ht1b ⟩
  progress with mul_spec as ⟨ t2, ht2, ht2b ⟩
  progress with mul_spec as ⟨ t3, ht3, ht3b ⟩
  progress with square_spec as ⟨ t4, ht4, ht4b ⟩
  progress with mul_spec as ⟨ t5, ht5, ht5b ⟩
  progress with pow2k_spec as ⟨ t6, ht6, ht6b ⟩
  progress with mul_spec as ⟨ t7, ht7, ht7b ⟩
  progress with pow2k_spec as ⟨ t8, ht8, ht8b ⟩
  progress with mul_spec as ⟨ t9, ht9, ht9b ⟩
  progress with pow2k_spec as ⟨ t10, ht10, ht10b ⟩
  progress with mul_spec as ⟨ t11, ht11, ht11b ⟩
  progress with pow2k_spec as ⟨ t12, ht12, ht12b ⟩
  progress with mul_spec as ⟨ t13, ht13, ht13b ⟩
  progress with pow2k_spec as ⟨ t14, ht14, ht14b ⟩
  progress with mul_spec as ⟨ t15, ht15, ht15b ⟩
  progress with pow2k_spec as ⟨ t16, ht16, ht16b ⟩
  progress with mul_spec as ⟨ t17, ht17, ht17b ⟩
  progress with pow2k_spec as ⟨ t18, ht18, ht18b ⟩
  progress with mul_spec as ⟨ t19, ht19, ht19b ⟩
  -- Chain modular congruences: each step computes the exponent of r.
  -- Exponents: t0→2, fe→4, t1→8, t2→9, t3→11, t4→22, t5→31,
  --   t6→992, t7→1023, ..., t19→(2^250-1)
  have exp_r : Field51_as_Nat r ≡ (Field51_as_Nat r) ^ 1 [MOD p] := by rw [pow_one]
  have exp_t0 := chain_sq exp_r ht0
  have exp_fe := chain_sq exp_t0 hfe
  have exp_t1 := chain_sq exp_fe ht1
  have exp_t2 := chain_mul exp_r exp_t1 ht2
  have exp_t3 := chain_mul exp_t0 exp_t2 ht3
  have exp_t4 := chain_sq exp_t3 ht4
  have exp_t5 := chain_mul exp_t2 exp_t4 ht5
  have exp_t6 := chain_pow2k exp_t5 ht6
  have exp_t7 := chain_mul exp_t6 exp_t5 ht7
  have exp_t8 := chain_pow2k exp_t7 ht8
  have exp_t9 := chain_mul exp_t8 exp_t7 ht9
  have exp_t10 := chain_pow2k exp_t9 ht10
  have exp_t11 := chain_mul exp_t10 exp_t9 ht11
  have exp_t12 := chain_pow2k exp_t11 ht12
  have exp_t13 := chain_mul exp_t12 exp_t7 ht13
  have exp_t14 := chain_pow2k exp_t13 ht14
  have exp_t15 := chain_mul exp_t14 exp_t13 ht15
  have exp_t16 := chain_pow2k exp_t15 ht16
  have exp_t17 := chain_mul exp_t16 exp_t15 ht17
  have exp_t18 := chain_pow2k exp_t17 ht18
  have exp_t19 := chain_mul exp_t18 exp_t13 ht19
  exact ⟨exp_t19, exp_t3, ht19b, ht3b⟩

end curve25519_dalek.field.FieldElement51
