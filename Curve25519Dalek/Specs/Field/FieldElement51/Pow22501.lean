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

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.field.FieldElement51

set_option exponentiation.threshold 100000
/-
Natural language description:

    • Computes a pair of powers: (r^(2^250-1), r^11) for a field element r in 𝔽_p where p = 2^255 - 19
    • The field element is represented in radix 2^51 form with five u64 limbs
    • This is a helper function used in computing field inversions and other exponentiations

Natural language specs:

    • The function succeeds (no panic)
    • For any field element r, the result (r1, r2) satisfies:
      - Field51_as_Nat(r1) ≡ Field51_as_Nat(r)^(2^250-1) (mod p)
      - Field51_as_Nat(r2) ≡ Field51_as_Nat(r)^11 (mod p)
-/

/-- **Spec and proof concerning `field.FieldElement51.pow22501`**:
- No panic (always returns (r1, r2) successfully)
- Field51_as_Nat(r1) ≡ Field51_as_Nat(r)^(2^250-1) (mod p)
  Field51_as_Nat(r2) ≡ Field51_as_Nat(r)^11 (mod p)
-/
@[progress]
theorem pow22501_spec (r : backend.serial.u64.field.FieldElement51) (h_bounds : ∀ i, i < 5 → (r[i]!).val < 2 ^ 54) :
    spec (pow22501 r) (fun result =>
    let r1 := result.1
    let r2 := result.2
    Field51_as_Nat r1 % p = (Field51_as_Nat r ^ (2 ^ 250 - 1)) % p ∧
    Field51_as_Nat r2 % p = (Field51_as_Nat r ^ 11) % p ∧
    (∀ i, i < 5 → (r1[i]!).val < 2 ^ 52) ∧
    (∀ i, i < 5 → (r2[i]!).val < 2 ^ 52))
    := by
    unfold pow22501
    sorry
/- OLD PROOF (needs updating for WP spec form + timeout issues)
    unfold pow22501
    progress*
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t0_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (fe_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t1_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t0_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t2_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t3_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t2_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t4_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t5_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t6_post_1 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t5_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t7_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t8_post_1 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t7_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t9_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t10_post_1 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t9_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t11_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t12_post_1 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t7_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t13_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t14_post_1 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t13_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t15_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t16_post_1 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t15_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t17_post_2 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t18_post_1 i hi)
      simp
      --- END TASK
    · -- BEGIN TASK
      intro i hi
      apply lt_trans (t13_post_2 i hi)
      simp
      --- END TASK
    use t19
    use t3
    simp
    constructor
    · -- BEGIN TASK
      simp_all
      rw[← Nat.ModEq]
      apply Nat.ModEq.trans t19_post_1
      have := Nat.ModEq.mul_right (Field51_as_Nat t13) t18_post_2
      apply Nat.ModEq.trans this
      have one:= pow_one (Field51_as_Nat t15)
      have ht151:= pow_add (Field51_as_Nat t15) 1267650600228229401496703205376 1
      rw[one] at ht151
      have ht150:= Nat.ModEq.mul_right (Field51_as_Nat t15) t16_post_2
      rw[← ht151] at ht150
      have ht1715:= Nat.ModEq.trans t17_post_1 ht150
      have ht1715p:= Nat.ModEq.pow 1125899906842624 ht1715
      rw[← pow_mul] at ht1715p
      have one13:= pow_one (Field51_as_Nat t13)
      have ht131:= pow_add (Field51_as_Nat t13) 1125899906842624 1
      rw[one13] at ht131
      have ht130:= Nat.ModEq.mul_right (Field51_as_Nat t13) t14_post_2
      rw[← ht131] at ht130
      have ht1513:= Nat.ModEq.trans t15_post_1 ht130
      have ht1513p:= Nat.ModEq.pow ((1267650600228229401496703205376 + 1) * 1125899906842624) ht1513
      have ht1713:= Nat.ModEq.trans ht1715p ht1513p
      have := Nat.ModEq.mul_right (Field51_as_Nat t13) ht1713
      apply Nat.ModEq.trans this
      rw[← pow_mul]
      have := pow_add (Field51_as_Nat t13) ((1125899906842624 + 1) * ((1267650600228229401496703205376 + 1) *
      1125899906842624)) 1
      rw[one13] at this
      rw[← this]
      have one7:= pow_one (Field51_as_Nat t7)
      have ht91:= pow_add (Field51_as_Nat t7) 1024 1
      rw[one7] at ht91
      have ht90:= Nat.ModEq.mul_right (Field51_as_Nat t7) t8_post_2
      rw[← ht91] at ht90
      have ht97:= Nat.ModEq.trans t9_post_1 ht90
      have ht97p:= Nat.ModEq.pow 1048576 ht97
      have ht107:= Nat.ModEq.trans t10_post_2 ht97p
      have ht110:= Nat.ModEq.mul ht107 ht97
      have ht117:= Nat.ModEq.trans  t11_post_1 ht110
      have ht11p:= Nat.ModEq.pow 1024 ht117
      have ht127:= Nat.ModEq.trans t12_post_2 ht11p
      rw[← pow_mul, ← pow_add, ← pow_mul] at ht127
      have ht1270:= Nat.ModEq.mul_right (Field51_as_Nat t7) ht127
      have ht127p:= pow_add (Field51_as_Nat t7) ((((1024 + 1) * 1048576 + (1024 + 1)) * 1024)) 1
      rw[one7] at ht127p
      rw[← ht127p] at ht1270
      have ht137:= Nat.ModEq.trans t13_post_1 ht1270
      have one5:= pow_one (Field51_as_Nat t5)
      have ht51:= pow_add (Field51_as_Nat t5) 32 1
      rw[one5] at ht51
      have ht70:= Nat.ModEq.mul_right (Field51_as_Nat t5) t6_post_2
      rw[← ht51] at ht70
      have ht75:= Nat.ModEq.trans t7_post_1 ht70
      have ht3p:= Nat.ModEq.pow 2 t3_post_1
      rw[mul_pow] at ht3p
      have ht43:= Nat.ModEq.trans t4_post_1 ht3p
      have ht520:= Nat.ModEq.mul_left (Field51_as_Nat t2) ht43
      have ht52:= Nat.ModEq.trans t5_post_1 ht520
      rw[← mul_assoc, mul_comm, ← mul_assoc] at ht52
      have one2:= pow_one (Field51_as_Nat t2)
      have ht21:= pow_add (Field51_as_Nat t2) 2 1
      rw[one2] at ht21
      rw[← ht21] at ht52
      have hfep:= Nat.ModEq.pow 2 fe_post_1
      have hfep1:= Nat.ModEq.trans t1_post_1 hfep
      have ht20:= Nat.ModEq.mul_left (Field51_as_Nat r) hfep1
      have ht2fep1:= Nat.ModEq.trans t2_post_1 ht20
      rw[← pow_mul] at  ht2fep1
      have hr:= Nat.ModEq.pow (2*2) t0_post_1
      have ht200:= Nat.ModEq.mul_left (Field51_as_Nat r) hr
      have ht201:= Nat.ModEq.trans ht2fep1 ht200
      clear ht200 hr ht2fep1 ht20 hfep1 hfep ht21
      rw[← pow_mul] at ht201
      have oner:= pow_one (Field51_as_Nat r)
      have ht202:= pow_add (Field51_as_Nat r) 1 (2 * (2 * 2))
      rw[oner] at ht202
      rw[← ht202] at ht201
      have ht203:= Nat.ModEq.pow (2+1) ht201
      rw[← pow_mul] at ht203
      have ht0r:= Nat.ModEq.pow 2 t0_post_1
      clear ht201 ht202
      have := Nat.ModEq.mul ht203 ht0r
      have ht50:= Nat.ModEq.trans ht52 this
      rw[← pow_mul,← pow_add] at ht50
      clear this ht0r ht203 one2 ht52 ht520 ht43 ht3p
      have ht700:= Nat.ModEq.pow (32 + 1) ht50
      have ht7r:= Nat.ModEq.trans ht75 ht700
      clear ht700 ht50 ht75 ht70 ht51 one5
      rw[← pow_mul] at ht7r
      have ht130:= Nat.ModEq.pow ((((1024 + 1) * 1048576 + (1024 + 1)) * 1024 + 1)) ht7r
      have ht13r:= Nat.ModEq.trans ht137 ht130
      rw[← pow_mul] at ht13r
      have ht13rp:= Nat.ModEq.pow ((1125899906842624 + 1) * ((1267650600228229401496703205376 + 1) * 1125899906842624) + 1) ht13r
      apply Nat.ModEq.trans ht13rp
      simp[← pow_mul]
      apply Nat.ModEq.rfl
      --- END TASK
    constructor
    · -- BEGIN TASK
      rw[← Nat.ModEq]
      apply Nat.ModEq.trans t3_post_1
      have := (Nat.ModEq.mul_left (Field51_as_Nat t0) t2_post_1 )
      apply Nat.ModEq.trans this
      rw[mul_comm, mul_assoc]
      have fep:= Nat.ModEq.pow 2 fe_post_1
      have :=Nat.ModEq.trans t1_post_1 fep
      have := Nat.ModEq.mul_right (Field51_as_Nat t0) this
      rw[← pow_mul] at this
      have one:= pow_one (Field51_as_Nat t0)
      have ht00:= pow_add (Field51_as_Nat t0) (2*2) 1
      rw[one] at ht00
      rw[← ht00] at this
      have ht0p:= Nat.ModEq.pow (2*2+1) t0_post_1
      have :=Nat.ModEq.trans this ht0p
      have := Nat.ModEq.mul_left (Field51_as_Nat r) this
      apply Nat.ModEq.trans this
      rw[← pow_mul]
      have one:= pow_one (Field51_as_Nat r)
      have := pow_add (Field51_as_Nat r)  1 (2 * (2 * 2 + 1))
      rw[one] at this
      rw[← this]
      --- END TASK
    constructor
    · -- BEGIN TASK
      intro i hi
      simp_all
      --- END TASK
    ·  -- BEGIN TASK
      intro i hi
      simp_all
      --- END TASK
    -/

end curve25519_dalek.field.FieldElement51
