/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.Step1
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.Step2

/-! # Spec Theorem for `CompressedRistretto::decompress`

Specification and proof for `CompressedRistretto::decompress`.

This function implements the Ristretto decompression (DECODE) function, which attempts to
decode a (valid) 32-byte representation back to a RistrettoPoint. The function is defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.1).

It takes a CompressedRistretto (a 32-byte array) and attempts to produce the associated RistrettoPoint,
returning None if the input byte array is not a valid canonical encoding.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Edwards Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.ristretto.CompressedRistretto

/-- When `decompress_step1` returns `some val`, `val` equals the field element `s.toField`
    computed by step_1. This follows from the uniqueness of the output value. -/
private lemma decompress_step1_val_eq (c : CompressedRistretto)
    (s : backend.serial.u64.field.FieldElement51)
    (hs : s.toField = ((U8x32_as_Nat c % 2 ^ 255 : ℕ) : ZMod p))
    {val : ZMod p} (h : decompress_step1 c = some val) :
    val = s.toField := by
  simp only [decompress_step1] at h
  split_ifs at h with h_cond
  simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le, not_or, not_le] at h_cond
  have h_lt_p : U8x32_as_Nat c < p := h_cond.1
  have h_lt_255 : U8x32_as_Nat c < 2 ^ 255 := lt_trans h_lt_p (by decide)
  rw [Option.some.injEq] at h
  rw [← h, hs, Nat.mod_eq_of_lt h_lt_255]

/-- **Spec and proof concerning `ristretto.CompressedRistretto.decompress`**:
- The function always succeeds for all U8x32 input arrays (no panic)
- If the input is not valid, then the output is none
- If the input is valid, then the output is a valid Ristretto point that reflects the
  output of the pure mathematical decompression function
-/
@[progress]
theorem decompress_spec (comp : CompressedRistretto) :
    decompress comp ⦃ result =>
    (¬comp.IsValid → result = none) ∧
    (comp.IsValid →
        ∃ rist,
        result = some rist ∧
        RistrettoPoint.IsValid rist ∧
        decompress_pure comp = some rist.toPoint) ⦄ := by
  unfold decompress
  progress as ⟨step1, h1⟩
  obtain ⟨h_tight, h_valid, h_field, h_enc, h_neg_iff, h_bridge⟩ := h1
  -- Convert WP goal to existential form so bind_ok can fire
  rw [spec_equiv_exists]
  -- Unfold Choice operations to if-then-else with ok
  simp only [subtle.Choice.Insts.CoreOpsBitNotChoice.not,
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor,
    Bool.Insts.CoreConvertFromChoice.from]
  -- Helper: derive decompress_step1 = none from flag failure
  have h_step1_none : ¬(step1.1.val = 1#u8 ∧ step1.2.1.val = 0#u8) →
      decompress_step1 comp = none := by
    intro h_fail
    rcases h_opt : decompress_step1 comp with _ | val
    · rfl
    · exfalso
      rw [decompress_step1_val_eq comp step1.2.2 h_field h_opt] at h_opt
      exact h_fail (h_bridge.mp h_opt)
  -- Case split on s_encoding_is_canonical
  by_cases h_canon : step1.1.val = 1#u8
  · -- Canonical encoding
    by_cases h_s_neg : step1.2.1.val = 1#u8
    · -- Negative s: return none
      refine ⟨none, ?_, fun _ => rfl, fun ⟨_, h⟩ => ?_⟩
      · simp only [h_canon, ↓reduceIte, Choice.zero, h_s_neg, or_true, Choice.one, bind_tc_ok,
        decide_eq_true_eq]
      · simp only [decompress_pure, h_step1_none (by simp only [h_s_neg, Nat.not_eq,
        UScalar.ofNat_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero,
        zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq, and_false]), Option.bind_none,
        reduceCtorEq] at h
    · -- Non-negative s: proceed to step_2
      have h_s_neg_zero : step1.2.1.val = 0#u8 := by
        rcases step1.2.1.valid with h | h <;> [exact h; exact absurd h h_s_neg]
      -- Evaluate first Choice chain: reduces ok-binds via Bind.bind + bind_ok
      simp only [Bind.bind, h_canon, h_s_neg_zero, Choice.zero, Choice.one,
        bind_ok, ↓reduceIte]
      -- Now the computation has reached step_2
      -- Get step_2 result via its spec
      have h_s_bounds : ∀ i < 5, step1.2.2[i]!.val < 2 ^ 52 := by
        intro i hi; exact lt_trans (h_tight i hi) (by norm_num)
      have ⟨⟨ok1, t_neg, y_zero, res⟩,
        h_step2_eq, ⟨h_ok1_iff, h_t_neg_iff, h_y_zero_iff⟩,
        h_step2_bridge, h_step2_valid⟩ :=
        spec_imp_exists (decompress.step_2_spec step1.2.2 h_s_bounds)
      -- Compose step1 + step2 into decompress_pure
      have h_ds1 : decompress_step1 comp = some step1.2.2.toField :=
        h_bridge.mpr ⟨h_canon, h_s_neg_zero⟩
      -- Helper: derive decompress_step2 = none from step2 flag failure
      have h_step2_none : ¬(ok1.val = 1#u8 ∧ t_neg.val = 0#u8 ∧ y_zero.val = 0#u8) →
          decompress_step2 step1.2.2.toField = none := by
        intro h_fail
        rcases h_opt : decompress_step2 step1.2.2.toField with _ | pt
        · rfl
        · exfalso
          exact h_fail ⟨((h_step2_bridge pt).mp h_opt).1,
            ((h_step2_bridge pt).mp h_opt).2.1, ((h_step2_bridge pt).mp h_opt).2.2.1⟩
      -- Rewrite with step_2 result
      rw [h_step2_eq]
      simp only [bind_ok]
      by_cases h_ok1 : ok1.val = 1#u8
      · -- invsqrt succeeded
        simp only [h_ok1, ↓reduceIte, bind_ok]
        by_cases h_t_neg : t_neg.val = 1#u8
        · -- t_is_negative: return none
          simp only [h_t_neg]
          exact ⟨none, rfl, fun _ => rfl, fun ⟨_, h⟩ => by
            simp only [decompress_pure, h_ds1, Option.bind_some, h_step2_none (by simp only [h_t_neg,
              Nat.not_eq, UScalar.ofNat_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one,
              not_lt_zero, zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq, false_and,
              and_false]),
              reduceCtorEq] at h⟩
        · by_cases h_y_zero : y_zero.val = 1#u8
          · -- y_is_zero: return none
            have h_t_neg_zero : t_neg.val = 0#u8 := by
              rcases t_neg.valid with h | h <;> [exact h; exact absurd h h_t_neg]
            simp only [h_t_neg_zero, h_y_zero]
            exact ⟨none, rfl, fun _ => rfl, fun ⟨_, h⟩ => by
              simp only [decompress_pure, h_ds1, Option.bind_some,
                h_step2_none (by simp only [h_y_zero, Nat.not_eq, UScalar.ofNat_val_eq, ne_eq,
                  one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero, zero_lt_one, or_true,
                  or_self, UScalar.val_not_eq_imp_not_eq, and_false]), reduceCtorEq] at h⟩
          · -- ALL VALID: return some res
            have h_t_neg_zero : t_neg.val = 0#u8 := by
              rcases t_neg.valid with h | h <;> [exact h; exact absurd h h_t_neg]
            have h_y_zero_zero : y_zero.val = 0#u8 := by
              rcases y_zero.valid with h | h <;> [exact h; exact absurd h h_y_zero]
            simp only [h_t_neg_zero, h_y_zero_zero]
            have h_ds2 : decompress_step2 step1.2.2.toField = some res.toPoint :=
              (h_step2_bridge res.toPoint).mpr ⟨h_ok1, h_t_neg_zero, h_y_zero_zero, rfl⟩
            refine ⟨some res, rfl, ?_, ?_⟩
            · intro h_not_valid
              exfalso; apply h_not_valid
              exact ⟨res.toPoint,
                by simp only [decompress_pure, h_ds1, Option.bind_some, h_ds2]⟩
            · intro _
              exact ⟨res, rfl,
                h_step2_valid ⟨h_ok1, h_t_neg_zero, h_y_zero_zero⟩,
                by simp only [decompress_pure, h_ds1, Option.bind_some, h_ds2]⟩
      · -- invsqrt failed: return none
        simp only [h_ok1, ↓reduceIte, bind_ok]
        exact ⟨none, rfl, fun _ => rfl, fun ⟨_, h⟩ => by
          simp only [decompress_pure, h_ds1, Option.bind_some, h_step2_none (by simp only [h_ok1,
            false_and, not_false_eq_true]),
            reduceCtorEq] at h⟩
  · -- Non-canonical encoding: return none
    refine ⟨none, ?_, fun _ => rfl, fun ⟨_, h⟩ => ?_⟩
    · simp only [h_canon, ↓reduceIte, Choice.one, bind_tc_ok, decide_eq_true_eq, true_or]
    · simp only [decompress_pure, h_step1_none (by simp only [h_canon, false_and,
      not_false_eq_true]), Option.bind_none,
      reduceCtorEq] at h

end curve25519_dalek.ristretto.CompressedRistretto
