/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.Step1
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.Step2

/-!
# Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::decompress`

Implements the Ristretto DECODE function (see §4.3.1 of
draft-irtf-cfrg-ristretto255-decaf448-08). Takes a `CompressedRistretto`
(a 32-byte array) and attempts to decode it back to a `RistrettoPoint`,
returning `none` if the input is not a valid canonical encoding.

Source: "curve25519-dalek/src/ristretto.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.ristretto
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

/-- **Spec theorem for `curve25519_dalek::ristretto::CompressedRistretto::decompress`**
• The function always succeeds for all U8x32 input arrays (no panic)
• If the input is not valid, then the output is none
• If the input is valid, then the output is a valid Ristretto point that reflects the
  output of the pure mathematical decompression function
-/
@[step]
theorem decompress_spec (self : CompressedRistretto) :
    decompress self ⦃ (result : Option RistrettoPoint) =>
      (¬self.IsValid → result = none) ∧
      (self.IsValid →
          ∃ rist,
          result = some rist ∧
          RistrettoPoint.IsValid rist ∧
          decompress_pure self = some rist.toPoint) ⦄ := by
  unfold decompress
  step as ⟨s_canon, s_neg, s, h1⟩
  obtain ⟨h_tight, h_valid, h_field, h_enc, h_neg_iff, h_bridge⟩ := h1
  -- Convert WP goal to existential form so bind_ok can fire
  rw [spec_equiv_exists]
  -- Unfold Choice operations to if-then-else with ok
  simp only [subtle.Choice.Insts.CoreOpsBitNotChoice.not,
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor,
    Bool.Insts.CoreConvertFromChoice.from]
  -- Helper: derive decompress_step1 = none from flag failure
  have h_step1_none : ¬(s_canon.val = 1#u8 ∧ s_neg.val = 0#u8) →
      decompress_step1 self = none := by
    intro h_fail
    rcases h_opt : decompress_step1 self with _ | val
    · rfl
    · exfalso
      rw [decompress_step1_val_eq self s h_field h_opt] at h_opt
      exact h_fail (h_bridge.mp h_opt)
  -- Case split on s_encoding_is_canonical
  by_cases h_canon : s_canon.val = 1#u8
  · -- Canonical encoding
    by_cases h_s_neg : s_neg.val = 1#u8
    · -- Negative s: return none
      refine ⟨none, ?_, fun _ => rfl, fun ⟨_, h⟩ => ?_⟩
      · simp only [h_canon, ↓reduceIte, Choice.zero, h_s_neg, or_true, Choice.one, bind_tc_ok,
        decide_eq_true_eq]
      · simp only [decompress_pure, h_step1_none (by simp only [h_s_neg, Nat.not_eq,
        UScalar.ofNatCore_val_eq, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, not_lt_zero,
        zero_lt_one, or_true, or_self, UScalar.val_not_eq_imp_not_eq, and_false]),
        Option.bind_none,
        reduceCtorEq] at h
    · -- Non-negative s: proceed to step_2
      have h_s_neg_zero : s_neg.val = 0#u8 := by
        rcases s_neg.valid with h | h <;> [exact h; exact absurd h h_s_neg]
      -- Evaluate first Choice chain: reduces ok-binds via Bind.bind + bind_ok
      simp only [Bind.bind, h_canon, h_s_neg_zero, Choice.zero, Choice.one,
        bind_ok, ↓reduceIte]
      norm_num
      -- Now the computation has reached step_2
      -- Get step_2 result via its spec
      have h_s_bounds : ∀ i < 5, s[i]!.val < 2 ^ 52 := by
        intro i hi; exact lt_trans (h_tight i hi) (by norm_num)
      have ⟨⟨ok1, t_neg, y_zero, res⟩,
        h_step2_eq, ⟨h_ok1_iff, h_t_neg_iff, h_y_zero_iff⟩,
        h_step2_bridge, h_step2_valid⟩ :=
        spec_imp_exists (decompress.step_2_spec s h_s_bounds)
      -- Compose step1 + step2 into decompress_pure
      have h_ds1 : decompress_step1 self = some s.toField :=
        h_bridge.mpr ⟨h_canon, h_s_neg_zero⟩
      -- Helper: derive decompress_step2 = none from step2 flag failure
      have h_step2_none : ¬(ok1.val = 1#u8 ∧ t_neg.val = 0#u8 ∧ y_zero.val = 0#u8) →
          decompress_step2 s.toField = none := by
        intro h_fail
        rcases h_opt : decompress_step2 s.toField with _ | pt
        · rfl
        · exfalso
          exact h_fail ⟨((h_step2_bridge pt).mp h_opt).1,
            ((h_step2_bridge pt).mp h_opt).2.1, ((h_step2_bridge pt).mp h_opt).2.2.1⟩
      -- Rewrite with step_2 result
      rw [h_step2_eq]
      simp only [bind_ok]
      -- Case split on the three boolean flags from step_2
      by_cases h_ok1 : (ok1.val = 1#u8)
      · -- ok1 = 1: subsequent flag c2 = 0 (success-so-far)
        by_cases h_t_neg : (t_neg.val = 0#u8)
        · -- t_neg = 0
          by_cases h_y_zero : (y_zero.val = 0#u8)
          · -- y_zero = 0: SUCCESS path → ok (some res)
            have h_t_neg_ne : ¬ t_neg.val = 1#u8 := by
              rw [h_t_neg]; decide
            have h_y_zero_ne : ¬ y_zero.val = 1#u8 := by
              rw [h_y_zero]; decide
            refine ⟨some res, ?_, ?_, ?_⟩
            · simp [h_ok1, h_t_neg_ne, h_y_zero_ne]
            · intro hnv
              exfalso
              apply hnv
              refine ⟨res.toPoint, ?_⟩
              unfold decompress_pure
              rw [h_ds1, Option.bind_some]
              exact (h_step2_bridge res.toPoint).mpr ⟨h_ok1, h_t_neg, h_y_zero, rfl⟩
            · intro _
              refine ⟨res, rfl, h_step2_valid ⟨h_ok1, h_t_neg, h_y_zero⟩, ?_⟩
              unfold decompress_pure
              rw [h_ds1, Option.bind_some]
              exact (h_step2_bridge res.toPoint).mpr ⟨h_ok1, h_t_neg, h_y_zero, rfl⟩
          · -- y_zero ≠ 0: FAIL path
            have h_y_zero_one : y_zero.val = 1#u8 := by
              rcases y_zero.valid with h | h
              · exact absurd h h_y_zero
              · exact h
            have h_t_neg_ne : ¬ t_neg.val = 1#u8 := by
              rw [h_t_neg]; decide
            have h_step2_none' : decompress_step2 s.toField = none :=
              h_step2_none (fun ⟨_, _, hz⟩ => h_y_zero (hz))
            refine ⟨none, ?_, fun _ => rfl, fun ⟨_, h⟩ => ?_⟩
            · simp [h_ok1, h_t_neg_ne, h_y_zero_one]
            · simp only [decompress_pure, h_ds1, Option.bind_some, h_step2_none',
                reduceCtorEq] at h
        · -- t_neg ≠ 0: FAIL path
          have h_t_neg_one : t_neg.val = 1#u8 := by
            rcases t_neg.valid with h | h
            · exact absurd h h_t_neg
            · exact h
          have h_step2_none' : decompress_step2 s.toField = none :=
            h_step2_none (fun ⟨_, ht, _⟩ => h_t_neg (ht))
          refine ⟨none, ?_, fun _ => rfl, fun ⟨_, h⟩ => ?_⟩
          · simp [h_ok1, h_t_neg_one]
          · simp only [decompress_pure, h_ds1, Option.bind_some, h_step2_none',
              reduceCtorEq] at h
      · -- ok1 ≠ 1: FAIL path
        have h_ok1_zero : ok1.val = 0#u8 := by
          rcases ok1.valid with h | h
          · exact h
          · exact absurd h h_ok1
        have h_step2_none' : decompress_step2 s.toField = none :=
          h_step2_none (fun ⟨hok, _, _⟩ => h_ok1 (hok))
        refine ⟨none, ?_, fun _ => rfl, fun ⟨_, h⟩ => ?_⟩
        · simp [h_ok1_zero]
        · simp only [decompress_pure, h_ds1, Option.bind_some, h_step2_none',
            reduceCtorEq] at h
  · -- Non-canonical encoding: return none
    refine ⟨none, ?_, fun _ => rfl, fun ⟨_, h⟩ => ?_⟩
    · simp only [h_canon, ↓reduceIte, Choice.one, bind_tc_ok, decide_eq_true_eq, true_or]
    · simp only [decompress_pure, h_step1_none (by simp only [h_canon, false_and,
      not_false_eq_true]), Option.bind_none,
      reduceCtorEq] at h

end curve25519_dalek.ristretto.CompressedRistretto
