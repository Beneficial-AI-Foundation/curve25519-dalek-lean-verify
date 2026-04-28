/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectivePoint.Double
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsProjective
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
import Mathlib

/-! # Spec Theorem for `EdwardsPoint::mul_by_pow_2`

Specification and proof for `EdwardsPoint::mul_by_pow_2`.

This function computes [2^k]e (the Edwards point e doubled k times for some natural k > 0)
by successive doublings.

**Source**: curve25519-dalek/src/edwards.rs:1328-1340
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.curve_models.ProjectivePoint
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint e and a positive integer k, and returns the result of doubling the point
k times (i.e., computes [2^k]e where e is the input point)

natural language specs:

• For k = 1, returns double(e)
• For k > 1, satisfies the recursive property: mul_by_pow_2(e, k) = double(mul_by_pow_2(e, k-1))
-/

/-- Loop spec for `mul_by_pow_2_loop`: repeatedly doubles `s` via
`ProjectivePoint.double` + `CompletedPoint.as_projective` from counter `i` up to `k - 1`.

Loop invariant at entry: `s.toPoint' hs_on = 2^i • P₀` for a reference point `P₀`.
At exit (counter `k - 1`), `result.toPoint' h_on = 2^(k-1) • P₀`.

Uses the weaker bounds `X, Y < 2^53` + `Z.IsValid` rather than `IsValid`'s `< 2^52`:
the initial `s` (from `EdwardsPoint.as_projective`) has only `< 2^53`, but each loop
iteration's `CompletedPoint.as_projective` produces `ProjectivePoint.IsValid` whose
`< 2^52` bounds imply the weaker ones. So the invariant is self-sustaining. -/
@[step]
theorem mul_by_pow_2_loop_spec
    (k : U32) (s : ProjectivePoint) (i : U32)
    (hk : k.val > 0) (hi : i.val ≤ k.val - 1)
    (hs_on : s.OnCurve)
    (hs_X : ∀ j < 5, s.X[j]!.val < 2 ^ 53)
    (hs_Y : ∀ j < 5, s.Y[j]!.val < 2 ^ 53)
    (hs_Z : s.Z.IsValid)
    (P₀ : Point Ed25519)
    (hs_point : s.toPoint' hs_on = 2 ^ i.val • P₀) :
    mul_by_pow_2_loop k s i ⦃ (result : ProjectivePoint) =>
      ∃ h_on : result.OnCurve,
        (∀ j < 5, result.X[j]!.val < 2 ^ 53) ∧
        (∀ j < 5, result.Y[j]!.val < 2 ^ 53) ∧
        result.Z.IsValid ∧
        result.toPoint' h_on = 2 ^ (k.val - 1) • P₀ ⦄ := by
  induction h_rem : (k.val - 1 - i.val) generalizing i s with
  | zero =>
    -- i.val = k.val - 1, loop returns ok s
    have hi_eq : i.val = k.val - 1 := by omega
    unfold mul_by_pow_2_loop
    step as ⟨i1, hi1_post1, hi1_post2⟩
    have hilt : ¬ (i < i1) := by scalar_tac
    simp only [hilt, ↓reduceIte, spec_ok]
    refine ⟨hs_on, hs_X, hs_Y, hs_Z, ?_⟩
    rw [← hi_eq]; exact hs_point
  | succ n ih =>
    -- i.val < k.val - 1, body executes then recurses
    have hlt : i.val < k.val - 1 := by omega
    unfold mul_by_pow_2_loop
    step as ⟨i1, hi1_post1, hi1_post2⟩
    have hiltu : i < i1 := by scalar_tac
    simp only [hiltu, ↓reduceIte]
    -- double s → r with r.IsValid, r.toPoint = s.toPoint' hs_on + s.toPoint' hs_on
    obtain ⟨r, hr_run, hr_valid, hr_toPoint⟩ :=
      double_spec_core s hs_on hs_X hs_Y hs_Z
    simp only [hr_run]
    -- CompletedPoint.as_projective r → proj with proj.IsValid, proj.toPoint = r.toPoint
    obtain ⟨proj, hproj_run, hproj_valid, hproj_toPoint⟩ :=
      spec_imp_exists (CompletedPoint.as_projective_spec r hr_valid)
    simp only [bind_tc_ok, hproj_run, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      exists_and_left]
    -- Increment counter
    step as ⟨i2, hi2_post1⟩
    -- Build IH preconditions for (proj, i2)
    have h_proj_on : proj.OnCurve := hproj_valid.toOnCurve
    have h_proj_X : ∀ j < 5, proj.X[j]!.val < 2 ^ 53 :=
      fun j hj => Nat.lt_of_lt_of_le (hproj_valid.X_bounds j hj) (by norm_num)
    have h_proj_Y : ∀ j < 5, proj.Y[j]!.val < 2 ^ 53 :=
      fun j hj => Nat.lt_of_lt_of_le (hproj_valid.Y_bounds j hj) (by norm_num)
    have h_proj_Z : proj.Z.IsValid :=
      FieldElement51.IsValid_of_lt_pow hproj_valid.Z_bounds (by decide)
    -- Point chain: s.toPoint' = 2^i • P₀ → r.toPoint = 2 • s.toPoint' = 2^(i+1) • P₀
    -- → proj.toPoint = r.toPoint → proj.toPoint' = proj.toPoint (IsValid)
    have h_proj_point : proj.toPoint' h_proj_on = 2 ^ i2.val • P₀ := by
      have heq_topoint : proj.toPoint' h_proj_on = proj.toPoint := by
        unfold ProjectivePoint.toPoint; rw [dif_pos hproj_valid]
      have hi2_val : i2.val = i.val + 1 := by scalar_tac
      rw [heq_topoint, hproj_toPoint, hr_toPoint, hs_point, hi2_val,
          ← two_nsmul, ← mul_smul]
      congr 1; ring
    -- Apply IH at (proj, i2) with remaining counter n
    have h_i2_le : i2.val ≤ k.val - 1 := by scalar_tac
    have h_new_rem : k.val - 1 - i2.val = n := by scalar_tac
    let* ⟨ result, result_post ⟩ ← ih
    obtain ⟨h_on, hX, hY, hZ, hpt⟩ := result_post
    exact ⟨hX, hY, hZ, h_on, hpt⟩

/-- **Spec and proof concerning `edwards.EdwardsPoint.mul_by_pow_2`**:
- For k = 1, returns the doubled point 2e for the input point e
- For k > 1, returns a point equal to double(mul_by_pow_2(e, k-1))
-/
@[step]
theorem mul_by_pow_2_spec (self : EdwardsPoint) (k : U32)
    (hself : self.IsValid) (hk : k.val > 0) :
    mul_by_pow_2 self k ⦃ result =>
      result.IsValid ∧
      result.toPoint = (2 ^ k.val) • self.toPoint ⦄ := by
  unfold mul_by_pow_2
  let* ⟨ hk2 ⟩ ← massert_spec
  let* ⟨ s, s_post1, s_post2, s_post3 ⟩ ← as_projective_spec
  let* ⟨ s1, s1_post ⟩ ← mul_by_pow_2_loop_spec
  -- P₀: reference point for loop invariant
  · exact self.toPoint
  -- s.OnCurve: inherit from self.OnCurve via s_post1/2/3
  · exact {
      Z_ne_zero := by rw [s_post3]; exact hself.Z_ne_zero
      on_curve := by rw [s_post1, s_post2, s_post3]; exact hself.on_curve
    }
  -- s.X[j]! < 2^53
  · intro j hj; rw [s_post1]; exact hself.X_bounds j hj
  -- s.Y[j]! < 2^53
  · intro j hj; rw [s_post2]; exact hself.Y_bounds j hj
  -- s.Z.IsValid
  · rw [s_post3]
    exact FieldElement51.IsValid_of_lt_pow hself.Z_bounds (by decide)
  -- s.toPoint' _ = 2^0 • self.toPoint = self.toPoint
  · show s.toPoint' _ = _
    simp only [show ((0#u32 : U32).val) = 0 from rfl, pow_zero, one_nsmul]
    unfold EdwardsPoint.toPoint
    rw [dif_pos hself]
    simp only [ProjectivePoint.toPoint', s_post1, s_post2, s_post3, EdwardsPoint.toPoint']
  -- Main goal: apply final double + as_extended using existential specs
  obtain ⟨h_s1_on, h_s1_X, h_s1_Y, h_s1_Z, h_s1_point⟩ := s1_post
  obtain ⟨cp, hcp_run, hcp_valid, hcp_eq⟩ :=
    double_spec_core s1 h_s1_on h_s1_X h_s1_Y h_s1_Z
  simp only [hcp_run]
  apply WP.spec_mono (CompletedPoint.as_extended_spec cp hcp_valid)
  intro result ⟨_, _, _, _, _, _, _, _, h_result_valid, h_result_toPoint⟩
  refine ⟨h_result_valid, ?_⟩
  rw [h_result_toPoint, hcp_eq, h_s1_point]
  -- 2^(k-1) • P + 2^(k-1) • P = 2^k • P
  rw [← two_nsmul, ← mul_smul]
  fcongr 1
  rw [show k.val = (k.val - 1) + 1 from by omega, pow_succ, mul_comm]
  agrind


end curve25519_dalek.edwards.EdwardsPoint
