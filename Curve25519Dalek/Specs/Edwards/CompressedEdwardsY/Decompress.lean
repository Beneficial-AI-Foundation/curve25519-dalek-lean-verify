/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.Step1
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.Step2
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.AsBytes

/-!
# Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::decompress`

Attempts to decompress a 32-byte array (`CompressedEdwardsY`) to an `EdwardsPoint` in
extended twisted Edwards coordinates. The compressed representation encodes the
y-coordinate in the low 255 bits (bytes 0–30 plus the low 7 bits of byte 31, in
little-endian) and the sign (parity) of the x-coordinate in the high bit of byte 31.
Decompression involves:

- Extracting the y-coordinate from the byte array
- Extracting the sign bit from the high bit of byte 31
- Computing the (absolute value of the) x-coordinate from `y` by solving the curve
  equation `-x² + y² = 1 + dx²y²` for `x²`
- Adjusting the sign of `x` to match the encoded sign bit
- Returning `ok none` if the input does not encode a valid Edwards point, otherwise
  `ok (some ep)`

Source: "curve25519-dalek/src/edwards.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field Edwards
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-- **Spec theorem for `curve25519_dalek::edwards::CompressedEdwardsY::decompress`**
• The function always succeeds (no panic)
• Decompression returns `some` iff the encoded `y` (the low 255 bits of `self`) is a
  valid Edwards y-coordinate, i.e. some curve point has that y value
• On success, `ep.IsValid` holds (curve equation, `T = XY/Z`, bounds, `Z ≠ 0`)
• On success, `ep.Y.toField = y` — `Y` matches the encoded y-coordinate at the
  `ZMod` level
• On success, `Field51_as_Nat ep.Y ≡ (U8x32_as_Nat self % 2^255) [MOD p]` — same
  equality at the `Nat` level
• On success, `ep.Z.toField = 1` — `Z` is the field element 1
• On success, `Field51_as_Nat ep.Z % p = 1` — same equality at the `Nat` level
• On success, when `y² ≠ 1` (the non-degenerate case where `x ≠ 0`), the encoded
  sign bit (bit 7 of byte 31) matches the parity of `X`:
  `x_sign_bit ↔ (Field51_as_Nat ep.X % p) % 2 = 1`
-/
@[step]
theorem decompress_spec (self : CompressedEdwardsY) :
    decompress self ⦃ (result : Option EdwardsPoint) =>
      let y : CurveField := ((U8x32_as_Nat self % 2 ^ 255 : Nat) : CurveField)
      let x_sign_bit := self[31]!.val.testBit 7
      (result.isSome ↔ ∃ pt : Point Ed25519, pt.y = y) ∧
      (∀ ep, result = some ep →
        ep.IsValid ∧
        ep.Y.toField = y ∧
        Field51_as_Nat ep.Y ≡ (U8x32_as_Nat self % 2 ^ 255) [MOD p] ∧
        ep.Z.toField = 1 ∧
        Field51_as_Nat ep.Z % p = 1 ∧
        (y ^ 2 ≠ 1 →
          (x_sign_bit ↔ (Field51_as_Nat ep.X % p) % 2 = 1))) ⦄ := by
  unfold decompress
  -- Compose step_1_spec (explicit `let*` to avoid Pattern-8 self-recursion of `@[step]`)
  let* ⟨res1, post1⟩ ← step_1_spec
  obtain ⟨is_valid, X, Y, Z⟩ := res1
  obtain ⟨Y_mod, Y_bounds, Z_val, Z_bounds, X_bounds, X_parity, flag_iff, flag_curve⟩ := post1
  simp only [step_simps]
  -- Nat → CurveField bridges for Y and Z
  have hY_toField : Y.toField = ((U8x32_as_Nat self % 2 ^ 255 : Nat) : CurveField) := by
    simp only [FieldElement51.toField]
    exact lift_mod_eq _ _ Y_mod
  have hZ_toField : Z.toField = 1 := by
    simp only [FieldElement51.toField, Z_val]; push_cast; rfl
  by_cases h_flag : is_valid.val = 1#u8
  · -- =====  Valid y-coordinate: decompression returns `some ep`  =====
    -- Chain step_2_spec
    have ⟨ep, h_step2_eq, ep_Y_eq, ep_Z_eq, ep_X_cond, ep_X_bounds, ep_T_eq, ep_T_bounds⟩ :=
      spec_imp_exists
        (step_2_spec self X Y Z self (self[31]!.val.testBit 7) rfl rfl X_bounds Y_bounds)
    rw [h_step2_eq]
    -- Sign-invariant X² bridge: `(±X).toField² = X.toField²`
    have hX_sq : ep.X.toField ^ 2 = X.toField ^ 2 := by
      rcases hst : self[31]!.val.testBit 7 with _ | _
      · simp only [hst] at ep_X_cond
        rw [ep_X_cond]
      · simp only [hst, ite_true] at ep_X_cond
        rw [ep_X_cond]; ring
    -- Reconstruct `ep.IsValid` from step_1/step_2 postconditions
    have h_isValid : ep.IsValid := by
      refine { Z_ne_zero := ?_, T_relation := ?_, on_curve := ?_,
               X_bounds := ?_, Y_bounds := ?_, Z_bounds := ?_, T_bounds := ?_ }
      · rw [ep_Z_eq, hZ_toField]; exact one_ne_zero
      · -- `T = X·Y` (step_2) and `Z = 1` give `X·Y = T·Z`
        rw [ep_Y_eq, ep_T_eq, ep_Z_eq, hZ_toField, mul_one]
      · -- Curve equation: rewrite to affine form (Z = 1), equate X² via sign symmetry
        rw [ep_Y_eq, ep_Z_eq, hZ_toField]
        dsimp only  -- β-reduce OnCurve.on_curve's `let` bindings
        rw [hX_sq]
        linear_combination flag_curve h_flag
      · intro i hi; exact Nat.lt_of_le_of_lt (ep_X_bounds i hi) (by decide)
      · intro i hi; rw [ep_Y_eq]; exact Nat.lt_of_lt_of_le (Y_bounds i hi) (by decide)
      · intro i hi; rw [ep_Z_eq]; exact Nat.lt_of_lt_of_le (Z_bounds i hi) (by decide)
      · intro i hi; exact Nat.lt_of_lt_of_le (ep_T_bounds i hi) (by decide)
    -- Reduce the WP: unfold Choice→Bool, collapse binds, take the `b = true` branch
    unfold Bool.Insts.CoreConvertFromChoice.from
    simp only [spec, theta, h_flag]
    refine ⟨?isSome_iff, ?on_some⟩
    case isSome_iff =>
      -- `result.isSome = true ↔ ∃ pt : Point Ed25519, pt.y = y`
      refine ⟨?_, fun _ => Option.isSome_some⟩
      intro _
      obtain ⟨x', hx'⟩ := flag_iff.mp h_flag
      exact ⟨⟨x', Y.toField, hx'⟩, hY_toField⟩
    case on_some =>
      intro ep' h_eq
      rw [Option.some.injEq] at h_eq; subst h_eq
      refine ⟨h_isValid, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ep_Y_eq]; exact hY_toField                 -- ep.Y.toField = y
      · rw [ep_Y_eq]; exact Y_mod                      -- Field51_as_Nat ep.Y ≡ ... [MOD p]
      · rw [ep_Z_eq]; exact hZ_toField                 -- ep.Z.toField = 1
      · rw [ep_Z_eq, Z_val]; unfold p; decide          -- Field51_as_Nat ep.Z % p = 1
      · -- Sign-bit ↔ parity (non-degenerate: y² ≠ 1)
        intro h_ysq_ne_1
        rcases hst : self[31]!.val.testBit 7 with _ | _
        · -- sign_bit = false: ep.X = X, so parity = 0 (from step_1 post 6)
          simp only [hst] at ep_X_cond
          rw [ep_X_cond, X_parity]; simp
        · -- sign_bit = true: ep.X.toField = -X.toField; derive parity flip 0 → 1
          simp only [hst, ite_true] at ep_X_cond
          -- Step a: y² ≠ 1 ⇒ X.toField ≠ 0 (via curve eq with x = 0 forces y² = 1)
          have hX_ne_0 : X.toField ≠ 0 := by
            intro h0
            apply h_ysq_ne_1
            have h_curve := flag_curve h_flag
            rw [h0] at h_curve
            simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero,
              zero_add, zero_mul, add_zero] at h_curve
            rw [← hY_toField]; exact h_curve
          have hX_cf_ne_0 : (Field51_as_Nat X : CurveField) ≠ 0 := by
            rwa [FieldElement51.toField] at hX_ne_0
          have hXmod_ne_0 : Field51_as_Nat X % p ≠ 0 := by
            intro h
            apply hX_cf_ne_0
            rw [ZMod.natCast_eq_zero_iff]
            exact Nat.dvd_of_mod_eq_zero h
          -- Step b: lift ep.X.toField = -X.toField to a Nat equality via ZMod.val
          have h_epX_cf :
              (Field51_as_Nat ep.X : CurveField) = -(Field51_as_Nat X : CurveField) := by
            simp only [FieldElement51.toField] at ep_X_cond; exact ep_X_cond
          have h_val_eq :
              (Field51_as_Nat ep.X : ZMod p).val = (-(Field51_as_Nat X : ZMod p)).val :=
            congrArg ZMod.val h_epX_cf
          rw [ZMod.val_natCast] at h_val_eq
          haveI : NeZero ((Field51_as_Nat X : ℕ) : ZMod p) := ⟨hX_cf_ne_0⟩
          rw [ZMod.val_neg_of_ne_zero, ZMod.val_natCast] at h_val_eq
          -- h_val_eq : Field51_as_Nat ep.X % p = p - Field51_as_Nat X % p
          -- Step c: (p - even) % 2 = 1 when p is odd (p = 2^255 − 19 is odd)
          have h_parity : (p - Field51_as_Nat X % p) % 2 = 1 := by
            have hle : Field51_as_Nat X % p ≤ p :=
              Nat.le_of_lt (Nat.mod_lt _ (by unfold p; decide))
            have hp_odd : Odd p := Nat.odd_iff.mpr (by unfold p; decide)
            have hXmod_even : Even (Field51_as_Nat X % p) := Nat.even_iff.mpr X_parity
            exact Nat.odd_iff.mp (Nat.Odd.sub_even hle hp_odd hXmod_even)
          rw [h_val_eq, h_parity]; simp
  · -- =====  Invalid y-coordinate: decompression returns `none`  =====
    unfold Bool.Insts.CoreConvertFromChoice.from
    simp only [spec, theta, h_flag]
    refine ⟨?isSome_iff, ?on_some⟩
    case isSome_iff =>
      refine ⟨fun h => by simp at h, ?_⟩
      -- Backward: ∃ pt with pt.y = y would give a curve-x for y via flag_iff,
      -- contradicting h_flag
      intro ⟨pt, hpt⟩
      exfalso
      apply h_flag
      have hyy : pt.y = Y.toField := hpt.trans hY_toField.symm
      exact flag_iff.mpr ⟨pt.x, hyy ▸ pt.on_curve⟩
    case on_some =>
      intro _ h_eq; exact absurd h_eq (by simp)

end curve25519_dalek.edwards.CompressedEdwardsY
