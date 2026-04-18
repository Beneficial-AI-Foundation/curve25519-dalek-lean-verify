/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Specs.Window.LookupTable.From
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Identity
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.ProjectiveNielsPoint.Neg
import Curve25519Dalek.ExternallyVerified
import Mathlib

/-! # Spec Theorem for `LookupTable<ProjectiveNielsPoint>::select`

Specification for `LookupTable::select`, specialised to `ProjectiveNielsPoint`.

Given a valid precomputed table `[P, 2P, ..., 8P]` (in `ProjectiveNielsPoint` form)
and a signed nibble `x ∈ [-8, 8]`, `select` returns (a representation of) `x • P`
in constant time. The body computes `|x|` via a sign-mask trick and then:

1. `t = identity` (= `0·P`);
2. for `j ∈ {1,...,8}`, conditionally copies `table[j-1]` onto `t` when `|x| = j`;
3. conditionally negates `t` when `x < 0`.

**Source**: curve25519-dalek/src/window.rs, lines 55-78 (inside `impl_lookup_table!` macro).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Edwards curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.edwards

namespace curve25519_dalek
namespace window.LookupTable

/-
natural language description:

• Input: a `LookupTable<ProjectiveNielsPoint>` that encodes `[1•P, 2•P, ..., 8•P]`
  for some base EdwardsPoint `P`, and a signed 8-bit integer `x` with `-8 ≤ x ≤ 8`.

• Computes the projective-Niels representation of `x • P` in constant time:
  1. Let `xmask = x >> 7` (0 if `x ≥ 0`, −1 if `x < 0`; arithmetic shift).
  2. Let `xabs = (x + xmask) XOR xmask = |x|`.
  3. Initialise `t = identity` (0•P).
  4. For `j ∈ {1, ..., 8}`, conditionally copy `table[j-1]` onto `t` when `|x| = j`.
     After the loop, `t = |x| • P` (or identity if `|x| = 0`).
  5. Let `neg_mask = xmask & 1` (= 1 iff `x < 0`).
  6. Conditionally replace `t` with `-t` if `neg_mask = 1`, producing `x • P`.

natural language specs:

• The function always succeeds (no panic) given `-8 ≤ x ≤ 8`.
• The result is a valid `ProjectiveNielsPoint`.
• The result represents `(x.val : ℤ) • P.toPoint` on Ed25519.
-/

/-! ## Helper: Inhabited instance (reuse) -/

-- `Inhabited ProjectiveNielsPoint` is already provided in `Window/LookupTable/From.lean`.

/-! ## Helpers: I16 arithmetic operations for the sign-mask trick -/

/-- Arithmetic shift right of an I16 by 7 bits.
For `i ∈ [-8, 8]`, the result is `-1` if `i < 0` and `0` otherwise.
This is the `xmask = x >> 7` step in `select`. Modelled on
`isize_shiftRight_4_spec` in `Specs/Scalar/Scalar/AsRadix16.lean`. -/
@[step]
private theorem i16_shiftRight_7_spec (i : Std.I16)
    (h_lo : -8 ≤ i.val) (h_hi : i.val ≤ 8) :
    i >>> 7#i32 ⦃ r =>
      r.val = i.val / 128 ∧
      (r.val = -1 ∨ r.val = 0) ∧
      (r.val = -1 ↔ i.val < 0) ⦄ := by
  simp only [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar,
             IScalar.shiftRight, IScalar.toNat, IScalar.val]
  norm_num
  have h7_eq : (7#IScalarTy.I32.numBits).toInt.toNat = 7 := by decide
  simp only [h7_eq]
  have hmatch : i.val >>> (7 : Nat) = i.val / 128 := by
    rw [Int.shiftRight_eq_div_pow]; norm_num
  have h_val_eq : (i.bv.sshiftRight 7).toInt = i.val / 128 := by
    rw [BitVec.sshiftRight_eq]
    rw [BitVec.toInt_ofInt]
    rw [I16.bv_toInt_eq]
    rw [hmatch]
    exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 15 (i.val / 128)
      (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · change (i.bv.sshiftRight 7).toInt = i.val / 128
    exact h_val_eq
  · change (i.bv.sshiftRight 7).toInt = -1 ∨ (i.bv.sshiftRight 7).toInt = 0
    rw [h_val_eq]
    rcases lt_or_ge i.val 0 with hneg | hnn
    · left; omega
    · right; omega
  · change (i.bv.sshiftRight 7).toInt = -1 ↔ i.val < 0
    rw [h_val_eq]
    omega

/-! ## Spec for `LookupTable<ProjectiveNielsPoint>::select` -/

/-- **Spec and proof concerning `window.LookupTable<ProjectiveNielsPoint>::select`**:
- No panic (always returns successfully) on inputs with `-8 ≤ x ≤ 8`.
- The returned `ProjectiveNielsPoint` is valid.
- It represents `(x.val : ℤ) • P.toPoint`, where `P` is the EdwardsPoint used to
  construct the table (so `table[k].toPoint = (k+1) • P.toPoint` for `k ∈ Fin 8`).

This follows the Rust semantics literally:
`selected.toPoint = (sign of x) • (|x| • P) = x • P`. -/
@[step]
theorem select_spec {P : EdwardsPoint}
    (table : window.LookupTable ProjectiveNielsPoint)
    (h_table_valid : ∀ (k : Fin 8), table.val[k].IsValid)
    (h_table_point : ∀ (k : Fin 8),
        table.val[k].toPoint = ((k.val + 1 : ℕ) : ℤ) • P.toPoint)
    (x : Std.I8)
    (h_bounds_lo : -8 ≤ x.val) (h_bounds_hi : x.val ≤ 8) :
    window.LookupTable.select
        ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity
        ProjectiveNielsPoint.Insts.SubtleConditionallySelectable
        ProjectiveNielsPoint.Insts.CoreMarkerCopy
        ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint
        table x ⦃ (selected : ProjectiveNielsPoint) =>
      selected.IsValid ∧
      selected.toPoint = (x.val : ℤ) • P.toPoint ⦄ := by
  unfold select
  simp only [step_simps]
  let* ⟨ hx ⟩ ← massert_spec
  let* ⟨ i, i_post ⟩ ← IScalar.cast.step_spec
  let* ⟨ _ ⟩ ← massert_spec
  · simp only [i_post, IScalar.le_equiv, IScalarTy.I8_numBits_eq, IScalarTy.I16_numBits_eq,
    Nat.reduceLeDiff, IScalar.val_mod_pow_greater_numBits]; agrind
  let* ⟨ i1, i1_post ⟩ ← IScalar.cast.step_spec
  -- Bridge: casting I8 → I16 preserves val.
  have hi1_val : i1.val = x.val := by
    simp only [i1_post, IScalarTy.I8_numBits_eq, IScalarTy.I16_numBits_eq,
      Nat.reduceLeDiff, IScalar.val_mod_pow_greater_numBits]
  let* ⟨ xmask, xmask_post1, xmask_post2, xmask_post3 ⟩ ← i16_shiftRight_7_spec
  let* ⟨ i2, i2_post ⟩ ← IScalar.cast.step_spec
  let* ⟨ i3, i3_post ⟩ ← I16.add_spec
  let* ⟨ xabs, xabs_post1, xabs_post2 ⟩ ← IScalar.xor_spec
  let* ⟨ t, t_post1, t_post2, t_post3, t_post4 ⟩ ←
    ProjectiveNielsPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec
  -- Bridge: i2 is also a cast, same as i and i1.
  have hi2_val : i2.val = x.val := by
    simp only [i2_post, IScalarTy.I8_numBits_eq, IScalarTy.I16_numBits_eq,
      Nat.reduceLeDiff, IScalar.val_mod_pow_greater_numBits]
  -- xabs.val = |x.val|: sign-mask trick `(x + xmask) XOR xmask = |x|`.
  -- Proof by case split on xmask.val ∈ {0, -1}. BitVec-level XOR identities
  -- are reduced via `BitVec.eq_of_toInt_eq` (no bv_decide needed).
  have hi3_val : i3.val = x.val + xmask.val := by rw [i3_post, hi2_val]
  have hxabs_val : xabs.val = x.val.natAbs := by
    have hxabs_bv_toInt : xabs.val = (i3.bv ^^^ xmask.bv).toInt := by
      change xabs.bv.toInt = _; fcongr 1
    rw [hxabs_bv_toInt]
    rcases xmask_post2 with hm | hm
    · -- xmask.val = -1, so x.val < 0, and xmask.bv = allOnes 16.
      have hx_neg : x.val < 0 := by rw [← hi1_val]; exact xmask_post3.mp hm
      have hxm_bv : xmask.bv = BitVec.allOnes 16 := by
        apply BitVec.eq_of_toInt_eq
        rw [BitVec.toInt_allOnes]
        change xmask.val = _
        rw [hm]; decide
      rw [hxm_bv, BitVec.xor_allOnes, BitVec.toInt_not]
      -- Goal: (↑(2^16 - 1 - i3.bv.toNat) : ℤ).bmod (2^16) = ↑x.val.natAbs.
      -- Bounds: i3.val = x.val - 1 ∈ [-9, -2].
      have hi3_toInt : i3.bv.toInt = x.val - 1 := by
        change i3.val = _; rw [hi3_val, hm]; ring
      have hi3_neg : i3.bv.toInt < 0 := by rw [hi3_toInt]; omega
      have hcond := BitVec.toInt_eq_toNat_cond i3.bv
      rw [hi3_toInt] at hcond
      split_ifs at hcond with hlt
      · exfalso; omega
      -- hcond : x.val - 1 = ↑i3.bv.toNat - 2^16
      have hi3_toNat : (i3.bv.toNat : ℤ) = x.val + (2^16 - 1) := by push_cast at hcond ⊢; omega
      have hbm_arg : (2^16 - 1 - (i3.bv.toNat : ℤ) : ℤ) = -x.val := by
        push_cast; omega
      rw [hbm_arg, Int.ofNat_natAbs_of_nonpos (le_of_lt hx_neg)]
      exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 15 (-x.val)
        (by omega) (by omega)
    · -- xmask.val = 0, so x.val ≥ 0, and xmask.bv = 0#16.
      have hx_nn : 0 ≤ x.val := by
        rw [← hi1_val]
        by_contra hneg
        push_neg at hneg
        have := xmask_post3.mpr hneg; omega
      have hxm_bv : xmask.bv = 0#16 := by
        apply BitVec.eq_of_toInt_eq
        change xmask.val = _
        rw [hm]; decide
      rw [hxm_bv, BitVec.xor_zero]
      change i3.val = _
      rw [hi3_val, hm, Int.natAbs_of_nonneg hx_nn]; ring
  sorry
  -- Proof strategy (to be completed; see `.formalising/fv-plans/.continue-here.md`):
  --
  --  1. Unfold `select`. Show the two `massert`s succeed (bounds on x).
  --  2. Identify `xmask.val = if x.val < 0 then -1 else 0` and `xabs.val = |x.val|`
  --     via arithmetic on I16. (`>>> 7` on I16 is arithmetic shift.)
  --  3. Step through `identity`; obtain initial `t` with `t.IsValid ∧ t.toPoint = 0`.
  --  4. Dispatch a `select_loop_spec` with loop invariant
  --       `t.IsValid ∧ t.toPoint = if |x|.val ∈ [1..iter.start.val) then
  --                                  ((|x|.val - 1 : ℕ) + 1 : ℤ) • P.toPoint
  --                                else 0`
  --     which, since the iterator runs `start = 1`, `end = 9`, yields after exit
  --       `t.toPoint = if |x|.val ∈ [1..8] then (|x|.val : ℤ) • P.toPoint else 0`
  --     i.e. `t.toPoint = (|x.val| : ℤ) • P.toPoint` for all `|x.val| ∈ [0..8]`.
  --  5. Compute `neg_mask`: it is `Choice.one` iff `x.val < 0`, else `Choice.zero`.
  --  6. Apply `neg_spec` to get `t_neg.IsValid ∧ t_neg.toPoint = -t.toPoint`.
  --  7. Apply a point-level `conditional_assign_spec` to combine: result matches
  --     `t` or `t_neg` depending on `neg_mask`, then push `toPoint` through.
  --  8. Conclude `selected.toPoint = sign(x) · |x| · P.toPoint = x.val • P.toPoint`
  --     via `Int.sign_mul_natAbs` / `zsmul` identities.


end window.LookupTable
end curve25519_dalek
