import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000 -- scalr_tac exceeds standard heartbeats rates
set_option exponentiation.threshold 500

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option linter.hashCommand false
#setup_aeneas_simps

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `mul_internal` -/

/-- **Spec for `backend.serial.u64.scalar.Scalar52.mul_internal`**:
- The result represents the product of the two input field elements
- Requires that each input limb is at most 62 bits to prevent overflow -/
@[progress]
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    mul_internal a b ⦃ (result : Array U128 9#usize) =>
      Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b ∧
      (∀ i < 9, result[i]!.val < 2 ^ 127) ⦄ := by
  unfold mul_internal
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  progress*
  constructor
  · clear * - result_post z8_post z7_post z6_post z5_post z4_post z3_post z2_post z1_post i2_post i_post i1_post i7_post i4_post i3_post i6_post i5_post i14_post i11_post i9_post i8_post i10_post i13_post i12_post i23_post i20_post i18_post i16_post i15_post i17_post i19_post i22_post i21_post i34_post i31_post i29_post i27_post i25_post i24_post i26_post i28_post i30_post i33_post i32_post i41_post i39_post i37_post i35_post i36_post i38_post i40_post i46_post i44_post i42_post i43_post i45_post i49_post i47_post i48_post i50_post
    simp [*, Scalar52_wide_as_Nat, Scalar52_as_Nat, Finset.sum_range_succ]
    ring
  · intro i hi
    have := ha 0 (by simp); have := hb 0 (by simp)
    have := ha 1 (by simp); have := hb 1 (by simp)
    have := ha 2 (by simp); have := hb 2 (by simp)
    have := ha 3 (by simp); have := hb 3 (by simp)
    have := ha 4 (by simp); have := hb 4 (by simp)

    -- Extract bounds once, in structured form
    -- have ha' : ∀ i : Fin 5, a[i]!.val < 2 ^ 62 := by
    --   intro i; exact ha i i.isLt

    -- have hb' : ∀ i : Fin 5, b[i]!.val < 2 ^ 62 := by
    --   intro i; exact hb i i.isLt

    -- Case analysis over result limbs
    -- fin_cases i <;>
    --   simp [result_post,
    --         z1_post, z2_post, z3_post, z4_post,
    --         z5_post, z6_post, z7_post, z8_post] <;>
    --   try
    --     -- arithmetic discharge
    --     linarith

    interval_cases i
    · simp only [Array.getElem!_Nat_eq, Array.set_val_eq, Array.repeat_val, UScalar.ofNatCore_val_eq, Nat.not_eq, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, OfNat.zero_ne_ofNat, not_lt_zero, Nat.ofNat_pos, or_true, or_self,
    ↓List.getElem!_set_ne, one_ne_zero, zero_ne_one, zero_lt_one, List.length_replicate, List.getElem!_set, gt_iff_lt,
    result_post, z8_post, z7_post, z6_post, z5_post, z4_post, z3_post, z2_post, z1_post, hi, i2_post, i_post, i1_post];
      grind =>
        instantiate only [=_ Array.getElem!_Nat_eq]
        instantiate approx
        lia
    all_goals simp [*]; grind =>
        instantiate only [=_ Array.getElem!_Nat_eq]
        instantiate approx
        lia

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
