/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.ElligatorEncode
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.Aplus2OverFour

/-!
# Spec theorem for `curve25519_dalek::montgomery::differential_add_and_double`

Performs the core step of the Montgomery ladder: simultaneous projective point doubling and
differential addition. Given projective points P and Q on the Montgomery curve, plus the
u-coordinate of P-Q, computes [2]P and P+Q simultaneously using formulas from
Costello-Smith 2017. Arithmetic is performed in 𝔽_p where p = 2^255 - 19. The addition
is 'differential' because it uses P-Q to efficiently compute P+Q.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
open backend.serial.u64.field.FieldElement51
open Montgomery
open backend.serial.u64.constants
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.montgomery
open curve25519_dalek.field.FieldElement51
namespace curve25519_dalek.montgomery

/-- A projective point is valid if its W coordinate is non-zero,
    meaning it represents a finite affine point u = U/W. -/
@[mk_iff]
structure ProjectivePoint.IsValid (P : ProjectivePoint) : Prop where
  /-- All coordinate limbs are bounded by 2^52. -/
  U_bounds : ∀ i < 5, P.U[i]!.val < 2 ^ 53
  W_bounds : ∀ i < 5, P.W[i]!.val < 2 ^ 53
  /-- The Z coordinate is non-zero. -/
  W_ne_zero : P.W.toField ≠ 0
  /-- The curve equation (cleared denominators). -/
  on_curve :
    let U := P.U.toField; let W := P.W.toField; let u := U / W
    IsSquare (u ^ 3 + Curve25519.A * u ^ 2 + u)

lemma not_eq_T_point (P : ProjectivePoint)
    (P_affine : FieldElement51)
    (hP_valid : P.IsValid)
    (P_a : P_affine.toField = P.U.toField / P.W.toField)
    (non_eq_T : P_affine.toField ≠ 0) :
    P.U.toField ≠ 0 := by
  intro h
  apply non_eq_T
  rw [P_a]
  have := hP_valid.W_ne_zero
  field_simp
  ring_nf
  exact h

/-- A valid Montgomery ladder state: P and Q are projective points, and affine_PmQ
    contains the u-coordinate of the difference (P-Q).

    This captures the invariant maintained by the Montgomery ladder algorithm:
    - The two points P and Q are distinct (P ≠ Q)
    - The difference between them is always known and non-zero
    - This allows the differential addition formula to work correctly
      (the formula requires P ≠ Q to avoid division by zero in (u_P - u_Q))
-/
def valid_ladder_state
    (P Q : ProjectivePoint)
    (affine_PmQ : FieldElement51) : Prop :=
  ∃ (P_affine Q_affine : FieldElement51),
    P_affine.toField ≠ 0 ∧ Q_affine.toField ≠ 0 ∧
    P_affine.toField ≠ Q_affine.toField ∧
    P_affine.toField = P.U.toField / P.W.toField ∧
    Q_affine.toField = Q.U.toField / Q.W.toField ∧
    (∀ i < 5, affine_PmQ[i]!.val < 2 ^ 52) ∧
    affine_PmQ.toField ≠ 0 ∧
    (∀ (P_affine Q_affine : Point),
    get_u P_affine = P.U.toField / P.W.toField ∧
    get_u Q_affine = Q.U.toField / Q.W.toField →
    get_u (P_affine - Q_affine) = affine_PmQ.toField)

set_option maxHeartbeats 400000 in -- heavy simp
/-- **Spec theorem for `curve25519_dalek::montgomery::differential_add_and_double`**
• The function always succeeds (no panic) for valid inputs satisfying the ladder state invariant
• Both output projective points are valid (`W ≠ 0`)
• For any Montgomery points consistent with the projective inputs and `affine_PmQ`, the
  u-coordinate of the first output equals that of [2]P and the second equals that of P+Q
• The projective inputs are realised by some pair of Montgomery curve points
-/
@[step]
theorem differential_add_and_double_spec
    (P Q : ProjectivePoint)
    (affine_PmQ : FieldElement51)
    (hP_valid : P.IsValid)
    (hQ_valid : Q.IsValid)
    (h_ladder_state : valid_ladder_state P Q affine_PmQ) :
    differential_add_and_double P Q affine_PmQ ⦃ (result : ProjectivePoint × ProjectivePoint) =>
      result.1.IsValid ∧
      result.2.IsValid ∧
      (∀ (P_affine Q_affine : Point),
        (get_u P_affine = Field51_as_Nat P.U / Field51_as_Nat P.W ∧
         get_u Q_affine = Field51_as_Nat Q.U / Field51_as_Nat Q.W ∧
         get_u (P_affine - Q_affine) = Field51_as_Nat affine_PmQ) →
        (Field51_as_Nat result.1.U / Field51_as_Nat result.1.W =
          get_u (2 • P_affine)) ∧
        (Field51_as_Nat result.2.U / Field51_as_Nat result.2.W =
          get_u (P_affine + Q_affine))) ∧
      (∃ (P_affine Q_affine : Point),
        (get_u P_affine = Field51_as_Nat P.U / Field51_as_Nat P.W ∧
         get_u Q_affine = Field51_as_Nat Q.U / Field51_as_Nat Q.W ∧
         get_u (P_affine - Q_affine) = Field51_as_Nat affine_PmQ) )
      ⦄ := by
  unfold differential_add_and_double
  obtain ⟨P_affine, Q_affine, hnon_p, hnon_q, hp_neq_q, hp_a, hq_a,
    hpmq_lt, hnon_pmq, heq_pmq⟩ := h_ladder_state
  step*
  · exact hP_valid.U_bounds
  · exact hP_valid.W_bounds
  · have := hQ_valid.U_bounds
    grind
  · have := hQ_valid.W_bounds
    grind
  · rw [lift_mod_eq_iff] at t16_post1
    rw [lift_mod_eq_iff] at t5_post1
    rw [lift_mod_eq_iff] at t4_post1
    rw [lift_mod_eq_iff] at t7_post1
    rw [lift_mod_eq_iff] at t8_post1
    rw [lift_mod_eq_iff] at t11_post1
    rw [lift_mod_eq_iff] at t13_post1
    rw [lift_mod_eq_iff] at t14_post1
    rw [lift_mod_eq_iff] at t17_post1
    rw [lift_mod_eq_iff] at t12_post1
    rw [← Nat.ModEq, lift_mod_eq_iff] at t6_post2
    rw [← Nat.ModEq, lift_mod_eq_iff] at t1_post2
    rw [← Nat.ModEq, lift_mod_eq_iff] at t3_post2
    rw [← Nat.ModEq, lift_mod_eq_iff] at t10_post2
    have ht6 : ((Field51_as_Nat t6) : CurveField) =
        ↑(Field51_as_Nat t0 ^ 2) - ↑(Field51_as_Nat t1 ^ 2) := by
      clear *- t6_post2 t5_post1 t4_post1
      grind => ring
    have ht1 : ((Field51_as_Nat t1) : CurveField) =
        ↑(Field51_as_Nat P.U) - ↑(Field51_as_Nat P.W) := by
      clear *- t1_post2
      grind only
    have ht0 : ((Field51_as_Nat t0) : CurveField) =
        Field51_as_Nat P.U + Field51_as_Nat P.W := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
        Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
        List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
        Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      clear *- t0_post1
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
        UScalar.ofNatCore_val_eq, getElem!_pos, Nat.ofNat_pos,
        Nat.cast_add, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      ring_nf
    have ht2 : ((Field51_as_Nat t2) : CurveField) =
        Field51_as_Nat Q.U + Field51_as_Nat Q.W := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
        Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
        List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
        Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      clear *- t2_post1
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
        UScalar.ofNatCore_val_eq, getElem!_pos, Nat.ofNat_pos,
        Nat.cast_add, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      ring_nf
    have ht3 : ((Field51_as_Nat t3) : CurveField) =
        Field51_as_Nat Q.U - Field51_as_Nat Q.W := by
      grind only
    have ht9 : ((Field51_as_Nat t9) : CurveField) =
        Field51_as_Nat t7 + Field51_as_Nat t8 := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
        Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
        List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
        Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      clear *- t9_post1
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
        UScalar.ofNatCore_val_eq, getElem!_pos, Nat.ofNat_pos,
        Nat.cast_add, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      ring_nf
    have ht15 : ((Field51_as_Nat t15) : CurveField) =
        Field51_as_Nat t13 + Field51_as_Nat t5 := by
      simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
        Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero,
        List.Vector.length_val, UScalar.ofNatCore_val_eq, Nat.ofNat_pos, getElem?_pos,
        Option.getD_some, one_mul, mul_one, Nat.reducePow, Nat.one_lt_ofNat, Nat.reduceMul,
        Nat.reduceLT, Nat.lt_add_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      clear *- t15_post1
      simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val,
        UScalar.ofNatCore_val_eq, getElem!_pos, Nat.ofNat_pos,
        Nat.cast_add, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one]
      ring_nf
    have ht10_eq : ((Field51_as_Nat t10) : CurveField) =
        ↑(Field51_as_Nat t7) - (Field51_as_Nat t8) := by grind
    have non_t6 : Field51_as_Nat t6 ≠ (0 : CurveField) := by
      simp only [Nat.cast_pow, ht6,
        (by grind : ∀ a b : CurveField, a ^ 2 - b ^ 2 = (a - b) * (a + b)),
        ne_eq, mul_eq_zero, not_or]
      constructor
      · simp only [ht0, ht1, add_sub_sub_cancel,
          (by grind : ∀ a : CurveField, a + a = 2 * a), mul_eq_zero, not_or]
        have := hP_valid.W_ne_zero
        unfold FieldElement51.toField at this
        simp only [this, not_false_eq_true, and_true, ne_eq]
        decide
      · simp only [ht0, ht1, add_add_sub_cancel,
          (by grind : ∀ a : CurveField, a + a = 2 * a), mul_eq_zero, not_or]
        constructor
        · decide
        · apply not_eq_T_point
          · exact hP_valid
          · exact hp_a
          · exact hnon_p
    have non_W := hP_valid.W_ne_zero
    unfold FieldElement51.toField at non_W
    have nonQ_W := hQ_valid.W_ne_zero
    unfold FieldElement51.toField at nonQ_W
    have non_t16 : (Field51_as_Nat t16) ≠ (0 : CurveField) := by
      simp only [t16_post1, Nat.cast_mul, ne_eq, mul_eq_zero, non_t6, false_or]
      simp only [ht15, t13_post1, Nat.cast_mul, ht6, Nat.cast_pow, ht0, ht1, t5_post1]
      set U := Field51_as_Nat P.U with HU
      set W := Field51_as_Nat P.W with HW
      have : Field51_as_Nat fe = (Curve25519.A + 2) / 4 := by
        rw [fe_post1]
        decide
      rw [this]
      have : (4 : CurveField) ≠ 0 := by decide
      have : (U + W) ^ 2 - (U - W) ^ 2 = (4 * U * W : CurveField) := by ring_nf
      rw [this]
      have : (4 : CurveField) ≠ 0 := by decide
      field_simp
      have : (Curve25519.A + 2) * ↑U * ↑W + (↑U - ↑W) ^ 2
        = ↑U * (↑U + ↑W * Curve25519.A) + ↑W ^ 2 := by grind
      rw [this]
      have := quadratic_ne_zero (U / W)
      field_simp at this
      simp only [mul_zero] at this
      exact this
    have non_t17 : (Field51_as_Nat t17) ≠ (0 : CurveField) := by
      intro h
      simp only [t17_post1, Nat.cast_mul, t12_post1, Nat.cast_pow, ht10_eq,
        mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff] at h
      rcases h with h | h
      · unfold FieldElement51.toField at hnon_pmq
        grind
      · simp only [t7_post1, Nat.cast_mul, ht0, ht3, t8_post1, ht1, ht2] at h
        ring_nf at h
        field_simp at h
        simp only [mul_eq_zero] at h
        rcases h with h | h
        · revert h
          decide
        · apply hp_neq_q
          simp[hp_a, hq_a]
          have := hP_valid.W_ne_zero
          have := hQ_valid.W_ne_zero
          field_simp
          unfold FieldElement51.toField
          grind
    have DBL_ADD_E : ∀ (P_affine Q_affine : Point),
      get_u P_affine = ↑(Field51_as_Nat P.U) / ↑(Field51_as_Nat P.W) ∧
      get_u Q_affine = ↑(Field51_as_Nat Q.U) / ↑(Field51_as_Nat Q.W) ∧
        get_u (P_affine - Q_affine) = (Field51_as_Nat affine_PmQ) →
      (Field51_as_Nat t14) / ((Field51_as_Nat t16) : CurveField) =
        get_u (2 • P_affine) ∧
      (Field51_as_Nat t11) / ((Field51_as_Nat t17) : CurveField) =
        get_u (P_affine + Q_affine) := by
      intro Pa Qa hpq
      have non_Pa : Pa ≠ 0 := by
        rcases Pa
        · unfold get_u at hpq
          simp only at hpq
          have eq := hpq.left
          unfold FieldElement51.toField at hp_a
          unfold FieldElement51.toField at hnon_p
          rw [← hp_a] at eq
          simp only [eq, ne_eq, not_true_eq_false] at hnon_p
        · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      have non_Qa : Qa ≠ 0 := by
        rcases Qa
        · unfold get_u at hpq
          simp only at hpq
          have eq := hpq.right.left
          unfold FieldElement51.toField at hq_a
          unfold FieldElement51.toField at hnon_q
          rw [← hq_a] at eq
          simp only [eq, ne_eq, not_true_eq_false] at hnon_q
        · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      have Pa_non_T_point : Pa ≠ T_point := by
        rcases Pa
        · simp only [T_point, ne_eq, reduceCtorEq, not_false_eq_true]
        · simp only [T_point, ne_eq, WeierstrassCurve.Affine.Point.some.injEq, not_and]
          rename_i x y nonP
          unfold get_u at hpq
          simp only at hpq
          have eq := hpq.left
          intro hx
          unfold FieldElement51.toField at hp_a
          unfold FieldElement51.toField at hnon_p
          rw [← hp_a] at eq
          simp only [eq] at hx
          simp only [hx, ne_eq, not_true_eq_false] at hnon_p
      have Qa_non_T_point : Qa ≠ T_point := by
        rcases Qa
        · simp only [T_point, ne_eq, reduceCtorEq, not_false_eq_true]
        · simp only [T_point, ne_eq, WeierstrassCurve.Affine.Point.some.injEq, not_and]
          rename_i x y nonP
          unfold get_u at hpq
          simp only at hpq
          have eq := hpq.right.left
          intro hx
          unfold FieldElement51.toField at hq_a
          unfold FieldElement51.toField at hnon_q
          rw [← hq_a] at eq
          simp only [eq] at hx
          simp only [hx, ne_eq, not_true_eq_false] at hnon_q
      constructor
      · have DBL := uDBL Pa non_Pa Pa_non_T_point
        simp only [hpq] at DBL
        field_simp at DBL
        field_simp
        simp only [t14_post1, Nat.cast_mul, t4_post1, Nat.cast_pow,
          t5_post1, ht1, t16_post1, ht6]
        simp only [ht0, ht15, t13_post1, Nat.cast_mul, ht6, Nat.cast_pow, ht1, t5_post1]
        field_simp
        have : Field51_as_Nat fe = (Curve25519.A + 2) / 4 := by
          rw [fe_post1]
          decide
        rw [this]
        clear *- DBL
        set U := Field51_as_Nat P.U with HU
        set W := Field51_as_Nat P.W with HW
        have : (4 : CurveField) ≠ 0 := by decide
        field_simp
        grind
      · have non_eq_pq : Pa ≠ Qa := by
          intro h
          rw [h] at hpq
          have eq := hpq.right.left
          rw [hpq.left] at eq
          apply hp_neq_q
          rw [hp_a, hq_a]
          unfold FieldElement51.toField
          rw [eq]
        have non_eq_pq_neg : Pa ≠ -Qa := by
          intro h
          rw [h, neg_u_coord] at hpq
          have eq := hpq.right.left
          rw [hpq.left] at eq
          apply hp_neq_q
          rw [hp_a, hq_a]
          unfold FieldElement51.toField
          rw [eq]
        have ADD := uADD Pa Qa non_Pa non_Qa
          Pa_non_T_point Qa_non_T_point non_eq_pq non_eq_pq_neg
        simp only [hpq] at ADD
        field_simp at ADD
        field_simp
        simp [t11_post1, ht9, t7_post1, ht0, t8_post1, ht3, ht1, ht2,
          t17_post1, t12_post1, ht10_eq]
        field_simp
        clear *- ADD
        set PU := Field51_as_Nat P.U with HPU
        set PW := Field51_as_Nat P.W with HPW
        set QU := Field51_as_Nat Q.U with HQU
        set QW := Field51_as_Nat Q.W with HQW
        grind => ring
    have eqP := hP_valid.on_curve
    simp only [IsSquare, (by grind : ∀ r : CurveField, r * r = r ^ 2)] at eqP
    obtain ⟨ vP, hvP⟩ := eqP
    have eqQ := hQ_valid.on_curve
    simp only [IsSquare, (by grind : ∀ r : CurveField, r * r = r ^ 2)] at eqQ
    obtain ⟨ vQ, hvQ⟩ := eqQ
    have get_u_Q := get_u_mk_point hvQ.symm
    have get_u_P := get_u_mk_point hvP.symm
    have P_neq_zero := mk_point_neq_zero hvP.symm
    have Q_neq_zero := mk_point_neq_zero hvQ.symm
    have uP_neq_zero : P.U.toField / P.W.toField ≠ 0 := by
      rw [← hp_a]
      exact hnon_p
    have P_neq_T := mk_point_neq_T_of_u uP_neq_zero hvP.symm
    have uQ_neq_zero : Q.U.toField / Q.W.toField ≠ 0 := by
      rw [← hq_a]
      exact hnon_q
    have Q_neq_T := mk_point_neq_T_of_u uQ_neq_zero hvQ.symm
    have uP_neq_uQ : P.U.toField / P.W.toField ≠ Q.U.toField / Q.W.toField := by
      rw [← hp_a, ← hq_a]
      exact hp_neq_q
    have P_neqQ := mk_point_neq uP_neq_uQ hvP.symm hvQ.symm
    have P_neqQ_neg := mk_point_neq_neg uP_neq_uQ hvP.symm hvQ.symm
    set Q_a := mk_point hvQ.symm with hQ_affine
    set P_a := mk_point hvP.symm with hP_affine
    have heq_pmq := heq_pmq P_a Q_a
    simp only [get_u_P, get_u_Q, and_self, forall_const] at heq_pmq
    unfold FieldElement51.toField at heq_pmq
    have DBL_ADD := DBL_ADD_E P_a Q_a
    simp only [get_u_P, get_u_Q, heq_pmq, and_true, and_imp] at DBL_ADD
    unfold FieldElement51.toField at DBL_ADD
    simp only [forall_const] at DBL_ADD
    have DBL_neq_0 := DBL_neq_zero P_a P_neq_zero P_neq_T
    have ADD_neq_0 : P_a + Q_a ≠ 0 := by grind
    constructor
    · constructor
      · grind only [#f2e6]
      · grind only [#b561]
      · simp only [ne_eq]
        unfold FieldElement51.toField
        apply non_t16
      · unfold FieldElement51.toField
        simp only [DBL_ADD]
        have := point_on_curve (2 • P_a) DBL_neq_0
        unfold IsSquare
        use get_v (2 • P_a)
        simp only [← this]
        ring_nf
    · constructor
      · constructor
        · simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow]
          clear *- t11_post2
          intro i hi
          have := t11_post2 i hi
          apply lt_trans this
          simp only [Nat.reducePow, Nat.reduceLT]
        · simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, Nat.reducePow]
          clear *- t17_post2
          intro i hi
          have := t17_post2 i hi
          apply lt_trans this
          simp only [Nat.reducePow, Nat.reduceLT]
        · simp only [ne_eq]
          unfold FieldElement51.toField
          exact non_t17
        · unfold FieldElement51.toField
          simp only [DBL_ADD]
          have := point_on_curve (P_a + Q_a) ADD_neq_0
          unfold IsSquare
          use get_v (P_a + Q_a)
          simp only [← this]
          ring_nf
      · constructor
        · exact DBL_ADD_E
        · use P_a
          use Q_a
          simp only [get_u_P, get_u_Q, heq_pmq, and_true]
          unfold FieldElement51.toField
          simp only [and_self]

end curve25519_dalek.montgomery
