/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add
/-!
# Spec theorem for `ProjectiveNielsPoint::sub`

This function implements the mixed subtraction of a ProjectiveNielsPoint from an
Edwards point in extended coordinates, returning the result in completed
coordinates (ℙ¹ × ℙ¹). Given
- an EdwardsPoint P = (X:Y:Z:T) in extended ℙ³ coordinates (with X/Z = x, Y/Z = y, and T = XY/Z),
- a ProjectiveNielsPoint N = (Y+X, Y−X, Z, 2dXY),
it computes a CompletedPoint C = (X':Y':Z':T') corresponding to P − N.

The concrete formulas are:
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PM        = Y_plus_X  · N.Y_minus_X
- MP        = Y_minus_X · N.Y_plus_X
- TT2d      = T · N.T2d
- ZZ        = Z · N.Z
- ZZ2       = ZZ + ZZ
- X'        = PM − MP
- Y'        = PM + MP
- Z'        = ZZ2 − TT2d
- T'        = ZZ2 + TT2d

Source: "curve25519-dalek/src/backend/serial/curve_models/mod.rs"
-/
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models
open curve25519_dalek.backend.serial.u64.field
open Edwards
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.edwards

/-! ## Independent sub-lemmas for `sub_spec_aux_54_52_53_52`

These lemmas factor out the key proof steps used in the main theorem:
1. `pointwise_add_Field51_as_Nat` (from Aux.lean): converts limb-wise addition to `Field51_as_Nat` sum
2. `sub_X_modular_relation` / `sub_Y_modular_relation` / `sub_Z_modular_relation` / `sub_T_modular_relation`:
   pure modular arithmetic lemmas for each coordinate relation
3. `double_limb_tight_bounds`: derives tight bounds for doubled limb values
-/


/-- X relation for sub: `X' + Y·YpX ≡ (Y+X)·YmX + X·YpX (mod p)`.
    Here X' = PM - MP, PM = (Y+X)·other.Y_minus_X, MP = (Y-X)·other.Y_plus_X.
    Parameters: Y, X are self coords; YpX, YmX are other coords;
    sum_YX = Y+X (limb-wise), diff_YX = Y-X (field sub);
    PM, MP are multiplication results; X' is the subtraction result. -/
private lemma sub_X_modular_relation
    {X Y YpX YmX sum_YX diff_YX PM MP X' : ℕ}
    (h_sum : Y + X = sum_YX)
    (h_diff : Nat.ModEq p (diff_YX + X) Y)
    (h_PM : Nat.ModEq p PM (sum_YX * YmX))
    (h_MP : Nat.ModEq p MP (diff_YX * YpX))
    (h_sub : Nat.ModEq p (X' + MP) PM) :
    Nat.ModEq p (X' + Y * YpX) (((Y + X) * YmX) + X * YpX) := by
  rw [h_sum]
  have h1 := Nat.ModEq.mul_right YpX h_diff
  have h2 := Nat.ModEq.symm (Nat.ModEq.add_left X' h1)
  rw [add_mul, ← add_assoc] at h2
  apply Nat.ModEq.trans h2
  apply Nat.ModEq.add_right
  apply Nat.ModEq.symm
  apply Nat.ModEq.trans (Nat.ModEq.symm h_PM)
  apply Nat.ModEq.trans (Nat.ModEq.symm h_sub)
  apply Nat.ModEq.add_left
  exact h_MP

/-- Y relation for sub: `Y' + X·YpX ≡ (Y+X)·YmX + Y·YpX (mod p)`.
    Here Y' = PM + MP (exact nat sum via limb-wise addition). -/
private lemma sub_Y_modular_relation
    {X Y YpX YmX sum_YX diff_YX PM MP Y' : ℕ}
    (h_sum : Y + X = sum_YX)
    (h_diff : Nat.ModEq p (diff_YX + X) Y)
    (h_PM : Nat.ModEq p PM (sum_YX * YmX))
    (h_MP : Nat.ModEq p MP (diff_YX * YpX))
    (h_add : Y' = PM + MP) :
    Nat.ModEq p (Y' + X * YpX) (((Y + X) * YmX) + Y * YpX) := by
  rw [h_add]
  have h1 := Nat.ModEq.add h_PM h_MP
  have h2 := Nat.ModEq.add_right (X * YpX) h1
  apply Nat.ModEq.trans h2
  rw [h_sum, add_assoc]
  apply Nat.ModEq.add_left
  rw [← add_mul]
  apply Nat.ModEq.mul_right
  exact h_diff

/-- Z relation for sub: `Z' + T·T2d ≡ 2·Z·Z₀ (mod p)`.
    Here Z' = ZZ2 - TT2d (field sub), ZZ2 = 2·ZZ (limb-wise double),
    ZZ ≡ Z·Z₀ (field mul), TT2d ≡ T·T2d (field mul). -/
private lemma sub_Z_modular_relation
    {T Z Z₀ T2d TT2d ZZ ZZ2 Z' : ℕ}
    (h_TT2d : Nat.ModEq p TT2d (T * T2d))
    (h_ZZ : Nat.ModEq p ZZ (Z * Z₀))
    (h_ZZ2 : ZZ2 = ZZ + ZZ)
    (h_sub : Nat.ModEq p (Z' + TT2d) ZZ2) :
    Nat.ModEq p (Z' + (T * T2d)) (2 * Z * Z₀) := by
  have h1 := Nat.ModEq.add_left Z' h_TT2d
  have h2 := Nat.ModEq.trans (Nat.ModEq.symm h1) h_sub
  apply Nat.ModEq.trans h2
  rw [h_ZZ2, show ZZ + ZZ = 2 * ZZ from by omega]
  have h3 := Nat.ModEq.mul_left 2 h_ZZ
  rw [mul_assoc]
  exact h3

/-- T relation for sub: `T' ≡ 2·Z·Z₀ + T·T2d (mod p)`.
    Here T' = ZZ2 + TT2d (exact nat sum via limb-wise addition). -/
private lemma sub_T_modular_relation
    {T Z Z₀ T2d TT2d ZZ ZZ2 T' : ℕ}
    (h_TT2d : Nat.ModEq p TT2d (T * T2d))
    (h_ZZ : Nat.ModEq p ZZ (Z * Z₀))
    (h_ZZ2 : ZZ2 = ZZ + ZZ)
    (h_add : T' = ZZ2 + TT2d) :
    Nat.ModEq p T' ((2 * Z * Z₀) + (T * T2d)) := by
  rw [h_add, h_ZZ2, show ZZ + ZZ = 2 * ZZ from by omega]
  exact Nat.ModEq.trans
    (Nat.ModEq.add_right TT2d (Nat.ModEq.mul_left 2 h_ZZ))
    (by rw [mul_assoc]; exact Nat.ModEq.add_left _ h_TT2d)

/-- Tight bound derivation: if `b[i] = a[i] + a[i]` and `a[i] < 2^52`, then `b[i] < 2^53`. -/
private lemma double_limb_tight_bounds (a b : Array U64 5#usize)
    (h_double : ∀ i, i < 5 → b[i]!.val = a[i]!.val + a[i]!.val)
    (h_bound : ∀ i, i < 5 → a[i]!.val < 2 ^ 52) :
    ∀ i, i < 5 → b[i]!.val < 2 ^ 53 := by
  intro i hi
  have h1 : b[i]!.val = a[i]!.val + a[i]!.val := h_double i hi
  have h2 : a[i]!.val < 2 ^ 52 := h_bound i hi
  calc b[i]!.val = a[i]!.val + a[i]!.val := h1
      _ < 2 ^ 52 + 2 ^ 52 := by omega
      _ = 2 ^ 53 := by norm_num




/-- Auxiliary spec for sub proving arithmetic correctness and output bounds.
Input bounds: EdwardsPoint coords < 2^53, ProjectiveNielsPoint (IsValid') bounds. -/
theorem sub_spec_aux_54_52_53_52
    (self : edwards.EdwardsPoint)
    (other : backend.serial.curve_models.ProjectiveNielsPoint)
    (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
    (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
    (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
    (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
    (h_otherYpX_bounds : ∀ i, i < 5 → (other.Y_plus_X[i]!).val < 2 ^ 54)
    (h_otherYmX_bounds : ∀ i, i < 5 → (other.Y_minus_X[i]!).val < 2 ^ 52)
    (h_otherZ_bounds : ∀ i, i < 5 → (other.Z[i]!).val < 2 ^ 53)
    (h_otherT2d_bounds : ∀ i, i < 5 → (other.T2d[i]!).val < 2 ^ 52) :
    sub self other ⦃ c =>
    let X := Field51_as_Nat self.X
    let Y := Field51_as_Nat self.Y
    let Z := Field51_as_Nat self.Z
    let T := Field51_as_Nat self.T
    let YpX := Field51_as_Nat other.Y_plus_X
    let YmX := Field51_as_Nat other.Y_minus_X
    let Z₀ := Field51_as_Nat other.Z
    let T2d := Field51_as_Nat other.T2d
    let X' := Field51_as_Nat c.X
    let Y' := Field51_as_Nat c.Y
    let Z' := Field51_as_Nat c.Z
    let T' := Field51_as_Nat c.T
    (X' + Y * YpX) % p = (((Y + X) * YmX) + X * YpX) % p ∧
    (Y' + X * YpX) % p = (((Y + X) * YmX) + Y * YpX) % p ∧
    (Z' + (T * T2d)) % p = (2 * Z * Z₀) % p ∧
    T' % p = ((2 * Z * Z₀) + (T * T2d)) % p ∧
    -- Output bounds (all < 2^54)
    (∀ i < 5, c.X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 54) ⦄ := by
  unfold sub
  simp only [step_simps]
  let* ⟨ Y_plus_X, Y_plus_X_post1, Y_plus_X_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
  let* ⟨ Y_minus_X, Y_minus_X_post1, Y_minus_X_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec
  let* ⟨ PM, PM_post1, PM_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ MP, MP_post1, MP_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ TT2d, TT2d_post1, TT2d_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ ZZ, ZZ_post1, ZZ_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul_spec
  let* ⟨ ZZ2, ZZ2_post1, ZZ2_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
  let* ⟨ fe, fe_post1, fe_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec
  let* ⟨ fe1, fe1_post1, fe1_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
  let* ⟨ fe2, fe2_post1, fe2_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub_spec
  let* ⟨ fe3, fe3_post1, fe3_post2 ⟩ ←
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add_spec
  have h_sum_YX := (pointwise_add_Field51_as_Nat self.Y self.X Y_plus_X Y_plus_X_post1).symm
  have h_fe1_nat := pointwise_add_Field51_as_Nat PM MP fe1 fe1_post1
  have h_ZZ2_nat := pointwise_add_Field51_as_Nat ZZ ZZ ZZ2 ZZ2_post1
  have h_fe3_nat := pointwise_add_Field51_as_Nat ZZ2 TT2d fe3 fe3_post1
  exact ⟨
    by rw [← Nat.ModEq]; exact sub_X_modular_relation h_sum_YX Y_minus_X_post2 PM_post1 MP_post1 fe_post2,
    by rw [← Nat.ModEq]; exact sub_Y_modular_relation h_sum_YX Y_minus_X_post2 PM_post1 MP_post1 h_fe1_nat,
    by rw [← Nat.ModEq]; exact sub_Z_modular_relation TT2d_post1 ZZ_post1 h_ZZ2_nat fe2_post2,
    by rw [← Nat.ModEq]; exact sub_T_modular_relation TT2d_post1 ZZ_post1 h_ZZ2_nat h_fe3_nat,
    fun i hi => lt_trans (fe_post1 i hi) (by norm_num),
    fe1_post2,
    fun i hi => lt_trans (fe2_post1 i hi) (by norm_num),
    fe3_post2⟩

theorem sub_spec_bounds'
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid) :
    ∃ c, sub self other = ok c ∧
    let X := Field51_as_Nat self.X
    let Y := Field51_as_Nat self.Y
    let Z := Field51_as_Nat self.Z
    let T := Field51_as_Nat self.T
    let YpX := Field51_as_Nat other.Y_plus_X
    let YmX := Field51_as_Nat other.Y_minus_X
    let Z₀ := Field51_as_Nat other.Z
    let T2d := Field51_as_Nat other.T2d
    let X' := Field51_as_Nat c.X
    let Y' := Field51_as_Nat c.Y
    let Z' := Field51_as_Nat c.Z
    let T' := Field51_as_Nat c.T
    (X' + Y * YpX) % p = (((Y + X) * YmX) + X * YpX) % p ∧
    (Y' + X * YpX) % p = (((Y + X) * YmX) + Y * YpX) % p ∧
    (Z' + (T * T2d)) % p = (2 * Z * Z₀) % p ∧
    T' % p = ((2 * Z * Z₀) + (T * T2d)) % p ∧
    -- Output bounds (all < 2^54)
    (∀ i < 5, c.X[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 54) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 54) :=
  spec_imp_exists (sub_spec_aux_54_52_53_52 self other
    hself.X_bounds hself.Y_bounds hself.Z_bounds hself.T_bounds
    hother.Y_plus_X_bounds hother.Y_minus_X_bounds hother.Z_bounds hother.T2d_bounds)


/-! ## Independent sub-lemmas for the main theorem `sub_spec'`

These lemmas factor out the key algebraic and geometric proof steps
used in the main theorem `sub_spec'`:

1. `completed_on_curve_of_affine_div`: General on-curve proof from affine coordinate ratios
2. `niels_T2d_affine_expr`: T2d expression in terms of affine coordinates
3. `edwards_T_affine_expr`: T expression in terms of affine coordinates
4. `sub_lift_to_field_eqs`: Lift modular arithmetic to simplified field equalities
5. `sub_isValid_and_toPoint`: Main geometric validity and point equality proof
-/

/-- General lemma: if a completed point `(cX : cY : cZ : cT)` satisfies
    `cX / cZ = Q.x` and `cY / cT = Q.y` for some point `Q` on Ed25519,
    with `cZ ≠ 0` and `cT ≠ 0`, then the projective curve equation holds:
    `a * cX² * cT² + cY² * cZ² = cZ² * cT² + d * cX² * cY²`.

    This is used to prove the on-curve property for both addition and subtraction
    of completed points. -/
private lemma completed_on_curve_of_affine_div
    (cX cY cZ cT : Edwards.CurveField)
    (hcZ_ne : cZ ≠ 0) (hcT_ne : cT ≠ 0)
    (Q : Point Ed25519)
    (hx_eq : cX / cZ = Q.x) (hy_eq : cY / cT = Q.y) :
    Ed25519.a * cX^2 * cT^2 + cY^2 * cZ^2 =
    cZ^2 * cT^2 + Ed25519.d * cX^2 * cY^2 := by
  have hcZ2 : cZ^2 ≠ 0 := pow_ne_zero 2 hcZ_ne
  have hcT2 : cT^2 ≠ 0 := pow_ne_zero 2 hcT_ne
  have h_on : Ed25519.a * Q.x^2 + Q.y^2 = 1 + Ed25519.d * Q.x^2 * Q.y^2 := Q.on_curve
  calc Ed25519.a * cX^2 * cT^2 + cY^2 * cZ^2
      = (Ed25519.a * (cX / cZ)^2 + (cY / cT)^2) *
          cZ^2 * cT^2 := by field_simp [hcZ2, hcT2]
    _ = (Ed25519.a * Q.x^2 + Q.y^2) * cZ^2 * cT^2 := by rw [hx_eq, hy_eq]
    _ = (1 + Ed25519.d * Q.x^2 * Q.y^2) * cZ^2 * cT^2 := by rw [h_on]
    _ = cZ^2 * cT^2 + Ed25519.d * cX^2 * cY^2 := by
          rw [← hx_eq, ← hy_eq]; simp only [div_pow]; field_simp [hcZ2, hcT2]

/-- From a projective niels point's T2d relation `2 * Z * T2d = d * (YpX² - YmX²)`,
    derive the affine expression `T2d = 2 * d * Z * x * y`
    where `x = (YpX - YmX) / (2 * Z)` and `y = (YpX + YmX) / (2 * Z)`. -/
private lemma niels_T2d_affine_expr
    (YpX YmX Z T2d x y : Edwards.CurveField)
    (hZ_ne : Z ≠ 0)
    (h_T2d_rel : 2 * Z * T2d = Ed25519.d * (YpX ^ 2 - YmX ^ 2))
    (hx : x = (YpX - YmX) / (2 * Z))
    (hy : y = (YpX + YmX) / (2 * Z)) :
    T2d = 2 * Ed25519.d * Z * x * y := by
  have h2 : (2 : Edwards.CurveField) ≠ 0 := by decide
  have h2Z_ne : 2 * Z ≠ 0 := mul_ne_zero h2 hZ_ne
  have h_sq_diff : YpX^2 - YmX^2 = (YpX - YmX) * (YpX + YmX) := by ring
  have h_factor : (YpX - YmX) * (YpX + YmX) = 4 * Z^2 * x * y := by
    simp only [hx, hy]; field_simp [h2Z_ne]; ring
  rw [h_sq_diff, h_factor] at h_T2d_rel
  have h_simpl : T2d * (2 * Z) = 2 * Ed25519.d * Z * x * y * (2 * Z) := by
    linear_combination h_T2d_rel
  field_simp [hZ_ne, h2] at h_simpl
  calc T2d = 2 * Z * Ed25519.d * x * y := h_simpl
    _ = 2 * Ed25519.d * Z * x * y := by ring

/-- From an Edwards point's T relation `X * Y = T * Z` with `Z ≠ 0`,
    derive the affine expression `T = x * y * Z`
    where `x = X / Z` and `y = Y / Z`. -/
private lemma edwards_T_affine_expr
    (X Y Z T x y : Edwards.CurveField)
    (hZ_ne : Z ≠ 0)
    (h_T_rel : X * Y = T * Z)
    (hx : x = X / Z) (hy : y = Y / Z) :
    T = x * y * Z := by
  simp only [hx, hy]
  field_simp [hZ_ne]
  linear_combination -h_T_rel

/-- Lift the four modular arithmetic results from `sub_spec_bounds'` to simplified
    field equalities in `CurveField`. Each modular relation `(a + b) % p = c % p`
    is lifted via `lift_mod_eq` and then simplified via `linear_combination`. -/
private lemma sub_lift_to_field_eqs
    (c : CompletedPoint)
    (self : curve25519_dalek.edwards.EdwardsPoint)
    (other : ProjectiveNielsPoint)
    (hX_arith : (Field51_as_Nat c.X + Field51_as_Nat self.Y * Field51_as_Nat other.Y_plus_X) % p =
        ((Field51_as_Nat self.Y + Field51_as_Nat self.X) * Field51_as_Nat other.Y_minus_X +
         Field51_as_Nat self.X * Field51_as_Nat other.Y_plus_X) % p)
    (hY_arith : (Field51_as_Nat c.Y + Field51_as_Nat self.X * Field51_as_Nat other.Y_plus_X) % p =
        ((Field51_as_Nat self.Y + Field51_as_Nat self.X) * Field51_as_Nat other.Y_minus_X +
         Field51_as_Nat self.Y * Field51_as_Nat other.Y_plus_X) % p)
    (hZ_arith : (Field51_as_Nat c.Z + Field51_as_Nat self.T * Field51_as_Nat other.T2d) % p =
        (2 * Field51_as_Nat self.Z * Field51_as_Nat other.Z) % p)
    (hT_arith : Field51_as_Nat c.T % p =
        (2 * Field51_as_Nat self.Z * Field51_as_Nat other.Z +
         Field51_as_Nat self.T * Field51_as_Nat other.T2d) % p) :
    c.X.toField = (self.Y.toField + self.X.toField) * other.Y_minus_X.toField -
        (self.Y.toField - self.X.toField) * other.Y_plus_X.toField ∧
    c.Y.toField = (self.Y.toField + self.X.toField) * other.Y_minus_X.toField +
        (self.Y.toField - self.X.toField) * other.Y_plus_X.toField ∧
    c.Z.toField = 2 * self.Z.toField * other.Z.toField -
        self.T.toField * other.T2d.toField ∧
    c.T.toField = 2 * self.Z.toField * other.Z.toField +
        self.T.toField * other.T2d.toField := by
  -- Lift each modular equality to a field equality
  have lift_X : c.X.toField + self.Y.toField * other.Y_plus_X.toField =
      (self.Y.toField + self.X.toField) * other.Y_minus_X.toField +
      self.X.toField * other.Y_plus_X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hX_arith
    push_cast at h
    exact h
  have lift_Y : c.Y.toField + self.X.toField * other.Y_plus_X.toField =
      (self.Y.toField + self.X.toField) * other.Y_minus_X.toField +
      self.Y.toField * other.Y_plus_X.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hY_arith
    push_cast at h
    exact h
  have lift_Z : c.Z.toField + self.T.toField * other.T2d.toField =
      2 * self.Z.toField * other.Z.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hZ_arith
    push_cast at h
    exact h
  have lift_T : c.T.toField = 2 * self.Z.toField * other.Z.toField +
      self.T.toField * other.T2d.toField := by
    unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hT_arith
    push_cast at h
    exact h
  exact ⟨by linear_combination lift_X,
         by linear_combination lift_Y,
         by linear_combination lift_Z,
         lift_T⟩

/-! ## Further sub-lemmas for `sub_isValid_and_toPoint`

These lemmas decompose the main geometric validity and point equality proof
into independent, reusable pieces:

1. `sub_diff_coords`: Computes the affine coordinates of P1 + (-P2) on Ed25519
2. `sub_factored_coords`: Derives factored forms for all four completed point
   coordinates plus Z ≠ 0 and T ≠ 0
3. `sub_completed_on_curve_proof`: Proves the on-curve equation from factored forms
4. `sub_toPoint_eq_proof`: Proves point equality from factored forms
-/

/-- For subtraction, the affine coordinates of `P1 + (-P2)` on Ed25519 are:
    `x = (P1.x * P2.y - P1.y * P2.x) / (1 - d * P1.x * P2.x * P1.y * P2.y)`
    `y = (P1.y * P2.y - P1.x * P2.x) / (1 + d * P1.x * P2.x * P1.y * P2.y)` -/
private lemma sub_diff_coords (P1 P2 : Point Ed25519) :
    (P1 + (-P2)).x = (P1.x * P2.y - P1.y * P2.x) /
        (1 - Ed25519.d * P1.x * P2.x * P1.y * P2.y) ∧
    (P1 + (-P2)).y = (P1.y * P2.y - P1.x * P2.x) /
        (1 + Ed25519.d * P1.x * P2.x * P1.y * P2.y) := by
  constructor
  · rw [add_x]; simp only [neg_x, neg_y]; congr 1 <;> ring
  · rw [add_y]
    have := Edwards.neg_x P2; rw [this]
    have := Edwards.neg_y P2; rw [this]
    simp only [Ed25519]
    ring_nf

/-- Derive factored forms for all four completed point coordinates in subtraction,
    plus Z ≠ 0 and T ≠ 0, from the field equalities and validity conditions.

    Given the simplified field equalities for c.X, c.Y, c.Z, c.T and the
    Edwards/Niels coordinate relations, this lemma produces:
    - `cX = 2 * Z1 * Z2 * (x1 * y2 - y1 * x2)`
    - `cY = 2 * Z1 * Z2 * (y1 * y2 - x1 * x2)`
    - `cZ = 2 * Z1 * Z2 * (1 - d * x1 * x2 * y1 * y2)`
    - `cT = 2 * Z1 * Z2 * (1 + d * x1 * x2 * y1 * y2)`
    - `cZ ≠ 0` and `cT ≠ 0` -/
private lemma sub_factored_coords
    (cX cY cZ cT X1 Y1 Z1 T1 YpX YmX Z2 T2d x1 y1 x2 y2 : Edwards.CurveField)
    (hZ1_ne : Z1 ≠ 0) (hZ2_ne : Z2 ≠ 0)
    (h_self_T : X1 * Y1 = T1 * Z1)
    (h_T2d_rel : 2 * Z2 * T2d = Ed25519.d * (YpX ^ 2 - YmX ^ 2))
    (hx1 : x1 = X1 / Z1) (hy1 : y1 = Y1 / Z1)
    (hx2 : x2 = (YpX - YmX) / (2 * Z2)) (hy2 : y2 = (YpX + YmX) / (2 * Z2))
    (hcX : cX = (Y1 + X1) * YmX - (Y1 - X1) * YpX)
    (hcY : cY = (Y1 + X1) * YmX + (Y1 - X1) * YpX)
    (hcZ : cZ = 2 * Z1 * Z2 - T1 * T2d)
    (hcT : cT = 2 * Z1 * Z2 + T1 * T2d)
    (h_denom_minus : 1 - Ed25519.d * x1 * x2 * y1 * y2 ≠ 0)
    (h_denom_plus : 1 + Ed25519.d * x1 * x2 * y1 * y2 ≠ 0) :
    cX = 2 * Z1 * Z2 * (x1 * y2 - y1 * x2) ∧
    cY = 2 * Z1 * Z2 * (y1 * y2 - x1 * x2) ∧
    cZ = 2 * Z1 * Z2 * (1 - Ed25519.d * x1 * x2 * y1 * y2) ∧
    cT = 2 * Z1 * Z2 * (1 + Ed25519.d * x1 * x2 * y1 * y2) ∧
    cZ ≠ 0 ∧ cT ≠ 0 := by
  have h2 : (2 : Edwards.CurveField) ≠ 0 := by decide
  have h2Z2_ne : 2 * Z2 ≠ 0 := mul_ne_zero h2 hZ2_ne
  -- T2d and T1 affine expressions using extracted lemmas
  have h_T2d_expr : T2d = 2 * Ed25519.d * Z2 * x2 * y2 :=
    niels_T2d_affine_expr YpX YmX Z2 T2d x2 y2 hZ2_ne h_T2d_rel hx2 hy2
  have h_T1_expr : T1 = x1 * y1 * Z1 :=
    edwards_T_affine_expr X1 Y1 Z1 T1 x1 y1 hZ1_ne h_self_T hx1 hy1
  have h_T1_T2d : T1 * T2d = 2 * Ed25519.d * x1 * x2 * y1 * y2 * Z1 * Z2 := by
    rw [h_T1_expr, h_T2d_expr]; ring
  -- Factored forms for Z and T
  have hZ_factored : cZ = 2 * Z1 * Z2 * (1 - Ed25519.d * x1 * x2 * y1 * y2) := by
    rw [hcZ, h_T1_T2d]; ring
  have hT_factored : cT = 2 * Z1 * Z2 * (1 + Ed25519.d * x1 * x2 * y1 * y2) := by
    rw [hcT, h_T1_T2d]; ring
  -- Z ≠ 0 and T ≠ 0 using completeness
  have hcZ_ne : cZ ≠ 0 := by
    rw [hZ_factored]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hZ1_ne) hZ2_ne) h_denom_minus
  have hcT_ne : cT ≠ 0 := by
    rw [hT_factored]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hZ1_ne) hZ2_ne) h_denom_plus
  -- Factored forms for X and Y via niels/edwards coordinate expressions
  have hYpX' : YpX = Z2 * (x2 + y2) := by
    simp only [hx2, hy2]; field_simp [h2Z2_ne]; ring
  have hYmX' : YmX = Z2 * (y2 - x2) := by
    simp only [hx2, hy2]; field_simp [h2Z2_ne]; ring
  have hX1' : X1 = Z1 * x1 := by simp only [hx1]; field_simp [hZ1_ne]
  have hY1' : Y1 = Z1 * y1 := by simp only [hy1]; field_simp [hZ1_ne]
  have hX_factored : cX = 2 * Z1 * Z2 * (x1 * y2 - y1 * x2) := by
    rw [hcX, hYpX', hYmX', hX1', hY1']; ring
  have hY_factored : cY = 2 * Z1 * Z2 * (y1 * y2 - x1 * x2) := by
    rw [hcY, hYpX', hYmX', hX1', hY1']; ring
  exact ⟨hX_factored, hY_factored, hZ_factored, hT_factored, hcZ_ne, hcT_ne⟩

/-- Prove the on-curve equation for the completed point from factored forms,
    using `completed_on_curve_of_affine_div` and `sub_diff_coords`.
    Shows: `a * cX² * cT² + cY² * cZ² = cZ² * cT² + d * cX² * cY²` -/
private lemma sub_completed_on_curve_proof
    (cX cY cZ cT Z1 Z2 : Edwards.CurveField)
    (P1 P2 : Point Ed25519)
    (hcZ_ne : cZ ≠ 0) (hcT_ne : cT ≠ 0)
    (hX : cX = 2 * Z1 * Z2 * (P1.x * P2.y - P1.y * P2.x))
    (hY : cY = 2 * Z1 * Z2 * (P1.y * P2.y - P1.x * P2.x))
    (hZ : cZ = 2 * Z1 * Z2 * (1 - Ed25519.d * P1.x * P2.x * P1.y * P2.y))
    (hT : cT = 2 * Z1 * Z2 * (1 + Ed25519.d * P1.x * P2.x * P1.y * P2.y))
    (hZ1_ne : Z1 ≠ 0) (hZ2_ne : Z2 ≠ 0) :
    Ed25519.a * cX ^ 2 * cT ^ 2 + cY ^ 2 * cZ ^ 2 =
    cZ ^ 2 * cT ^ 2 + Ed25519.d * cX ^ 2 * cY ^ 2 := by
  have h2 : (2 : Edwards.CurveField) ≠ 0 := by decide
  have ⟨h_diff_x, h_diff_y⟩ := sub_diff_coords P1 P2
  have h_cx_eq : cX / cZ = (P1 + (-P2)).x := by
    rw [hX, hZ, h_diff_x]
    field_simp [h2, hZ1_ne, hZ2_ne]
  have h_cy_eq : cY / cT = (P1 + (-P2)).y := by
    rw [hY, hT, h_diff_y]
    field_simp [h2, hZ1_ne, hZ2_ne]
  exact completed_on_curve_of_affine_div cX cY cZ cT hcZ_ne hcT_ne (P1 + (-P2)) h_cx_eq h_cy_eq

/-- Prove the point equality `c.toPoint = self.toPoint - other.toPointI`
    from the factored forms and affine coordinate relations. -/
private lemma sub_toPoint_eq_proof
    (c : CompletedPoint)
    (self : curve25519_dalek.edwards.EdwardsPoint)
    (other : ProjectiveNielsPoint)
    (h_c_valid : c.IsValid)
    (Z1 Z2 x1 y1 x2 y2 : Edwards.CurveField)
    (hZ1_ne : Z1 ≠ 0) (hZ2_ne : Z2 ≠ 0)
    (h_self_x : self.toPoint.x = x1) (h_self_y : self.toPoint.y = y1)
    (h_other_x : other.toPoint.x = x2) (h_other_y : other.toPoint.y = y2)
    (hX_factored : c.X.toField = 2 * Z1 * Z2 * (x1 * y2 - y1 * x2))
    (hY_factored : c.Y.toField = 2 * Z1 * Z2 * (y1 * y2 - x1 * x2))
    (hZ_factored : c.Z.toField = 2 * Z1 * Z2 * (1 - Ed25519.d * x1 * x2 * y1 * y2))
    (hT_factored : c.T.toField = 2 * Z1 * Z2 * (1 + Ed25519.d * x1 * x2 * y1 * y2)) :
    c.toPoint = self.toPoint - other.toPoint := by
  have h2 : (2 : Edwards.CurveField) ≠ 0 := by decide
  have ⟨h_cx, h_cy⟩ := CompletedPoint.toPoint_of_isValid h_c_valid
  ext
  · -- x coordinate: X'/Z' = (P1 - P2).x = (P1 + (-P2)).x
    rw [h_cx, hX_factored, hZ_factored]
    simp only [sub_eq_add_neg]
    rw [add_x]
    simp only [neg_x, neg_y, h_self_x, h_self_y, h_other_x, h_other_y]
    field_simp [h2, hZ1_ne, hZ2_ne]
  · -- y coordinate: Y'/T' = (P1 - P2).y = (P1 + (-P2)).y
    rw [h_cy, hY_factored, hT_factored]
    simp only [sub_eq_add_neg]
    rw [add_y]
    have := Edwards.neg_x other.toPoint
    rw [this]
    have := Edwards.neg_y other.toPoint
    rw [this]
    simp only [h_self_x, h_self_y, h_other_x, h_other_y, Ed25519]
    field_simp [h2, hZ1_ne, hZ2_ne]
    ring_nf

/- Main geometric and algebraic proof for subtraction:
    given the simplified field equalities and output bounds,
    prove that the completed point is valid and represents `self - other`.
    Delegates to `sub_factored_coords`, `sub_completed_on_curve_proof`,
    and `sub_toPoint_eq_proof`. -/

private lemma sub_isValid_and_toPoint
    (c : CompletedPoint)
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid)
    (hX_F' : c.X.toField = (self.Y.toField + self.X.toField) * other.Y_minus_X.toField -
        (self.Y.toField - self.X.toField) * other.Y_plus_X.toField)
    (hY_F' : c.Y.toField = (self.Y.toField + self.X.toField) * other.Y_minus_X.toField +
        (self.Y.toField - self.X.toField) * other.Y_plus_X.toField)
    (hZ_F' : c.Z.toField = 2 * self.Z.toField * other.Z.toField -
        self.T.toField * other.T2d.toField)
    (hT_F : c.T.toField = 2 * self.Z.toField * other.Z.toField +
        self.T.toField * other.T2d.toField)
    (hcX_bounds : ∀ i < 5, c.X[i]!.val < 2 ^ 54)
    (hcY_bounds : ∀ i < 5, c.Y[i]!.val < 2 ^ 54)
    (hcZ_bounds : ∀ i < 5, c.Z[i]!.val < 2 ^ 54)
    (hcT_bounds : ∀ i < 5, c.T[i]!.val < 2 ^ 54) :
    c.IsValid ∧ c.toPoint = self.toPoint - other.toPoint := by
  -- Setup self's affine coordinates
  set X1 := self.X.toField with hX1_def
  set Y1 := self.Y.toField with hY1_def
  set Z1 := self.Z.toField with hZ1_def
  set T1 := self.T.toField with hT1_def
  have hZ1_ne : Z1 ≠ 0 := hself.Z_ne_zero
  set x1 := X1 / Z1 with hx1_def
  set y1 := Y1 / Z1 with hy1_def
  have h_P1_on_curve : Ed25519.a * x1 ^ 2 + y1 ^ 2 = 1 + Ed25519.d * x1 ^ 2 * y1 ^ 2 := by
    have hZ1_2 : Z1 ^ 2 ≠ 0 := pow_ne_zero 2 hZ1_ne
    have hZ1_4 : Z1 ^ 4 ≠ 0 := pow_ne_zero 4 hZ1_ne
    have h_self_curve := hself.on_curve
    simp only [Ed25519] at h_self_curve ⊢
    simp only [hx1_def, hy1_def, div_pow]
    field_simp [hZ1_2, hZ1_4]
    linear_combination h_self_curve
  let P1 : Point Ed25519 := ⟨x1, y1, h_P1_on_curve⟩
  -- Setup other's affine coordinates from ProjectiveNielsPoint
  set YpX := other.Y_plus_X.toField with hYpX_def
  set YmX := other.Y_minus_X.toField with hYmX_def
  set Z2 := other.Z.toField with hZ2_def
  set T2d := other.T2d.toField with hT2d_def
  have hZ2_ne : Z2 ≠ 0 := hother.Z_ne_zero
  have h2Z2_ne : 2 * Z2 ≠ 0 := mul_ne_zero (by decide : (2 : Edwards.CurveField) ≠ 0) hZ2_ne
  set x2 := (YpX - YmX) / (2 * Z2) with hx2_def
  set y2 := (YpX + YmX) / (2 * Z2) with hy2_def
  have h_P2_on_curve : Ed25519.a * x2 ^ 2 + y2 ^ 2 = 1 + Ed25519.d * x2 ^ 2 * y2 ^ 2 := by
    have h2Z2_2 : (2 * Z2) ^ 2 ≠ 0 := pow_ne_zero 2 h2Z2_ne
    have h2Z2_4 : (2 * Z2) ^ 4 ≠ 0 := pow_ne_zero 4 h2Z2_ne
    have h_other_curve := hother.on_curve
    simp only [Ed25519] at h_other_curve ⊢
    simp only [hx2_def, hy2_def, div_pow]
    field_simp [h2Z2_2, h2Z2_4]
    ring_nf; ring_nf at h_other_curve
    linear_combination h_other_curve
  let P2 : Point Ed25519 := ⟨x2, y2, h_P2_on_curve⟩
  -- Completeness theorem for denominators
  have h_denoms := Ed25519.denomsNeZero P1 P2
  have h_denom_plus : 1 + Ed25519.d * x1 * x2 * y1 * y2 ≠ 0 := by
    have h := h_denoms.1; simp only [P1, P2] at h; convert h using 1
  have h_denom_minus : 1 - Ed25519.d * x1 * x2 * y1 * y2 ≠ 0 := by
    have h := h_denoms.2; simp only [P1, P2] at h; convert h using 1
  -- Bounds → validity
  have hcX_valid : c.X.IsValid := hcX_bounds
  have hcY_valid : c.Y.IsValid := hcY_bounds
  have hcZ_valid : c.Z.IsValid := hcZ_bounds
  have hcT_valid : c.T.IsValid := hcT_bounds
  -- Derive all factored forms + Z ≠ 0 + T ≠ 0
  have ⟨hX_factored, hY_factored, hZ_factored, hT_factored, hcZ_ne, hcT_ne⟩ :=
    sub_factored_coords c.X.toField c.Y.toField c.Z.toField c.T.toField
      X1 Y1 Z1 T1 YpX YmX Z2 T2d x1 y1 x2 y2
      hZ1_ne hZ2_ne hself.T_relation hother.T2d_relation
      hx1_def hy1_def hx2_def hy2_def
      hX_F' hY_F' hZ_F' hT_F h_denom_minus h_denom_plus
  -- On-curve proof using sub_completed_on_curve_proof
  have h_c_on_curve := sub_completed_on_curve_proof
    c.X.toField c.Y.toField c.Z.toField c.T.toField Z1 Z2 P1 P2
    hcZ_ne hcT_ne hX_factored hY_factored hZ_factored hT_factored
    hZ1_ne hZ2_ne
  constructor
  · exact {
      X_valid := hcX_valid
      Y_valid := hcY_valid
      Z_valid := hcZ_valid
      T_valid := hcT_valid
      Z_ne_zero := hcZ_ne
      T_ne_zero := hcT_ne
      on_curve := h_c_on_curve
    }
  · -- Relate toPoints to affine coordinates and delegate to sub_toPoint_eq_proof
    have h_c_valid : c.IsValid := {
      X_valid := hcX_valid
      Y_valid := hcY_valid
      Z_valid := hcZ_valid
      T_valid := hcT_valid
      Z_ne_zero := hcZ_ne
      T_ne_zero := hcT_ne
      on_curve := h_c_on_curve
    }
    have ⟨h_selfx, h_selfy⟩ := EdwardsPoint.toPoint_of_isValid hself
    have ⟨h_otherx, h_othery⟩ := ProjectiveNielsPoint.toPoint_of_isValid hother
    have h_self_x : self.toPoint.x = x1 := by simp only [h_selfx, hx1_def, hX1_def, hZ1_def]
    have h_self_y : self.toPoint.y = y1 := by simp only [h_selfy, hy1_def, hY1_def, hZ1_def]
    have h_other_x : other.toPoint.x = x2 := by
      simp only [h_otherx, hx2_def, hYpX_def, hYmX_def, hZ2_def]
    have h_other_y : other.toPoint.y = y2 := by
      simp only [h_othery, hy2_def, hYpX_def, hYmX_def, hZ2_def]
    exact sub_toPoint_eq_proof c self other h_c_valid Z1 Z2 x1 y1 x2 y2
      hZ1_ne hZ2_ne h_self_x h_self_y h_other_x h_other_y
      hX_factored hY_factored hZ_factored hT_factored

/-- **Spec theorem for
`curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint.sub`**

Computes `self - other` as a CompletedPoint: the result is valid and represents
the difference of the two input points. -/
@[step]
theorem sub_spec
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid) :
    sub self other ⦃ (c : CompletedPoint) =>
      c.IsValid ∧
      c.toPoint = self.toPoint - other.toPoint ⦄ := by
  obtain ⟨c, hc_run, hX_arith, hY_arith, hZ_arith, hT_arith, hcX_bounds, hcY_bounds, hcZ_bounds, hcT_bounds⟩ :=
    sub_spec_bounds' self hself other hother
  simp only [spec]
  apply exists_imp_spec
  use c, hc_run
  have ⟨hX_F', hY_F', hZ_F', hT_F⟩ :=
    sub_lift_to_field_eqs c self other hX_arith hY_arith hZ_arith hT_arith
  exact sub_isValid_and_toPoint c self hself other hother
    hX_F' hY_F' hZ_F' hT_F hcX_bounds hcY_bounds hcZ_bounds hcT_bounds

end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint
