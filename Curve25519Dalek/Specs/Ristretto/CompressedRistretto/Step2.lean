/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `ristretto.decompress.step_2`

Specification and proof for `ristretto.decompress.step_2`.

This function performs the second step of Ristretto decompression, computing
the affine coordinates (x, y) of a point on the Edwards curve from the field element s, then
outputs extended Edwards coordinates (x, y, 1, xy)

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.decompress

/-
natural language description:

    • Takes a field element s as input (from step_1)
    • Computes ss = s²
    • Computes u1 = 1 - ss
    • Computes u2 = 1 + ss
    • Computes u2_sqr = u2²
    • Computes v = (-EDWARDS_D) · u1² - u2²
    • Computes I = invsqrt(v · u2²), obtaining (ok1, I) where ok1 indicates if the inverse square root exists
    • Computes Dx = I · u2
    • Computes Dy = I · Dx · v
    • Computes x = 2s · Dx
    • Conditionally negates x if x is negative, producing x1
    • Computes y = u1 · Dy
    • Computes t = x1 · y (the extended coordinate)
    • Checks if t is negative (stored in c)
    • Checks if y is zero (stored in c1)
    • Returns a tuple containing:
        - ok1: Choice indicating whether the inverse square root computation succeeded
        - c: Choice indicating whether t is negative
        - c1: Choice indicating whether y is zero
        - A RistrettoPoint with coordinates (X=x1, Y=y, Z=1, T=t) in extended twisted Edwards form

    This is the second step in Ristretto decompression. It computes the point coordinates
    from the field element s, performing the inverse of the Ristretto encoding map.
    The three Choice values (ok1, c, c1) are used in subsequent steps to validate
    that the decompression is valid.

natural language specs:

    • The function always succeeds (no panic) for any field element s
    • The computed point (x1, y, 1, t) is a valid Ristretto point
-/

/-- **Spec and proof concerning `ristretto.decompress.step_2`**:
  - The function always succeeds (no panic) for any field element s
  - The computed point (x1, y, 1, t) is a valid Ristretto point
-/
@[progress]
theorem step_2_spec (s : backend.serial.u64.field.FieldElement51) :
    ∃ (ok1 c c1 : subtle.Choice) (pt : ristretto.RistrettoPoint),
    step_2 s = ok (ok1, c, c1, pt) ∧

    -- Intermediate computations exist
    (∃ (ss u1 u2 u2_sqr v : backend.serial.u64.field.FieldElement51),
     backend.serial.u64.field.FieldElement51.square s = ok ss ∧
     backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub
       backend.serial.u64.field.FieldElement51.ONE ss = ok u1 ∧
     backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add
       backend.serial.u64.field.FieldElement51.ONE ss = ok u2 ∧
     backend.serial.u64.field.FieldElement51.square u2 = ok u2_sqr ∧
     (∃ (neg_d u1_sqr d_u1_sqr : backend.serial.u64.field.FieldElement51),
      backend.serial.u64.field.NegShared0FieldElement51FieldElement51.neg
        backend.serial.u64.constants.EDWARDS_D = ok neg_d ∧
      backend.serial.u64.field.FieldElement51.square u1 = ok u1_sqr ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
        neg_d u1_sqr = ok d_u1_sqr ∧
      backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub
        d_u1_sqr u2_sqr = ok v)) ∧

    -- Inverse square root computation
    (∃ (v_u2_sqr : backend.serial.u64.field.FieldElement51) (I : backend.serial.u64.field.FieldElement51),
     (∃ v u2_sqr, backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
       v u2_sqr = ok v_u2_sqr) ∧
     field.FieldElement51.invsqrt v_u2_sqr = ok (ok1, I) ∧

     -- Computing Dx and Dy
     ∃ (Dx Dy : backend.serial.u64.field.FieldElement51),
     (∃ u2, backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
       I u2 = ok Dx) ∧
     (∃ v Dx_v, backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
       Dx v = ok Dx_v ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
       I Dx_v = ok Dy) ∧

     -- Computing x and x1 (with conditional negation)
     ∃ (x x1 : backend.serial.u64.field.FieldElement51) (x_neg : subtle.Choice),
     (∃ s_doubled, backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add
       s s = ok s_doubled ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
       s_doubled Dx = ok x) ∧
     field.FieldElement51.is_negative x = ok x_neg ∧
     subtle.ConditionallyNegatable.Blanket.conditional_negate
       subtle.ConditionallySelectableFieldElement51
       core.ops.arith.NegShared0FieldElement51FieldElement51 x x_neg = ok x1 ∧

     -- Computing y and t
     ∃ (y t : backend.serial.u64.field.FieldElement51),
     (∃ u1, backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
       u1 Dy = ok y) ∧
     backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
       x1 y = ok t ∧

     -- Validity checks
     field.FieldElement51.is_negative t = ok c ∧
     field.FieldElement51.is_zero y = ok c1 ∧

     -- The resulting point has the computed coordinates
     pt.X = x1 ∧
     pt.Y = y ∧
     pt.Z = backend.serial.u64.field.FieldElement51.ONE ∧
     pt.T = t) := by

  sorry

end curve25519_dalek.ristretto.decompress
