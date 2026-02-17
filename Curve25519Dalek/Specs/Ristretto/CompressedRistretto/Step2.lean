/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation

/-! # Spec Theorem for `ristretto.decompress.step_2`

Specification and proof for `ristretto.decompress.step_2`.

This function performs the second step of Ristretto decompression, computing
the affine coordinates (x, y) of a point on the Edwards curve from the field element s, then
outputs extended Edwards coordinates (x, y, 1, xy)

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result Edwards Aeneas.Std.WP
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
    The three Choice values (ok1, c, c1) are used in the full decompress function to validate
    that the decompression is valid.

natural language specs:

    • The function always succeeds (no panic) for any valid field element s
    • ok1 is true if and only if the inverse square root of v · u2² exists,
      where v = (-EDWARDS_D) · u1² - u2², u1 = 1 - s², u2 = 1 + s²
    • c is true if and only if t is negative, where t = x1 · y is the T coordinate of the output point
    • c1 is true if and only if y = 0
    • The output point pt is a valid RistrettoPoint when ok1 = 1, c = 0, and c1 = 0 (all checks pass)
-/

/-- **Spec and proof concerning `ristretto.decompress.step_2`**:
    • The function always succeeds (no panic) for any valid field element `s`
    • ok1 is true if and only if the inverse square root of v · u2² exists
    • c is true if and only if t is negative
    • c1 is true if and only if y is zero
    • pt is a valid RistrettoPoint when ok1 = 1, c = 0, and c1 = 0
-/
@[progress]
theorem step_2_spec (s : backend.serial.u64.field.FieldElement51) (h_s : s.IsValid) :
    spec (step_2 s) (fun (ok1, c, c1, pt) =>
    (let u1 := 1 - s.toField ^ 2
     let u2 := 1 + s.toField ^ 2
     let v := (-Ed25519.d) * u1 ^ 2 - u2 ^ 2
     ok1.val = 1#u8 ↔ (v * u2 ^ 2 ≠ 0) ∧ IsSquare (v * u2 ^ 2)) ∧
    (c.val = 1#u8 ↔ math.is_negative pt.T.toField) ∧
    (c1.val = 1#u8 ↔ pt.Y.toField = 0) ∧
    (ok1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 → RistrettoPoint.IsValid pt)) := by
  sorry

end curve25519_dalek.ristretto.decompress
