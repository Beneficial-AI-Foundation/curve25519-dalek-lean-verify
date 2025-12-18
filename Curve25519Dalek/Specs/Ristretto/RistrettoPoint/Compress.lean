/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `RistrettoPoint::compress`

Specification and proof for `RistrettoPoint::compress`.

This function implements the Ristretto compression (ENCODE) function, which maps a
RistrettoPoint to its canonical 32-byte representation. The function is defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.2).

It takes a RistrettoPoint (which represents an equivalence class of 8 Edwards points)
and produces a unique, canonical byte representation.

**Source**: curve25519-dalek/src/ristretto.rs

## TODO
- Write specification
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a RistrettoPoint (represented internally as an EdwardsPoint in extended coordinates
  (X, Y, Z, T)) and compresses it to a canonical 32-byte representation according to the
  Ristretto ENCODE function specified in:
  https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.2

  Arithmetics are performed in the field 𝔽ₚ where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic) for all valid RistrettoPoint inputs
• Different Edwards point representations of the same Ristretto point
  (which constitutes an equivalence class of 8 Edwards points)
  result in the same output byte representation

Note: To check whether two Edwards points e and e' mathematically represent the same Ristretto point, one can for example
check whether
mul_by_cofactor e = mul_by_cofactor e', since
8e = 8e' is equivalent to
8 (e - e') = 0, which is equivalent to
e - e' being in the torsion subgroup E[8], which is equivalent to
e and e' representing the same Ristretto point.
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.compress`**:

1. The function always succeeds (no panic) for all valid RistrettoPoint inputs
2. Canonicalization: If two RistrettoPoint representations are equivalent
  (i.e., their cofactor multiples are equal as Edwards points), then they compress to
  the same byte representation.
-/
theorem compress_spec
  (rist1 rist2 : RistrettoPoint)
  (h1_X_bounds : ∀ i, i < 5 → (rist1.X[i]!).val < 2 ^ 54)
  (h1_Y_bounds : ∀ i, i < 5 → (rist1.Y[i]!).val < 2 ^ 53)
  (h1_Z_bounds : ∀ i, i < 5 → (rist1.Z[i]!).val < 2 ^ 53)
  (h1_T_bounds : ∀ i, i < 5 → (rist1.T[i]!).val < 2 ^ 54)
  (h2_X_bounds : ∀ i, i < 5 → (rist2.X[i]!).val < 2 ^ 54)
  (h2_Y_bounds : ∀ i, i < 5 → (rist2.Y[i]!).val < 2 ^ 53)
  (h2_Z_bounds : ∀ i, i < 5 → (rist2.Z[i]!).val < 2 ^ 53)
  (h2_T_bounds : ∀ i, i < 5 → (rist2.T[i]!).val < 2 ^ 54) :

  ∃ c1,
  ∃ c2,
    compress rist1 = ok c1 ∧
    compress rist2 = ok c2 ∧
    ((∃ p1_times_8,
      ∃ p2_times_8,
      ∃ eq_choice,
        edwards.EdwardsPoint.mul_by_cofactor rist1 = ok p1_times_8 ∧
        edwards.EdwardsPoint.mul_by_cofactor rist2 = ok p2_times_8 ∧
        edwards.ConstantTimeEqcurve25519_dalekedwardsEdwardsPoint.ct_eq p1_times_8 p2_times_8 = ok eq_choice ∧
        eq_choice = Choice.one) →
      c1 = c2) := by
  sorry

end curve25519_dalek.ristretto.RistrettoPoint
