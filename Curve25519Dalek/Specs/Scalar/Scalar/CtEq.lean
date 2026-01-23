/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `ConstantTimeEqScalar.ct_eq`

Specification and proof for `ConstantTimeEqScalar.ct_eq`.

This function performs constant-time equality comparison.

Source: curve25519-dalek/src/scalar.rs
-/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
namespace curve25519_dalek.scalar.ConstantTimeEqScalar

/-
natural language description:

    • Compares two scalar types s and s' to determine whether they are equal or not.

    • Crucially does so in constant time irrespective of the inputs as to avoid security liabilities.

natural language specs:

    • s.bytes = s'.bytes \iff Choice = True
-/

/-- **Spec and proof concerning `scalar.ConstantTimeEqScalar.ct_eq`**:
- No panic (always returns successfully)
- Returns `Choice` representing equality in constant time
- The result is Choice.one (true) if and only if the two scalars are equal (same byte representation)
-/
@[progress]
theorem ct_eq_spec (s s' : Scalar) :
    ct_eq s s' ⦃ c => c = Choice.one ↔ s.bytes = s'.bytes ⦄ := by
  sorry

end curve25519_dalek.scalar.ConstantTimeEqScalar
