/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # Spec Theorem for `Scalar::is_canonical`

Specification and proof for `Scalar::is_canonical`.

This function checks if the representation is canonical.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Returns True if the input Scalar s is the canonical
      representative modulo \ell within the scalar field, i.e.,
      if s \in \{0,…, \ell – 1\}, else returns False.

natural language specs:

    • scalar_to_nat(s) \in \{0,…, \ell - 1 \} \iff Return value = True
-/

/-- **Spec and proof concerning `scalar.Scalar.is_canonical`**:
- No panic (always returns successfully)
- Returns Choice.one if and only if the scalar's bytes represent a value less than L (the group order)
-/
theorem is_canonical_spec (s : Scalar):
    ∃ c,
    is_canonical s = ok c ∧
    (c = Choice.one ↔ U8x32_as_Nat s.bytes < L)
    := by
  sorry

end curve25519_dalek.scalar.Scalar
