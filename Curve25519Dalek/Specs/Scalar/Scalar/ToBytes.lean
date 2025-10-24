/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `Scalar::to_bytes`

Specification and proof for `Scalar::to_bytes`.

This function converts the structure to a byte array.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Takes an input Scalar s and returns its constituting
      array a of type [u8;32].

natural language specs:

    • s.bytes = a
    • Scalar{a} = s
-/

/-- **Spec and proof concerning `scalar.Scalar.to_bytes`**:
- No panic (always returns successfully)
- The result array a is the byte array representation of the scalar (s.bytes)
- Converting the result a back to a Scalar via the constructor yields the original scalar s
-/
theorem to_bytes_spec (s : Scalar) :
    ∃ a,
    to_bytes s = ok a ∧
    a = s.bytes ∧
    mk a = s
    := by
  unfold to_bytes
  simp

end curve25519_dalek.scalar.Scalar
