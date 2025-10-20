/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs

/-! # Spec Theorem for `Scalar::as_bytes`

Specification and proof for `Scalar::as_bytes`.

This function converts the structure to its byte representation.

**Source**: curve25519-dalek/src/scalar.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-
natural language description:

    • Extract the little-endian byte representation of type [u8;32] from a Scalar s. "Little-endian"
      means that the left-most byte is the least significant.

natural language specs:

    • Scalar{ bytes : s.as_bytes() } = s, whereby Scalar{} denotes the constructor
      for the Scalar type, i.e., if I convert to bytes and then back to Scalar type I get the identity
-/

/-- **Spec and proof concerning `scalar.Scalar.as_bytes`**:
- No panic (always returns successfully)
- The result is the byte representation of the scalar (s.bytes)
- Converting the result back to a Scalar via the constructor yields the original scalar
-/
theorem as_bytes_spec (s : Scalar):
    ∃ result,
    as_bytes s = ok result ∧
    result = s.bytes ∧
    mk result = s
    := by
  unfold as_bytes
  simp

end curve25519_dalek.scalar.Scalar
