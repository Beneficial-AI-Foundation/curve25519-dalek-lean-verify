/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # as_bytes

Specification and proof for `Scalar::as_bytes`.

This function converts the structure to its byte representation.

**Source**: curve25519-dalek/src/scalar.rs:L705-L708

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Extract the little-endian byte representation of type [u8;32] from a Scalar s. "Little-endian"
      means that the left-most byte is the least significant.

natural language specs:

    • Scalar{ bytes : s.as_bytes() } = s, whereby Scalar{} denotes the constructor
      for the Scalar type, i.e., if I convert to bytes and then back to Scalar type I get the identity
    • s.as_bytes() is an array of length 32
    • Each entry of s_as_bytes() is a u8
-/
