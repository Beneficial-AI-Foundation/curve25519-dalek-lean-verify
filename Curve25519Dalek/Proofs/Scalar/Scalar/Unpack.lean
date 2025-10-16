/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # unpack

Specification and proof for `Scalar::unpack`.

This function unpacks the element from a compact representation.

**Source**: curve25519-dalek/src/scalar.rs:L1118-L1121

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes an input Scalar s and returns the corresponding
      UnpackedScalar u.

natural language specs:

    • scalar_to_nat(s) = unpacked_scalar_to_nat(u)
    • pack(u) = s
-/
