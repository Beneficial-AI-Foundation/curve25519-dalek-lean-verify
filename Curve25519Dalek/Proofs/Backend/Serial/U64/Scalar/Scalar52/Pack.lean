/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # pack

Specification and proof for `Scalar52::pack`.

This function packs the element into a compact representation.

**Source**: curve25519-dalek/src/scalar.rs:L1140-L1145

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek

/-
natural language description:

    • Takes an input UnpackedScalar r and returns
      the corresponding Scalar s.

natural language specs:

    • scalar_to_nat(s) = unpacked_scalar_to_nat(r)
    • unpack(s) = r
-/
