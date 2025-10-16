/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # reduce

Specification and proof for `Scalar::reduce`.

This function performs modular reduction.

**Source**: curve25519-dalek/src/scalar.rs:L1124-L1130

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes an input Scalar s and outputs a Scalar s’ that represents
      the canonical reduced version, i.e.,  s’ \in \{0, …, \ell – 1}
      and s is congruent to s’ modulo \ell.

natural language specs:

    • scalar_to_nat(s) is congruent to scalar_to_nat(s’) modulo \ell
    • scalar_to_nat(s’) \in \{0,…, \ell – 1}
-/
