/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # is_canonical

Specification and proof for `Scalar::is_canonical`.

This function checks if the representation is canonical.

**Source**: curve25519-dalek/src/scalar.rs:L1133-L1136

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Returns True if the input Scalar s is the canonical
      representative modulo \ell within the scalar field, i.e.,
      if s \in \{0,…, \ell – 1\}, else returns False.

natural language specs:

    • scalar_to_nat(s) \in \{0,…, \ell - 1 \} \iff Return value = True
-/
