/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # from_canonical_bytes

Specification and proof for `Scalar::from_canonical_bytes`.

This function constructs a scalar from canonical bytes.

**Source**: curve25519-dalek/src/scalar.rs:L260-L265

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes an input array a of type [u8;32].

      Two conditions are checked:
      (1) whether the most significant bit in the most significant byte of a is 0, and
      (2) whether the Scalar s = Scalar{a} corresponding to the input array fulfils s.is_canonical(),
          which means that it lies between 0 and \ell.

      If both conditions are true, then the Scalar s is returned,
      otherwise None is returned.

natural language specs:

    • The Return value is not None \iff a[31][0] = 0 and u8x32_to_nat(a) < \ell
    • The Return value is not None \implies scalar_to_nat(s) = u8x32_to_nat(a)
-/
