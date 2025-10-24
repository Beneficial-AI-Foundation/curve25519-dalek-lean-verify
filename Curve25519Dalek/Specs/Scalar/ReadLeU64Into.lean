/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # read_le_u64_into

Specification and proof for `read_le_u64_into`.

This function reads little-endian u64 values into an array.

**Source**: curve25519-dalek/src/scalar.rs:L1349-L1364

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes an array a of type [u8] (note the arbitrary length) and
      another array b of type [u64]. Then updates the entries of b by
      subsequently converting chunks of consecutive u8s in a into
      one u64 and then filling the u64 into b. For this to make sense,
      it has to hold that len(a) = 8*len(b). Note that no value is
      returned here, rather the array b is modified in place.

natural language specs:

    • After the function has been run, it should hold that
      \forall i \in \{0,…, len(b)-1}:
      b[i] = (256)^7 a[8i + 7] + … + (256)^0  a[8i])
-/
